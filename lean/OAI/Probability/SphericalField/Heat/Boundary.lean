import Mathlib
import OAI.Probability.SphericalField.Heat.MovingParameters

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma heatLog_boundary_hasDerivAt (g : Jet3) (s r : ℝ) (hs : 0 < s) (hr : 0 < r)
    (d e : ℝ≥0) :
    HasDerivAt (fun t => heatLogBCF (s+t).toNNReal d
      (heatLogBCF (r-t).toNNReal e g.f))
      ((((d:ℝ)-(e:ℝ))/2) • heatTiltCLM s.toNNReal d (g.heatLog r.toNNReal e).f
        ((g.heatLog r.toNNReal e).d1^2)) 0 := by
  let u := g.heatLog r.toNNReal e
  have hsub : HasDerivAt (fun t : ℝ => r-t) (-1 : ℝ) 0 := by
    convert! (hasDerivAt_const 0 r).sub (hasDerivAt_id 0) using 1; norm_num
  have hadd : HasDerivAt (fun t : ℝ => s+t) (1 : ℝ) 0 := by
    convert! (hasDerivAt_const 0 s).add (hasDerivAt_id 0) using 1; norm_num
  have ht : HasDerivAt (fun t => heatLogBCF t.toNNReal e g.f) (heatGenerator e u) (r-0) := by
    simpa only [sub_zero] using heatLogBCF_time_hasDerivAt g e r hr
  have hG : HasDerivAt (fun t => heatLogBCF (r-t).toNNReal e g.f)
      ((-1 : ℝ) • heatGenerator e u) 0 := ht.scomp 0 hsub
  obtain ⟨h',hh'⟩ := (heatGenerator_boundedC1 u e).smul (-1)
  have he := heatLogBCF_moving_hasDerivAt u d (fun t => s+t)
    (fun t => heatLogBCF (r-t).toNNReal e g.f) 0 1
    ((-1:ℝ) • heatGenerator e u) h'
    hadd
    (by simpa only [add_zero] using hs) hG
    (by simp only [sub_zero,u,Jet3.heatLog_f]) hh'
  apply he.congr_deriv
  simp only [add_zero,one_smul,map_smul]
  rw [← heatTilt_heatGenerator u s.toNNReal d]
  have hg : heatGenerator d u-heatGenerator e u = (((d:ℝ)-(e:ℝ))/2) • (u.d1^2) := by
    ext x
    simp only [heatGenerator,BoundedContinuousFunction.coe_sub,BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_pow,Pi.sub_apply,
      Pi.add_apply,Pi.pow_apply,smul_eq_mul]
    ring
  have hh := congrArg (heatTiltCLM s.toNNReal d u.f) hg
  rw [map_sub,map_smul] at hh
  convert hh using 1; module

lemma weighted_list_tail_nonneg (xs : List (ℝ×ℝ))
    (hc : xs.Pairwise (fun u v => u.2 ≤ v.2))
    (hc0 : ∀ u ∈ xs, 0 ≤ u.2)
    (ht : ∀ ys : List (ℝ×ℝ), ys.IsSuffix xs → 0 ≤ (ys.map Prod.fst).sum) :
    0 ≤ (xs.map (fun u => u.1*u.2)).sum := by
  suffices ∀ (b : ℝ), (∀ u ∈ xs, b ≤ u.2) →
      b*(xs.map Prod.fst).sum ≤ (xs.map (fun u => u.1*u.2)).sum by
    simpa only [zero_mul] using this 0 hc0
  intro b hb
  induction xs generalizing b with
  | nil => simp
  | cons u xs ih =>
    obtain ⟨hum,hrest⟩ := List.pairwise_cons.mp hc
    have htail : ∀ ys : List (ℝ×ℝ), ys.IsSuffix xs → 0 ≤ (ys.map Prod.fst).sum := by
      intro ys hys
      exact ht ys (hys.trans (List.suffix_cons u xs))
    have hi := ih hrest (fun v hv => hc0 v (List.mem_cons_of_mem _ hv)) htail u.2 hum
    have hx := ht (u::xs) (by simp)
    have hu := hb u (List.mem_cons_self ..)
    simp only [List.map_cons,List.sum_cons] at hx ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hx]

def heatBoundaryTerms (g : Jet3) (θ : ℝ) : List HeatIntervalParam → ℝ → List (ℝ×(ℝ→ᵇ ℝ))
  | [], _ => []
  | [_], _ => []
  | p::q::ps, a =>
    let u := parametricHeatJet g (q::ps) θ
    let T := heatTiltCLM (p.duration θ).toNNReal p.coefficient u.f
    (((q.coefficient:ℝ)-(p.coefficient:ℝ))*(a+p.rate),T (u.d1^2)) ::
      (heatBoundaryTerms g θ (q::ps) (a+p.rate)).map (fun z => (z.1,T z.2))

def heatBoundarySum (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ) : ℝ→ᵇ ℝ :=
  ((heatBoundaryTerms g θ ps a).map (fun z => z.1 • z.2)).sum

lemma heatBoundarySum_cons (g : Jet3) (θ : ℝ) (p q : HeatIntervalParam)
    (ps : List HeatIntervalParam) (a : ℝ) :
    heatBoundarySum g θ (p::q::ps) a =
      (((q.coefficient:ℝ)-(p.coefficient:ℝ))*(a+p.rate)) •
        heatTiltCLM (p.duration θ).toNNReal p.coefficient (parametricHeatJet g (q::ps) θ).f
          ((parametricHeatJet g (q::ps) θ).d1^2) +
      heatTiltCLM (p.duration θ).toNNReal p.coefficient (parametricHeatJet g (q::ps) θ).f
        (heatBoundarySum g θ (q::ps) (a+p.rate)) := by
  simp only [heatBoundarySum,heatBoundaryTerms,List.map_cons,List.sum_cons,List.map_map]
  congr 1
  rw [map_list_sum,List.map_map]
  congr 1
  apply List.map_congr_left
  intro z _
  exact (map_smul _ _ _).symm

lemma heatGenerator_sub (g : Jet3) (d e : ℝ≥0) :
    heatGenerator d g-heatGenerator e g = (((d:ℝ)-(e:ℝ))/2) • (g.d1^2) := by
  ext x
  simp only [heatGenerator,BoundedContinuousFunction.coe_sub,BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_pow,Pi.sub_apply,
    Pi.add_apply,Pi.pow_apply,smul_eq_mul]
  ring

def firstHeatGenerator (g : Jet3) (ps : List HeatIntervalParam) (θ : ℝ) : ℝ→ᵇ ℝ :=
  match ps with
  | [] => 0
  | p::_ => heatGenerator p.coefficient (parametricHeatJet g ps θ)

lemma parametricHeatVelocity_boundary (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam)
    (a : ℝ) (hend : a+(ps.map HeatIntervalParam.rate).sum = 0) :
    parametricHeatVelocity g ps θ+a • firstHeatGenerator g ps θ =
      (-1/2 : ℝ) • heatBoundarySum g θ ps a := by
  induction ps generalizing a with
  | nil => simp [parametricHeatVelocity,firstHeatGenerator,heatBoundarySum,heatBoundaryTerms]
  | cons p ps ih =>
    cases ps with
    | nil =>
      simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero] at hend
      simp only [parametricHeatVelocity,firstHeatGenerator,heatBoundarySum,heatBoundaryTerms,
        List.map_nil,List.sum_nil,map_zero,add_zero,smul_zero]
      rw [← add_smul,add_comm p.rate a,hend,zero_smul]
    | cons q ps =>
      have hend' : (a+p.rate)+((q::ps).map HeatIntervalParam.rate).sum = 0 := by
        simpa only [List.map_cons,List.sum_cons,add_assoc] using hend
      have hi := ih (a+p.rate) hend'
      let u := parametricHeatJet g (q::ps) θ
      let T := heatTiltCLM (p.duration θ).toNNReal p.coefficient u.f
      have hh := congrArg T hi
      simp only [map_add,map_smul] at hh
      change T (parametricHeatVelocity g (q::ps) θ)+(a+p.rate) • T (heatGenerator q.coefficient u) =
        (-1/2:ℝ) • T (heatBoundarySum g θ (q::ps) (a+p.rate)) at hh
      have hg := congrArg T (heatGenerator_sub u p.coefficient q.coefficient)
      simp only [map_sub,map_smul] at hg
      rw [heatBoundarySum_cons]
      change p.rate • heatGenerator p.coefficient (u.heatLog (p.duration θ).toNNReal p.coefficient)+
        T (parametricHeatVelocity g (q::ps) θ)+
        a • heatGenerator p.coefficient (u.heatLog (p.duration θ).toNNReal p.coefficient) = _
      rw [← heatTilt_heatGenerator u (p.duration θ).toNNReal p.coefficient]
      change p.rate • T (heatGenerator p.coefficient u)+T (parametricHeatVelocity g (q::ps) θ)+
        a • T (heatGenerator p.coefficient u) = (-1/2:ℝ) •
          ((((q.coefficient:ℝ)-(p.coefficient:ℝ))*(a+p.rate)) • T (u.d1^2)+
            T (heatBoundarySum g θ (q::ps) (a+p.rate)))
      linear_combination (norm := module) hh+(a+p.rate) • hg

lemma heatBoundaryTerms_lower (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ) :
    ∀ z ∈ heatBoundaryTerms g θ ps a, ∀ x,
      ((parametricHeatJet g ps θ).d1 x)^2 ≤ z.2 x := by
  induction ps generalizing a with
  | nil => simp [heatBoundaryTerms]
  | cons p ps ih =>
    cases ps with
    | nil => simp [heatBoundaryTerms]
    | cons q ps =>
      intro z hz x
      let u := parametricHeatJet g (q::ps) θ
      let T := heatTiltCLM (p.duration θ).toNNReal p.coefficient u.f
      have hfirst := u.heatLog_d1_sq_le (p.duration θ).toNNReal p.coefficient x
      change ((parametricHeatJet g (p::q::ps) θ).d1 x)^2 ≤ (T (u.d1^2)) x at hfirst
      simp only [heatBoundaryTerms,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hfirst
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
        exact hfirst.trans (heatTilt_mono (p.duration θ).toNNReal p.coefficient u.f
          (u.d1^2) w.2 (fun y => ih (a+p.rate) w hw y) x)

lemma heatBoundaryTerms_ordered (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ) :
    (heatBoundaryTerms g θ ps a).Pairwise (fun z w => ∀ x, z.2 x ≤ w.2 x) := by
  induction ps generalizing a with
  | nil => simp [heatBoundaryTerms]
  | cons p ps ih =>
    cases ps with
    | nil => simp [heatBoundaryTerms]
    | cons q ps =>
      simp only [heatBoundaryTerms,List.pairwise_cons]
      constructor
      · intro z hz x
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
        exact heatTilt_mono (p.duration θ).toNNReal p.coefficient (parametricHeatJet g (q::ps) θ).f
          ((parametricHeatJet g (q::ps) θ).d1^2) w.2
          (fun y => heatBoundaryTerms_lower g θ (q::ps) (a+p.rate) w hw y) x
      · rw [List.pairwise_map]
        exact (ih (a+p.rate)).imp (fun hz x => heatTilt_mono (p.duration θ).toNNReal p.coefficient
          (parametricHeatJet g (q::ps) θ).f _ _ hz x)

lemma heatBoundarySum_nonneg (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ)
    (ht : ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)), zs.IsSuffix (heatBoundaryTerms g θ ps a) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : 0 ≤ heatBoundarySum g θ ps a x := by
  let zs := heatBoundaryTerms g θ ps a
  let val (z : ℝ×(ℝ→ᵇ ℝ)) : ℝ×ℝ := (z.1,z.2 x)
  have hc : (zs.map val).Pairwise (fun u v => u.2 ≤ v.2) := by
    rw [List.pairwise_map]
    exact (heatBoundaryTerms_ordered g θ ps a).imp (fun h => h x)
  have hc0 : ∀ u ∈ zs.map val, 0 ≤ u.2 := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
    exact (sq_nonneg _).trans (heatBoundaryTerms_lower g θ ps a z hz x)
  have htail : ∀ ys : List (ℝ×ℝ), ys.IsSuffix (zs.map val) → 0 ≤ (ys.map Prod.fst).sum := by
    intro ys hys
    obtain ⟨ws,hws,rfl⟩ := List.suffix_map_iff.mp hys
    simpa only [List.map_map,Function.comp_def,val] using ht ws hws
  have he := weighted_list_tail_nonneg (zs.map val) hc hc0 htail
  change 0 ≤ (BoundedContinuousFunction.evalCLM ℝ x) ((zs.map (fun z => z.1 • z.2)).sum)
  rw [map_list_sum,List.map_map]
  change 0 ≤ (zs.map (fun z => z.1*z.2 x)).sum
  simpa only [List.map_map,Function.comp_def,val] using he

lemma parametricHeatJet_deriv_nonpos (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam)
    (hp : ∀ p ∈ ps, HasDerivAt p.duration p.rate θ ∧ 0 < p.duration θ)
    (hend : (ps.map HeatIntervalParam.rate).sum = 0)
    (ht : ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)), zs.IsSuffix (heatBoundaryTerms g θ ps 0) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : deriv (fun t => (parametricHeatJet g ps t).f x) θ ≤ 0 := by
  have hd := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt θ
    (parametricHeatJet_hasDerivAt g ps θ hp)
  change HasDerivAt (fun t => (parametricHeatJet g ps t).f x) ((parametricHeatVelocity g ps θ) x) θ at hd
  rw [hd.deriv]
  have he := parametricHeatVelocity_boundary g θ ps 0 (by simpa only [zero_add] using hend)
  simp only [zero_smul,add_zero] at he
  rw [he]
  change (-1/2:ℝ)*heatBoundarySum g θ ps 0 x ≤ 0
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (heatBoundarySum_nonneg g θ ps 0 ht x)

end SphericalPerceptron
end
end
end

end OAI
