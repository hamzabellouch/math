import Mathlib
import OAI.Probability.Perceptron.Cascade.PoissonWeightedTotal
import OAI.Probability.Perceptron.Variational.BcfEvalRingHom

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

def BoundedC1 (f : ℝ→ᵇ ℝ) : Prop := ∃ f' : ℝ→ᵇ ℝ, ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x

lemma BoundedC1.zero : BoundedC1 (0 : ℝ→ᵇ ℝ) := ⟨0,fun x => hasDerivAt_const x 0⟩

lemma BoundedC1.add {f h : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (hh : BoundedC1 h) :
    BoundedC1 (f+h) := by
  obtain ⟨f',hf'⟩ := hf
  obtain ⟨h',hh'⟩ := hh
  exact ⟨f'+h',fun x => (hf' x).add (hh' x)⟩

lemma BoundedC1.smul {f : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (a : ℝ) :
    BoundedC1 (a • f) := by
  obtain ⟨f',hf'⟩ := hf
  exact ⟨a • f',fun x => (hf' x).const_mul a⟩

lemma BoundedC1.heatTilt {f h : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (hh : BoundedC1 h)
    (s d : ℝ≥0) : BoundedC1 (heatTiltCLM s d f h) := by
  obtain ⟨f',hf'⟩ := hf
  obtain ⟨h',hh'⟩ := hh
  exact ⟨_,fun x => heatTiltBCF_hasDerivAt s d f f' h h' hf' hh' x⟩

lemma heatGenerator_boundedC1 (g : Jet3) (d : ℝ≥0) : BoundedC1 (heatGenerator d g) :=
  ⟨_,heatGenerator_hasDerivAt g d⟩

structure HeatIntervalParam where
  duration : ℝ → ℝ
  rate : ℝ
  coefficient : ℝ≥0

def parametricHeatJet (g : Jet3) : List HeatIntervalParam → ℝ → Jet3
  | [], _ => g
  | p::ps, t => (parametricHeatJet g ps t).heatLog (p.duration t).toNNReal p.coefficient

def parametricHeatVelocity (g : Jet3) : List HeatIntervalParam → ℝ → (ℝ→ᵇ ℝ)
  | [], _ => 0
  | p::ps, t => p.rate • heatGenerator p.coefficient (parametricHeatJet g (p::ps) t) +
      heatTiltCLM (p.duration t).toNNReal p.coefficient (parametricHeatJet g ps t).f
        (parametricHeatVelocity g ps t)

lemma parametricHeatVelocity_boundedC1 (g : Jet3) (ps : List HeatIntervalParam) (t : ℝ) :
    BoundedC1 (parametricHeatVelocity g ps t) := by
  induction ps with
  | nil => exact BoundedC1.zero
  | cons p ps ih =>
      exact ((heatGenerator_boundedC1 _ _).smul p.rate).add
        (BoundedC1.heatTilt ⟨_,(parametricHeatJet g ps t).has1⟩ ih _ _)

lemma parametricHeatJet_hasDerivAt (g : Jet3) (ps : List HeatIntervalParam) (θ : ℝ)
    (hp : ∀ p ∈ ps, HasDerivAt p.duration p.rate θ ∧ 0 < p.duration θ) :
    HasDerivAt (fun t => (parametricHeatJet g ps t).f) (parametricHeatVelocity g ps θ) θ := by
  induction ps with
  | nil => exact hasDerivAt_const θ g.f
  | cons p ps ih =>
    have hhead := hp p (List.mem_cons_self ..)
    have htail := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    obtain ⟨h',hh'⟩ := parametricHeatVelocity_boundedC1 g ps θ
    have he := heatLogBCF_moving_hasDerivAt (parametricHeatJet g ps θ) p.coefficient
      p.duration (fun t => (parametricHeatJet g ps t).f) θ p.rate
      (parametricHeatVelocity g ps θ) h' hhead.1 hhead.2 htail rfl hh'
    simpa only [parametricHeatJet,parametricHeatVelocity,Jet3.heatLog_f] using he

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

lemma heatLogBCF_time_continuousAt_all (g : Jet3) (d : ℝ≥0) (s : ℝ) :
    ContinuousAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f) s := by
  by_cases hd : d = 0
  · subst d
    have he : (fun t : ℝ => heatLogBCF t.toNNReal 0 g.f) =
        (fun t => gaussianAverageBCF t.toNNReal g.f) := by ext t x; simp [heatLog]
    rw [he]
    exact (gaussianAverageBCF_time_continuous_of_deriv g.f g.d1 g.has1).continuousAt
  let A : ℝ → (ℝ →ᵇ ℝ) := fun t => gaussianAverageBCF t.toNNReal (expBCF d g.f)
  let c : ℝ := Real.exp (-(d : ℝ)*‖g.f‖)
  have hc : 0 < c := Real.exp_pos _
  have hb t : ∀ x, c ≤ A t x := fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg g.f x).1
  have ha : ContinuousAt A s := (gaussianAverageBCF_time_continuous_of_deriv (g.exp d).f (g.exp d).d1 (g.exp d).has1).continuousAt
  have hbd t : ‖heatLogBCF t.toNNReal d g.f - heatLogBCF s.toNNReal d g.f‖ ≤
      (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change |heatLog t.toNNReal d g.f x-heatLog s.toNNReal d g.f x| ≤ _
    simp only [heatLog,hd,↓reduceIte,← mul_sub,abs_mul,abs_inv,abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ)⁻¹*(c⁻¹*|A t x-A s x|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_above hc (hb s x) (hb t x)) (by positivity)
      _ ≤ (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left ((A t-A s).norm_coe_le_norm x) (by positivity)
  have ht : Tendsto (fun t => (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖) (𝓝 s) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
      (ha.sub (continuousAt_const (y := A s))).norm.const_mul ((d : ℝ)⁻¹*c⁻¹) |>.tendsto
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbd ht)

lemma heatLogBCF_terminal_norm_le (s d : ℝ≥0) (f h : ℝ→ᵇ ℝ) :
    ‖heatLogBCF s d f-heatLogBCF s d h‖ ≤ ‖f-h‖ := by
  have hb (u : ℝ→ᵇ ℝ) : ‖heatTiltCLM s d u‖ ≤ 1 := by
    apply (heatTiltCLM s d u).opNorm_le_bound (by norm_num)
    intro v
    change ‖heatTiltBCF s d u v‖ ≤ 1*‖v‖
    simpa only [one_mul] using heatTiltBCF_norm_le s d u v
  simpa only [one_mul] using (convex_univ : Convex ℝ (Set.univ : Set (ℝ→ᵇ ℝ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u _ => (heatLogBCF_hasFDerivAt s d u).hasFDerivWithinAt)
    (fun u _ => hb u) (mem_univ h) (mem_univ f)

lemma heatLogBCF_moving_continuousAt (g : Jet3) (d : ℝ≥0)
    (s : ℝ→ℝ) (F : ℝ→(ℝ→ᵇ ℝ)) (t : ℝ)
    (hs : ContinuousAt s t) (hF : ContinuousAt F t) (he : F t = g.f) :
    ContinuousAt (fun r => heatLogBCF (s r).toNNReal d (F r)) t := by
  have hc := (heatLogBCF_time_continuousAt_all g d (s t)).comp hs
  have hb r : ‖heatLogBCF (s r).toNNReal d (F r)-heatLogBCF (s t).toNNReal d (F t)‖ ≤
      ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖ := by
    calc
      _ ≤ ‖heatLogBCF (s r).toNNReal d (F r)-heatLogBCF (s r).toNNReal d (F t)‖+
          ‖heatLogBCF (s r).toNNReal d (F t)-heatLogBCF (s t).toNNReal d (F t)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        have H := add_le_add_right (heatLogBCF_terminal_norm_le (s r).toNNReal d (F r) (F t))
          ‖heatLogBCF (s r).toNNReal d (F t)-heatLogBCF (s t).toNNReal d (F t)‖
        simpa only [he,add_comm] using H
  have hz : Tendsto (fun r => ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖) (𝓝 t) (𝓝 0) := by
    have H := ((hF.sub (continuousAt_const (y := F t))).norm.add
        (hc.sub (continuousAt_const (y := heatLogBCF (s t).toNNReal d g.f))).norm).tendsto
    change Tendsto (fun r => ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖) (𝓝 t)
      (𝓝 (‖F t-F t‖+‖heatLogBCF (s t).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖)) at H
    simpa only [sub_self,norm_zero,zero_add] using H
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hb hz)

lemma parametricHeatJet_continuousAt (g : Jet3) (ps : List HeatIntervalParam) (t : ℝ)
    (hp : ∀ p ∈ ps, ContinuousAt p.duration t) :
    ContinuousAt (fun r => (parametricHeatJet g ps r).f) t := by
  induction ps with
  | nil => exact continuousAt_const
  | cons p ps ih =>
    simp only [parametricHeatJet,Jet3.heatLog_f]
    exact heatLogBCF_moving_continuousAt (parametricHeatJet g ps t) p.coefficient p.duration
      (fun r => (parametricHeatJet g ps r).f) t (hp p (List.mem_cons_self))
        (ih fun q hq => hp q (List.mem_cons_of_mem p hq)) rfl

lemma parametricHeatJet_tail_order (g : Jet3) (ps : List HeatIntervalParam)
    (hc : ∀ p ∈ ps, Continuous p.duration)
    (hp : ∀ t ∈ Ioo (0:ℝ) 1, ∀ p ∈ ps, HasDerivAt p.duration p.rate t ∧ 0 < p.duration t)
    (hend : (ps.map HeatIntervalParam.rate).sum = 0)
    (ht : ∀ t ∈ Ioo (0:ℝ) 1, ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)),
      zs.IsSuffix (heatBoundaryTerms g t ps 0) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : (parametricHeatJet g ps 1).f x ≤ (parametricHeatJet g ps 0).f x := by
  have hcont : Continuous (fun t => (parametricHeatJet g ps t).f x) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt g ps t (fun p h => (hc p h).continuousAt))
  have hdiff : DifferentiableOn ℝ (fun t => (parametricHeatJet g ps t).f x) (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    exact ((BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t
      (parametricHeatJet_hasDerivAt g ps t (hp t ht))).differentiableAt.differentiableWithinAt
  have hn := antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 1) hcont.continuousOn hdiff
    (fun t h => parametricHeatJet_deriv_nonpos g t ps (hp t (by simpa only [interior_Icc] using h))
      hend (ht t (by simpa only [interior_Icc] using h)) x)
  exact hn ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one

lemma poissonWeightedTotal_law {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (poissonWeightedTotal X) =
      (poissonRandomMeasureLaw (stableLogIntensity b)).map
        (fun η => Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η) := by
  let c := Real.log (∫ x, Real.exp (b*X x) ∂ν)/b
  let F := fun x => X x-c
  have hF : Measurable F := hX.sub_const c
  have hMpos := integral_exp_pos hI
  have hfac (x : S) : Real.exp (b*F x) = Real.exp (-b*c)*Real.exp (b*X x) := by
    dsimp [F]
    rw [← Real.exp_add]
    congr 1
    ring
  have hFI : Integrable (fun x => Real.exp (b*F x)) ν := by
    simp_rw [hfac]
    exact hI.const_mul _
  have hFM : (∫ x, Real.exp (b*F x) ∂ν) = 1 := by
    simp_rw [hfac]
    rw [integral_const_mul,show -b*c = -Real.log (∫ x, Real.exp (b*X x) ∂ν) by dsimp [c]; field_simp,
      Real.exp_neg,Real.exp_log hMpos,inv_mul_cancel₀ hMpos.ne']
  have he := stablePoisson_normalized_mark_projection ν hb.le hF hFI hFM
  have hm : Measurable (fun p : ℝ×S => p.1+F p.2) := measurable_fst.add (hF.comp measurable_snd)
  have hT : poissonWeightedTotal X = fun η => Real.exp c*stablePoissonTotal
      (η.map (fun p : ℝ×S => p.1+F p.2)) := by
    funext η
    rw [← poissonWeightedTotal_eq hF]
    convert poissonWeightedTotal_add_const hF c η using 1
    congr 1
    funext x
    dsimp [F]
    ring
  rw [hT,show (fun η : Measure (ℝ×S) => Real.exp c*stablePoissonTotal
      (η.map (fun p => p.1+F p.2))) =
      (fun η : Measure ℝ => Real.exp c*stablePoissonTotal η) ∘ Measure.map (fun p : ℝ×S => p.1+F p.2) from rfl,
    ← Measure.map_map ((stablePoissonTotal_measurable.const_mul _))
      (Measure.measurable_map _ hm),he]

end SphericalPerceptronFreeEnergy

end

end OAI
