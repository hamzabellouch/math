import Mathlib
import OAI.Probability.SKFluctuations.ProjectionRootEstimate

namespace OAI

/-! Scalar Curvature Lower. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalar_line_derivative {f g : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (g x) x)
    (x v : Fin 1 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f ((x+s • v) 0))
      (∑ i : Fin 1, v i*g ((x+t • v) 0)) t := by
  have hh := (hd (x 0+t*v 0)).comp t
    ((hasDerivAt_const t (x 0)).add ((hasDerivAt_id t).mul_const (v 0)))
  convert! hh using 1
  simp only [Fin.sum_univ_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,zero_add,one_mul]
  ring

 noncomputable def HeatJet.withCurvature (J : HeatJet 0) : HeatJet 0 :=
  { J with
    A := fun x => Scalar.curvature (x 0)
    A₁ := fun _ x => Scalar.third (x 0)
    A₂ := fun _ x => Scalar.fourth (x 0)
    smoothA := Scalar.curvature_pi_bddSmooth
    smoothA₁ := fun _ => Scalar.third_bddSmooth
    smoothA₂ := fun _ => Scalar.fourth_bddSmooth
    derivA := scalar_line_derivative Scalar.curvature_derivative
    derivA₁ := by
      intro i x t
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Fin.sum_univ_one,Pi.single_eq_same,one_mul] using
        scalar_line_derivative Scalar.third_derivative x (Pi.single 0 1) t }

 theorem HeatJet.curvature_test_derivative_lower {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) (t : ℝ) (x : Fin 1 → ℝ) :
    -4*clockTest m J.F (fun y => Scalar.curvature (y 0)) t x ≤
      clockTestDerivative m J.F J.G J.H J.withCurvature.A
        J.withCurvature.A₁ J.withCurvature.A₂ t x := by
  let W := fun y : Fin 1 → ℝ => Scalar.curvature (y 0)
  have hp (y : Fin 1 → ℝ) : 0 ≤ potentialHeatTrace m J.G J.H y ∧
      potentialHeatTrace m J.G J.H y ≤ 2 := by
    simp only [potentialHeatTrace,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    have hg : (J.G 0 y)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hJ.gradient y)
    have hmsq : m^2 ≤ 1 := by nlinarith
    constructor
    · exact add_nonneg (mul_nonneg hm (hJ y).1) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · have hh := mul_le_mul hm1 (hJ.curvature y) (hJ y).1 zero_le_one
      have hgg := mul_le_mul hmsq hg (sq_nonneg _) zero_le_one
      nlinarith
  have hq (y : Fin 1 → ℝ) : -6*W y ≤ testedHeatTrace m J.G J.H
      J.withCurvature.A J.withCurvature.A₁ J.withCurvature.A₂ y := by
    have hw := (Scalar.curvature_bounds (y 0)).1
    have habs : |Scalar.third (y 0)*J.G 0 y| ≤ 2*W y := by
      rw [abs_mul]
      exact (mul_le_mul (Scalar.third_abs_le_curvature _) (hJ.gradient y)
        (abs_nonneg _) (mul_nonneg (by norm_num) hw)).trans_eq (mul_one _)
    have ht := (abs_le.mp habs).1
    have htz : -(2*W y) ≤ m*(Scalar.third (y 0)*J.G 0 y) := by
      nlinarith [mul_nonneg hm (sub_nonneg.mpr ht),mul_nonneg (sub_nonneg.mpr hm1) hw]
    have hww := mul_nonneg hw (hp y).1
    have hf := Scalar.fourth_lower (y 0)
    simp only [testedHeatTrace,potentialHeatTrace,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,HeatJet.withCurvature] at *
    dsimp only [W] at *
    nlinarith
  have hW : BddSmooth 0 W := Scalar.curvature_pi_bddSmooth
  have hlo := clockTest_mono J.lipschitz (hW.const_mul (-6))
    (testedHeatTrace_bddSmooth J.smoothG J.smoothH J.withCurvature.smoothA
      J.withCurvature.smoothA₁ J.withCurvature.smoothA₂ m) hq m t x
  rw [clockTest_const_mul] at hlo
  have hhi := clockTest_mono J.lipschitz (potentialHeatTrace_bddSmooth J.smoothG J.smoothH m)
    (BddSmooth.const 0 2) (fun y => (hp y).2) m t x
  rw [clockTest_const J.lipschitz] at hhi
  have hwp := clockTest_nonneg J.lipschitz (fun y => (Scalar.curvature_bounds (y 0)).1) m t x
  have hh := mul_le_mul_of_nonneg_left hhi hwp
  change -4*clockTest m J.F W t x ≤ _
  unfold clockTestDerivative
  change -4*clockTest m J.F W t x ≤ (1/2:ℝ)*
    (clockTest m J.F (testedHeatTrace m J.G J.H J.withCurvature.A
      J.withCurvature.A₁ J.withCurvature.A₂) t x-
      clockTest m J.F W t x*clockTest m J.F (potentialHeatTrace m J.G J.H) t x)
  nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
 theorem exp_lower_of_clock_derivative {f d : ℝ → ℝ} (a : ℝ)
    (hc : ContinuousOn f (Ici 0)) (hd : ∀ s, 0 < s → HasDerivAt f (d s) s)
    (hb : ∀ s, 0 < s → -a*f s ≤ d s) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-a*t)*f 0 ≤ f t := by
  let g := fun s => Real.exp (a*s)*f s
  have hgd (s : ℝ) (hs : 0 < s) : HasDerivAt g
      (Real.exp (a*s)*(d s+a*f s)) s := by
    convert (((hasDerivAt_id s).const_mul a).exp.mul (hd s hs)) using 1 <;>
      first | rfl | dsimp [g]; ring
  have hgc : ContinuousOn g (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hgc
    · intro s hs
      rw [interior_Ici] at hs
      exact (hgd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hgd s hs).deriv]
      exact mul_nonneg (Real.exp_nonneg _) (by linarith [hb s hs])
  have hh := mul_le_mul_of_nonneg_left
    (hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht) (Real.exp_nonneg (-a*t))
  simpa only [g,mul_zero,Real.exp_zero,one_mul,← mul_assoc,← Real.exp_add,
    neg_mul,neg_add_cancel,Real.exp_zero,one_mul] using hh

 theorem HeatJet.curvature_test_lower {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) {t : ℝ} (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    Real.exp (-4*t)*Scalar.curvature (x 0) ≤
      clockTest m J.F (fun y => Scalar.curvature (y 0)) t x := by
  let K := J.withCurvature
  have hc : Continuous (fun s => clockTest m J.F K.A s x) :=
    (clockTest_continuous J.lipschitz K.smoothA m).comp (continuous_id.prodMk continuous_const)
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt (fun t => clockTest m J.F K.A t x)
      (clockTestDerivative m J.F J.G J.H K.A K.A₁ K.A₂ s x) s :=
    (hasDerivWithinAt_clockTest J.lipschitz K.smoothA J.smoothG J.smoothH
      K.smoothA₁ K.smoothA₂ J.derivF J.derivG K.derivA K.derivA₁ m x hs.le).hasDerivAt
        (Ici_mem_nhds hs)
  have hh := exp_lower_of_clock_derivative 4 hc.continuousOn hd
    (fun s _ => HeatJet.curvature_test_derivative_lower hJ hm hm1 s x) ht
  rw [clockTest_zero] at hh
  exact hh

 theorem HeatJet.evolve_curvature_lower {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (hH : ∀ y, c*Scalar.curvature (y 0) ≤ J.H 0 y)
    {t : ℝ} (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    (c*Real.exp (-4*t))*Scalar.curvature (x 0) ≤ (J.evolve hm t).H 0 x := by
  have h1 := mul_le_mul_of_nonneg_left (HeatJet.curvature_test_lower hJ hm.le hm1 ht x) hc
  have h2 := clockTest_mono J.lipschitz (Scalar.curvature_pi_bddSmooth.const_mul c)
    (J.smoothH 0) hH m t x
  rw [clockTest_const_mul] at h2
  have hv := clockTest_variance_nonneg J.lipschitz (J.smoothG 0) m t x
  change _ ≤ clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x
  simp only [clockGradient,← pow_two]
  nlinarith [mul_nonneg hm.le hv]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarTerminal_G (x : Fin 1 → ℝ) : scalarTerminal.G 0 x = Real.tanh (x 0) := by
  have hd := scalarTerminal.derivF_coord 0 x 0
  have ht := scalar_line_derivative Scalar.logCosh_derivative x (Pi.single 0 1) 0
  simp only [zero_smul,add_zero,scalarTerminal_F] at hd
  simp only [Fin.sum_univ_one,Pi.single_eq_same,one_mul,zero_smul,add_zero,Scalar.logCosh] at ht
  exact hd.unique ht

 theorem scalarTerminal_H (x : Fin 1 → ℝ) : scalarTerminal.H 0 x = Scalar.curvature (x 0) := by
  have hd := scalarTerminal.derivG 0 x 0
  have ht := scalar_line_derivative Scalar.tanh_derivative x (Pi.single 0 1) 0
  simp only [zero_smul,add_zero,scalarTerminal_G] at hd
  simp only [Fin.sum_univ_one,Pi.single_eq_same,one_mul,zero_smul,add_zero] at ht
  exact hd.unique ht

 theorem scalarTerminal_admissible : scalarTerminal.ScalarAdmissible := by
  intro x
  rw [scalarTerminal_G,scalarTerminal_H]
  exact ⟨(Scalar.curvature_bounds _).1,by dsimp [Scalar.curvature]; linarith⟩

 theorem HeatJet.ScalarAdmissible.schedule {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (cs : List HeatClock) (hc : ∀ c ∈ cs, c.mass ≤ 1) : (J.schedule cs).ScalarAdmissible := by
  induction cs with
  | nil => exact hJ
  | cons c cs ih =>
    exact (ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))).evolve c.positive
      (hc c (List.mem_cons_self ..)) c.time

 theorem scalar_schedule_curvature_lower (cs : List HeatClock)
    (hc : ∀ c ∈ cs, c.mass ≤ 1) (x : Fin 1 → ℝ) :
    Real.exp (-4*(cs.map (fun c => (c.time:ℝ))).sum)*Scalar.curvature (x 0) ≤
      (scalarTerminal.schedule cs).H 0 x := by
  induction cs generalizing x with
  | nil =>
    simp only [List.map_nil,List.sum_nil,mul_zero,Real.exp_zero,one_mul,HeatJet.schedule,
      scalarTerminal_H,le_refl]
  | cons c cs ih =>
    have hc' : ∀ d ∈ cs, d.mass ≤ 1 := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    have hh := HeatJet.evolve_curvature_lower (scalarTerminal_admissible.schedule cs hc')
      c.positive (hc c (List.mem_cons_self ..)) (Real.exp_nonneg _)
      (ih hc') c.time.coe_nonneg x
    apply le_trans _ hh
    apply le_of_eq
    rw [← Real.exp_add]
    simp only [List.map_cons,List.sum_cons]
    congr 2
    ring

 theorem PositiveMassProfile.grid_total_time (α : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    ((α.grid l t k).map (fun c => (c.time:ℝ))).sum = t := by
  induction k generalizing l t with
  | zero => simp [PositiveMassProfile.grid]
  | succ k ih =>
    simp only [PositiveMassProfile.grid,List.map_append,List.sum_append,ih,NNReal.coe_div,NNReal.coe_ofNat]
    ring

 theorem scalarSourceJet_one_schedule (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : ℝ) :
    scalarSourceJet (heatSteps cs) 1 x = (scalarTerminal.schedule cs).G 0 (fun _ => x) := by
  have hd := scalarSourceJet_hasDerivAt ho 0 x
  have ht := (scalarTerminal.schedule cs).derivF 0 (fun _ => 1) x
  have he (s : ℝ) : (0 : Fin 1 → ℝ)+s • (fun _ => (1:ℝ)) = (fun _ => s) := by ext i; simp
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,one_mul,he,scalar_schedule_eq_hierarchy] at ht
  exact hd.unique ht

 theorem scalarSourceJet_two_schedule (cs : List HeatClock)
    (ho : OrderedSteps 0 (heatSteps (ι := Fin 1) cs)) (x : ℝ) :
    scalarSourceJet (heatSteps cs) 2 x = (scalarTerminal.schedule cs).H 0 (fun _ => x) := by
  have hd := scalarSourceJet_hasDerivAt ho 1 x
  have ht := (scalarTerminal.schedule cs).derivG 0 0 x
  have he (s : ℝ) : (0 : Fin 1 → ℝ)+s • Pi.single 0 (1:ℝ) = (fun _ => s) := by
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  simp only [he] at ht
  have heG : scalarSourceJet (heatSteps cs) 1 =
      (fun s => (scalarTerminal.schedule cs).G 0 (fun _ => s)) :=
    funext (scalarSourceJet_one_schedule cs ho)
  rw [heG] at hd
  exact hd.unique ht

 theorem scalarCappedJets_curvature_lower (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (n : ℕ) (x : ℝ) :
    Real.exp (-4*(t:ℝ))*Scalar.curvature x ≤ scalarCappedJets α l t n 2 x := by
  have hc : ∀ c ∈ (α.cappedApprox n).grid l t n, c.mass ≤ 1 := by
    intro c hc
    exact ((α.cappedApprox n).grid_mass_bounds l t n hc).2.trans
      (α.cappedApprox_le_one hα n (l+t))
  rw [scalarCappedJets,scalarSourceJet_two_schedule _ (scalarCappedJets_ordered α hα l t n)]
  have hh := scalar_schedule_curvature_lower ((α.cappedApprox n).grid l t n) hc (fun _ => x)
  rw [PositiveMassProfile.grid_total_time] at hh
  exact hh

 

 theorem scalarProfileJet_curvature_lower (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    Real.exp (-4*(t:ℝ))*Scalar.curvature x ≤ scalarProfileJet α l t 2 x :=
  ge_of_tendsto ((scalarProfileJet_tendstoUniformly α hα l t 2).tendsto_at x)
    (Eventually.of_forall (fun n => scalarCappedJets_curvature_lower α hα l t n x))

 theorem scalarProfileJet_curvature_pos (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    0 < scalarProfileJet α l t 2 x :=
  (mul_pos (Real.exp_pos _) (Scalar.curvature_pos x)).trans_le
    (scalarProfileJet_curvature_lower α hα l t x)

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.evolve_potential_bound {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {t : ℝ} (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    |(J.evolve hm t).F x-J.F x| ≤ t/2 := by
  have hc : ContinuousOn (fun s => (J.evolve hm s).F x) (Ici 0) :=
    ((clockContinuation_continuous J.lipschitz m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  have hd (s : ℝ) (hs : 0 < s) := J.evolve_time_F hm hs x
  have hb (s : ℝ) (hs : 0 < s) :
      |(1/2:ℝ)*∑ i, ((J.evolve hm s).H i x+m*((J.evolve hm s).G i x)^2)| ≤ 1/2 := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    have hh := (hJ.evolve hm hm1 s) x
    have hsq := sq_nonneg ((J.evolve hm s).G 0 x)
    have hmsq := mul_nonneg (sub_nonneg.mpr hm1) hsq
    have hpos := mul_nonneg hm.le hsq
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (1/2:ℝ)*
      ((J.evolve hm s).H 0 x+m*((J.evolve hm s).G 0 x)^2))]
    nlinarith [hh.1,hh.2]
  have hh := abs_sub_le_mul_of_deriv_interior hc hd hb (le_refl 0) ht
  simpa only [HeatJet.evolve,clockContinuation_zero hm.ne',sub_zero,abs_of_nonneg ht,
    one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] using hh

theorem scalar_schedule_potential_bound (cs : List HeatClock)
    (hc : ∀ c ∈ cs, c.mass ≤ 1) (x : Fin 1 → ℝ) :
    |(scalarTerminal.schedule cs).F x-Scalar.logCosh (x 0)| ≤
      (cs.map (fun c => (c.time:ℝ))).sum/2 := by
  induction cs with
  | nil => simp only [HeatJet.schedule,scalarTerminal_F,Scalar.logCosh,sub_self,abs_zero,
      List.map_nil,List.sum_nil,zero_div,le_refl]
  | cons c cs ih =>
    have hc' : ∀ d ∈ cs, d.mass ≤ 1 := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    have hh := HeatJet.evolve_potential_bound (scalarTerminal_admissible.schedule cs hc')
      c.positive (hc c (List.mem_cons_self ..)) c.time.coe_nonneg x
    have ht := abs_add_le ((scalarTerminal.schedule (c::cs)).F x-(scalarTerminal.schedule cs).F x)
      ((scalarTerminal.schedule cs).F x-Scalar.logCosh (x 0))
    simp only [sub_add_sub_cancel] at ht
    simp only [List.map_cons,List.sum_cons]
    change |((scalarTerminal.schedule cs).evolve c.positive c.time).F x-Scalar.logCosh (x 0)| ≤ _
    change |((scalarTerminal.schedule cs).evolve c.positive c.time).F x-Scalar.logCosh (x 0)| ≤ _ at ht
    dsimp only [HeatJet.schedule] at ht
    linarith [ih hc']

theorem scalarCappedJets_potential_bound (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (n : ℕ) (x : ℝ) :
    |scalarCappedJets α l t n 0 x-Scalar.logCosh x| ≤ (t:ℝ)/2 := by
  have hc : ∀ c ∈ (α.cappedApprox n).grid l t n, c.mass ≤ 1 := by
    intro c hc
    exact ((α.cappedApprox n).grid_mass_bounds l t n hc).2.trans
      (α.cappedApprox_le_one hα n (l+t))
  have hh := scalar_schedule_potential_bound ((α.cappedApprox n).grid l t n) hc (fun _ => x)
  rw [PositiveMassProfile.grid_total_time,scalar_schedule_eq_hierarchy] at hh
  exact hh

theorem scalarProfileJet_potential_bound (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    |scalarProfileJet α l t 0 x-Scalar.logCosh x| ≤ (t:ℝ)/2 :=
  le_of_tendsto (((scalarProfileJet_tendstoUniformly α hα l t 0).tendsto_at x).sub_const _).abs
    (Eventually.of_forall (fun n => scalarCappedJets_potential_bound α hα l t n x))

theorem scalarProfileJet_admissible (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    0 ≤ scalarProfileJet α l t 2 x ∧
      scalarProfileJet α l t 2 x+(scalarProfileJet α l t 1 x)^2 ≤ 1 := by
  have hc (n : ℕ) : ∀ c ∈ (α.cappedApprox n).grid l t n, c.mass ≤ 1 := by
    intro c hc
    exact ((α.cappedApprox n).grid_mass_bounds l t n hc).2.trans
      (α.cappedApprox_le_one hα n (l+t))
  have hb (n : ℕ) : scalarCappedJets α l t n 2 x+(scalarCappedJets α l t n 1 x)^2 ≤ 1 := by
    have ho := scalarCappedJets_ordered α hα l t n
    have hh := (scalarTerminal_admissible.schedule ((α.cappedApprox n).grid l t n) (hc n)) (fun _ => x)
    simpa only [scalarCappedJets,scalarSourceJet_one_schedule _ ho,
      scalarSourceJet_two_schedule _ ho] using hh.2
  refine ⟨(scalarProfileJet_curvature_pos α hα l t x).le,?_⟩
  exact le_of_tendsto (((scalarProfileJet_tendstoUniformly α hα l t 2).tendsto_at x).add
    (((scalarProfileJet_tendstoUniformly α hα l t 1).tendsto_at x).pow 2))
    (Eventually.of_forall hb)

theorem scalarProfileJet_gradient_strictMono (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    StrictMono (scalarProfileJet α l t 1) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(scalarProfileJet_hasDerivAt α hα l t 1 x).deriv]
  exact scalarProfileJet_curvature_pos α hα l t x

theorem scalarProfileJet_gradient_mem (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    scalarProfileJet α l t 1 x ∈ Ioo (-1) 1 := by
  have hh := (scalarProfileJet_admissible α hα l t x).2
  have hp := scalarProfileJet_curvature_pos α hα l t x
  have hs : (scalarProfileJet α l t 1 x)^2 < 1 := by linarith
  exact ⟨(abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hs)).1,
    (abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hs)).2⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open Filter Set
open scoped Topology

theorem logCosh_lower (x : ℝ) : |x|-Real.log 2 ≤ logCosh x := by
  have hl (y : ℝ) : y-Real.log 2 ≤ logCosh y := by
    have he : Real.exp y/2 ≤ Real.cosh y := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-y)]
    have hh := Real.log_le_log (div_pos (Real.exp_pos y) (by norm_num)) he
    simpa only [Real.log_div (Real.exp_ne_zero y) (by norm_num : (2:ℝ) ≠ 0),
      Real.log_exp,logCosh] using hh
  rcases le_total 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using hl x
  · simpa only [abs_of_nonpos hx,logCosh,Real.cosh_neg] using hl (-x)

theorem exists_slope_gt_of_coercive {F G : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x, HasDerivAt F (G x) x) (hb : ∀ x, |x|-C ≤ F x)
    {v : ℝ} (hv : v < 1) : ∃ x, v < G x := by
  let R := (|F 0|+C+1)/(1-v)
  have hp : 0 < 1-v := sub_pos.mpr hv
  have hR : 0 < R := div_pos (by positivity) hp
  have he : R*(1-v) = |F 0|+C+1 := div_mul_cancel₀ _ hp.ne'
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  obtain ⟨x,hx,h⟩ := exists_hasDerivAt_eq_slope F G hR hc.continuousOn (fun x _ => hd x)
  refine ⟨x,?_⟩
  rw [h,sub_zero]
  apply (lt_div_iff₀ hR).mpr
  have hbR := hb R
  rw [abs_of_pos hR] at hbR
  nlinarith [le_abs_self (F 0)]

theorem exists_slope_lt_of_coercive {F G : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x, HasDerivAt F (G x) x) (hb : ∀ x, |x|-C ≤ F x)
    {v : ℝ} (hv : -1 < v) : ∃ x, G x < v := by
  have hD (x : ℝ) : HasDerivAt (fun y => F (-y)) (-G (-x)) x := by
    simpa only [Function.comp_def,mul_neg_one] using (hd (-x)).comp x (hasDerivAt_neg x)
  have hB (x : ℝ) : |x|-C ≤ F (-x) := by simpa only [abs_neg] using hb (-x)
  obtain ⟨x,hx⟩ := exists_slope_gt_of_coercive hC hD hB (v := -v) (by linarith)
  exact ⟨-x,by linarith⟩

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarProfileJet_gradient_range (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    Set.range (scalarProfileJet α l t 1) = Ioo (-1) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,rfl⟩
    exact scalarProfileJet_gradient_mem α hα l t x
  · intro v hv
    have hC : 0 ≤ Real.log 2+(t:ℝ)/2 := by positivity
    have hb (x : ℝ) : |x|-(Real.log 2+(t:ℝ)/2) ≤ scalarProfileJet α l t 0 x := by
      have hh := (abs_le.mp (scalarProfileJet_potential_bound α hα l t x)).1
      linarith [Scalar.logCosh_lower x]
    have hd := scalarProfileJet_hasDerivAt α hα l t 0
    obtain ⟨a,ha⟩ := Scalar.exists_slope_lt_of_coercive hC hd hb hv.1
    obtain ⟨b,hb⟩ := Scalar.exists_slope_gt_of_coercive hC hd hb hv.2
    have hm := scalarProfileJet_gradient_strictMono α hα l t
    have hab : a ≤ b := (hm.lt_iff_lt.mp (ha.trans hb)).le
    have hc : Continuous (scalarProfileJet α l t 1) :=
      continuous_iff_continuousAt.mpr (fun x => (scalarProfileJet_hasDerivAt α hα l t 1 x).continuousAt)
    obtain ⟨x,_,hx⟩ := intermediate_value_Icc hab hc.continuousOn ⟨ha.le,hb.le⟩
    exact ⟨x,hx⟩

 

noncomputable def scalarSlopeInverse (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) : ℝ → ℝ :=
  Function.invFun (scalarProfileJet α l t 1)

theorem scalarSlopeInverse_gradient (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    scalarSlopeInverse α l t (scalarProfileJet α l t 1 x) = x :=
  Function.leftInverse_invFun (scalarProfileJet_gradient_strictMono α hα l t).injective x

theorem scalarSlopeInverse_right (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    scalarProfileJet α l t 1 (scalarSlopeInverse α l t b) = b := by
  rw [← scalarProfileJet_gradient_range α hα l t] at hb
  obtain ⟨x,rfl⟩ := hb
  rw [scalarSlopeInverse_gradient α hα l t]

theorem scalarSlopeInverse_strictMonoOn (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    StrictMonoOn (scalarSlopeInverse α l t) (Ioo (-1) 1) := by
  intro a ha b hb hab
  apply (scalarProfileJet_gradient_strictMono α hα l t).lt_iff_lt.mp
  simpa only [scalarSlopeInverse_right α hα l t ha,scalarSlopeInverse_right α hα l t hb] using hab

theorem scalarSlopeInverse_continuousAt (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    ContinuousAt (scalarSlopeInverse α l t) b := by
  apply (scalarSlopeInverse_strictMonoOn α hα l t).continuousAt_of_image_mem_nhds
    (isOpen_Ioo.mem_nhds hb)
  have he : scalarSlopeInverse α l t '' Ioo (-1) 1 = univ := by
    apply eq_univ_of_forall
    intro x
    exact ⟨scalarProfileJet α l t 1 x,scalarProfileJet_gradient_mem α hα l t x,
      scalarSlopeInverse_gradient α hα l t x⟩
  rw [he]
  exact univ_mem

theorem scalarSlopeInverse_hasDerivAt (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    HasDerivAt (scalarSlopeInverse α l t)
      (scalarProfileJet α l t 2 (scalarSlopeInverse α l t b))⁻¹ b :=
  (scalarProfileJet_hasDerivAt α hα l t 1 _).of_local_left_inverse
    (scalarSlopeInverse_continuousAt α hα l t hb)
    (scalarProfileJet_curvature_pos α hα l t _).ne'
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hb] with c hc
      exact scalarSlopeInverse_right α hα l t hc)

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem clockContinuation_even {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (hF : ∀ x, F (-x) = F x) (m t : ℝ) (x : ι → ℝ) :
    clockContinuation m F t (-x) = clockContinuation m F t x := by
  let T := signEquiv (fun _ : ι => (-1:ℝ)) (fun _ => by norm_num)
  have hT : MeasurePreserving T (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t))
      (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t)) := signEquiv_gaussian _ _ _
  have he (z : ι → ℝ) : -x+T z = -(x+z) := by ext i; simp [T,signEquiv_apply]; ring
  have hi := hT.integral_comp T.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => Real.exp (m*F (-x+z)))
  simp only [he,hF] at hi
  change Real.log _ / m = Real.log _ / m
  rw [hi]

theorem scalar_schedule_even (cs : List HeatClock) (x : Fin 1 → ℝ) :
    (scalarTerminal.schedule cs).F (-x) = (scalarTerminal.schedule cs).F x := by
  induction cs generalizing x with
  | nil => simp only [HeatJet.schedule,scalarTerminal_F,Pi.neg_apply,Real.cosh_neg]
  | cons c cs ih => exact clockContinuation_even ih c.mass c.time x

theorem scalarProfileJet_zero_even (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    scalarProfileJet α l t 0 (-x) = scalarProfileJet α l t 0 x := by
  have he (n : ℕ) : scalarCappedJets α l t n 0 (-x) = scalarCappedJets α l t n 0 x := by
    have hh := scalar_schedule_even ((α.cappedApprox n).grid l t n) (fun _ => x)
    rw [show -(fun _ : Fin 1 => x) = (fun _ => -x) from rfl] at hh
    simpa only [scalar_schedule_eq_hierarchy,scalarCappedJets,scalarSourceJet] using hh
  exact tendsto_nhds_unique ((scalarProfileJet_tendstoUniformly α hα l t 0).tendsto_at (-x))
    (by simpa only [he] using (scalarProfileJet_tendstoUniformly α hα l t 0).tendsto_at x)

theorem scalarProfileJet_parity (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (k : ℕ) (x : ℝ) :
    scalarProfileJet α l t k (-x) = (-1:ℝ)^k*scalarProfileJet α l t k x := by
  induction k generalizing x with
  | zero => simpa only [pow_zero,one_mul] using scalarProfileJet_zero_even α hα l t x
  | succ k ih =>
    have he : (fun y => scalarProfileJet α l t k (-y)) =
        (fun y => (-1:ℝ)^k*scalarProfileJet α l t k y) := funext ih
    have hd := (scalarProfileJet_hasDerivAt α hα l t k (-x)).comp x (hasDerivAt_neg x)
    have hr := (scalarProfileJet_hasDerivAt α hα l t k x).const_mul ((-1:ℝ)^k)
    change HasDerivAt (fun y => scalarProfileJet α l t k (-y)) _ x at hd
    rw [he] at hd
    have hh := hd.unique hr
    simp only [mul_neg_one] at hh
    rw [pow_succ]
    nlinarith

theorem scalarProfileJet_gradient_zero (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    scalarProfileJet α l t 1 0 = 0 := by
  have hh := scalarProfileJet_parity α hα l t 1 0
  simp only [neg_zero,pow_one,neg_one_mul] at hh
  linarith

theorem scalarSlopeInverse_zero (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) : scalarSlopeInverse α l t 0 = 0 := by
  simpa only [scalarProfileJet_gradient_zero α hα l t] using scalarSlopeInverse_gradient α hα l t 0

theorem scalarSlopeInverse_odd (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    scalarSlopeInverse α l t (-b) = -scalarSlopeInverse α l t b := by
  have hnb : -b ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hb.2],by linarith [hb.1]⟩
  apply (scalarProfileJet_gradient_strictMono α hα l t).injective
  rw [scalarSlopeInverse_right α hα l t hnb,scalarProfileJet_parity α hα l t 1,
    scalarSlopeInverse_right α hα l t hb,pow_one,neg_one_mul]

 
noncomputable def scalarSlopeCurvature (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  scalarProfileJet α l t 2 (scalarSlopeInverse α l t b)

 
noncomputable def scalarSlopeCurvature₁ (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  scalarProfileJet α l t 3 (scalarSlopeInverse α l t b)/scalarSlopeCurvature α l t b

noncomputable def scalarSlopeCurvature₂ (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  (scalarProfileJet α l t 4 (scalarSlopeInverse α l t b)*scalarSlopeCurvature α l t b-
    (scalarProfileJet α l t 3 (scalarSlopeInverse α l t b))^2)/(scalarSlopeCurvature α l t b)^3

theorem scalarSlopeCurvature_pos (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (b : ℝ) :
    0 < scalarSlopeCurvature α l t b := scalarProfileJet_curvature_pos α hα l t _

theorem scalarSlopeCurvature_upper (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    scalarSlopeCurvature α l t b ≤ 1-b^2 := by
  have hh := (scalarProfileJet_admissible α hα l t (scalarSlopeInverse α l t b)).2
  rw [scalarSlopeInverse_right α hα l t hb] at hh
  exact (le_sub_iff_add_le).mpr hh

theorem scalarSlopeCurvature_hasDerivAt (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    HasDerivAt (scalarSlopeCurvature α l t) (scalarSlopeCurvature₁ α l t b) b := by
  have hh := (scalarProfileJet_hasDerivAt α hα l t 2 _).comp b
    (scalarSlopeInverse_hasDerivAt α hα l t hb)
  change HasDerivAt (scalarSlopeCurvature α l t) _ b at hh
  convert hh using 1
  exact div_eq_mul_inv _ _

theorem scalarSlopeCurvature₁_hasDerivAt (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    HasDerivAt (scalarSlopeCurvature₁ α l t) (scalarSlopeCurvature₂ α l t b) b := by
  have hn := (scalarProfileJet_hasDerivAt α hα l t 3 _).comp b
    (scalarSlopeInverse_hasDerivAt α hα l t hb)
  have hd := scalarSlopeCurvature_hasDerivAt α hα l t hb
  have hp := (scalarSlopeCurvature_pos α hα l t b).ne'
  have hh := hn.div hd hp
  change HasDerivAt (scalarSlopeCurvature₁ α l t) _ b at hh
  convert hh using 1
  dsimp only [scalarSlopeCurvature₂,scalarSlopeCurvature₁]
  change (_ * scalarSlopeCurvature α l t b - _^2) / _^3 =
    ((scalarProfileJet α l t 4 (scalarSlopeInverse α l t b) *
      (scalarSlopeCurvature α l t b)⁻¹) * scalarSlopeCurvature α l t b -
     scalarProfileJet α l t 3 (scalarSlopeInverse α l t b) *
      (scalarProfileJet α l t 3 (scalarSlopeInverse α l t b)/scalarSlopeCurvature α l t b)) /
      (scalarSlopeCurvature α l t b)^2
  field_simp

theorem scalarSlopeCurvature_even (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    scalarSlopeCurvature α l t (-b) = scalarSlopeCurvature α l t b := by
  rw [scalarSlopeCurvature,scalarSlopeInverse_odd α hα l t hb,scalarProfileJet_parity α hα l t 2]
  norm_num [scalarSlopeCurvature]

theorem scalarSlopeCurvature₁_zero (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) : scalarSlopeCurvature₁ α l t 0 = 0 := by
  have hh := scalarProfileJet_parity α hα l t 3 0
  norm_num at hh
  have h3 : scalarProfileJet α l t 3 0 = 0 := by linarith
  simp only [scalarSlopeCurvature₁,scalarSlopeInverse_zero α hα l t,h3,zero_div]

end SKFluctuations.Hierarchy

end

end OAI
