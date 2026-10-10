import Mathlib
import OAI.Probability.SKFluctuations.RescaledProfileTestContinuity

namespace OAI

/-! Scalar Jet Power Tests. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem tendstoUniformly_pow_of_abs_le {X : Type*} {f : ℕ → X → ℝ} {g : X → ℝ}
    {K : ℝ} (hf : ∀ n x, |f n x| ≤ K) (hg : ∀ x, |g x| ≤ K)
    (ht : TendstoUniformly f g atTop) (p : ℕ) :
    TendstoUniformly (fun n x => (f n x)^p) (fun x => (g x)^p) atTop := by
  exact UniformContinuousOn.comp_tendstoUniformly (s:=Icc (-K) K)
    (fun n x => abs_le.mp (hf n x)) (fun x => abs_le.mp (hg x))
    (isCompact_Icc.uniformContinuousOn_of_continuous (continuous_pow p).continuousOn) ht

theorem scalarTailSpatialJet_bddSmooth_all {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k j : ℕ) (q : ℝ) :
    BddSmooth j (scalarTailSpatialJet hT α (k+1) q) :=
  scalarProfileJet_bddSmooth_all (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) _ _ j k

noncomputable def scalarJetPowerTest {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k p : ℕ) (q : ℝ) : HeatJet 0 :=
  (scalarTailJet hT α q).withTest (fun y => (scalarTailSpatialJet hT α (k+1) q y)^p)
    ((scalarTailSpatialJet_bddSmooth_all hT α k 2 q).pow p)

noncomputable def scalarPlantedJetPower {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k p : ℕ) (q : ℝ) : ℝ :=
  (scalarJetPowerTest hT α k p q).nonnegativeProfileTest (rescaledMassProfile α hT)
    0 (Real.toNNReal (T*q)) 0

theorem scalarJetPowerTest_bound {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k p : ℕ) (q : ℝ) (y : Fin 1 → ℝ) :
    |(scalarJetPowerTest hT α k p q).A y| ≤ (ReplicaTree.attachmentCount 1 k:ℝ)^p := by
  change |(scalarTailSpatialJet hT α (k+1) q y)^p| ≤ _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (scalarProfileJet_bound (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) _ _ k (y 0)) p

theorem scalarPlantedJetPower_abs_le {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k p : ℕ) (q : ℝ) :
    |scalarPlantedJetPower hT α k p q| ≤ (ReplicaTree.attachmentCount 1 k:ℝ)^p :=
  (scalarJetPowerTest hT α k p q).nonnegativeProfileTest_abs_le
    (scalarJetPowerTest_bound hT α k p q) (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) 0 _ 0

theorem scalarPlantedJetPower_continuous {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k p : ℕ) : Continuous (scalarPlantedJetPower hT α k p) := by
  rw [continuous_iff_seqContinuous]
  intro q r hq
  have hb (u : ℝ) (y : Fin 1 → ℝ) :
      |scalarTailSpatialJet hT α (k+1) u y| ≤ (ReplicaTree.attachmentCount 1 k:ℝ) :=
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ k (y 0)
  have hA := tendstoUniformly_pow_of_abs_le (fun n => hb (q n)) (hb r)
    (scalarTailSpatialJet_window_tendsto hT α hq (k+1)) p
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun n => scalarJetPowerTest hT α k p (q n)) (scalarJetPowerTest hT α k p r)
    (scalarTailJet_F_tendsto hT α hq) hA
    (fun _ => rescaledMassProfile α hT) (fun _ s => (α.property.1 (s/T)).2)
    (fun _ => 0) (fun n => Real.toNNReal (T*q n))
  have hl := ((scalarJetPowerTest hT α k p r).nonnegativeProfileTest_window_continuous
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0).tendsto
    (0,Real.toNNReal (T*r)) |>.comp
      (tendsto_const_nhds.prodMk_nhds
        (continuous_real_toNNReal.tendsto (T*r) |>.comp (hq.const_mul T)))
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarPlantedJetPower] using hh

theorem scalarPlantedJetPower_parameter_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (k p : ℕ) (q : ℝ) :
    Tendsto (fun n => scalarPlantedJetPower hT (α n) k p q) atTop
      (𝓝 (scalarPlantedJetPower hT β k p q)) := by
  have hb (γ : boundedMassProfiles) (y : Fin 1 → ℝ) :
      |scalarTailSpatialJet hT γ (k+1) q y| ≤ (ReplicaTree.attachmentCount 1 k:ℝ) :=
    scalarProfileJet_bound _ (fun s => (γ.property.1 (s/T)).2) _ _ k (y 0)
  have hA := tendstoUniformly_pow_of_abs_le (fun n => hb (α n)) (hb β)
    (scalarTailSpatialJet_parameter_tendsto hT hα q (k+1)) p
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun n => scalarJetPowerTest hT (α n) k p q) (scalarJetPowerTest hT β k p q)
    (scalarTailSpatialJet_parameter_tendsto hT hα q 0) hA
    (fun n => rescaledMassProfile (α n) hT) (fun n s => ((α n).property.1 (s/T)).2)
    (fun _ => 0) (fun _ => Real.toNNReal (T*q))
  have hl := (continuous_rescaledProfile_test (scalarJetPowerTest hT β k p q) hT 0
    (Real.toNNReal (T*q)) 0).tendsto β |>.comp hα
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarPlantedJetPower] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarClockProfileJet_zero_all (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {m : ℝ} (hm : 0 < m)
    (k : ℕ) (x : ℝ) :
    scalarClockProfileJet α hα l t m 0 k x=scalarProfileJet α l t k x := by
  induction k generalizing x with
  | zero => exact scalarClockProfileJet_zero_clock α hα l t hm x
  | succ k ih =>
    change deriv (fun y => scalarClockProfileJet α hα l t m 0 k y) x=
      scalarProfileJet α l t (k+1) x
    rw [show (fun y => scalarClockProfileJet α hα l t m 0 k y)=
      (fun y => scalarProfileJet α l t k y) from funext ih]
    exact (scalarProfileJet_hasDerivAt α hα l t k x).deriv

noncomputable def scalarCurvatureFlux {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) : ℝ :=
  scalarPlantedJetPower hT α 2 2 q-2*α.val q*scalarPlantedJetPower hT α 1 3 q

theorem scalarPrefixRootSecond_eq_flux {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hm : 0 < α.val q) :
    scalarPrefixRootSecond hT α q hm=scalarCurvatureFlux hT α q := by
  let J := scalarJetPowerTest hT α 2 2 q
  let D := scalarJetPowerTest hT α 1 3 q
  let K := D.withTest (fun y => 2*α.val q*D.A y) (((scalarTailSpatialJet_bddSmooth_all hT α 1 2 q).pow 3).const_mul (2*α.val q))
  let L := (scalarTailJet hT α q).withTest
    (scalarRootSecond (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) (α.val q) 0)
    (scalarRootSecond_bddSmooth (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) hm 0 2)
  have hA : L.A=fun y => J.A y-K.A y := by
    funext y
    change (scalarClockProfileJet (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q)))
        (α.val q) 0 3 (y 0))^2-2*α.val q*
      (scalarClockProfileJet (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q)))
        (α.val q) 0 2 (y 0))^3=
      (scalarTailSpatialJet hT α 3 q y)^2-2*α.val q*(scalarTailSpatialJet hT α 2 q y)^3
    exact congrArg₂ (fun a b : ℝ => a^2-2*α.val q*b^3)
      (scalarClockProfileJet_zero_all (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) hm 3 (y 0))
      (scalarClockProfileJet_zero_all (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) hm 2 (y 0))
  have hsub := J.nonnegativeProfileTest_sub K L rfl rfl hA
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal (T*q)) 0
  have hmul := D.nonnegativeProfileTest_affine K 0 (2*α.val q) rfl
    (by funext y; exact (zero_add _).symm)
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal (T*q)) 0
  simp only [hmul,zero_add] at hsub
  exact hsub

theorem scalarCurvatureFlux_intervalIntegrable {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (a b : ℝ) : IntervalIntegrable (scalarCurvatureFlux hT α) volume a b := by
  exact (scalarPlantedJetPower_continuous hT α 2 2).intervalIntegrable a b |>.sub
    (((α.property.2.intervalIntegrable (a:=a) (b:=b) (μ:=volume)).const_mul 2).mul_continuousOn
      (scalarPlantedJetPower_continuous hT α 1 3).continuousOn)

theorem scalarCurvatureFlux_parameter_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (q : ℝ) :
    Tendsto (fun n => scalarCurvatureFlux hT (α n) q) atTop (𝓝 (scalarCurvatureFlux hT β q)) := by
  have hv : Tendsto (fun n => (α n).val q) atTop (𝓝 (β.val q)) :=
    ((continuous_apply q).comp continuous_subtype_val).tendsto β |>.comp hα
  exact (scalarPlantedJetPower_parameter_tendsto hT hα 2 2 q).sub
    ((hv.const_mul 2).mul (scalarPlantedJetPower_parameter_tendsto hT hα 1 3 q))

theorem scalarCurvatureFlux_right_continuous {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) {q : ℝ} (hc : ContinuousWithinAt α.val (Ici q) q) :
    ContinuousWithinAt (scalarCurvatureFlux hT α) (Ici q) q :=
  (scalarPlantedJetPower_continuous hT α 2 2).continuousWithinAt.sub
    ((hc.const_mul 2).mul (scalarPlantedJetPower_continuous hT α 1 3).continuousWithinAt)

theorem scalarPlantedCurvature_derivative_flux_plateau {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hq : q ∈ Ioo p r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    HasDerivAt (scalarPlantedCurvature hT α) (T*scalarCurvatureFlux hT α q) q := by
  have hmq : 0 < α.val q := by rw [hf q hq]; exact hm
  rw [← scalarPrefixRootSecond_eq_flux hT α hmq]
  exact scalarPlantedCurvature_derivative_plateau hT hp hq hr α hm hm1 hf hmq

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedCurvature_grid_integral {T h : ℝ} (hT : 0 < T) (hh : 0 < h)
    (N : ℕ) (hN : (N:ℝ)*h ≤ 1) (α : boundedMassProfiles)
    (hcell : ∀ k < N, ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ x ∈ Ioo ((k:ℝ)*h) (((k:ℝ)+1)*h), α.val x=m) :
    scalarPlantedCurvature hT α ((N:ℝ)*h)-scalarPlantedCurvature hT α 0=
      T*∫ x in 0..(N:ℝ)*h, scalarCurvatureFlux hT α x := by
  let f := scalarPlantedCurvature hT α
  let g := fun x => T*scalarCurvatureFlux hT α x
  have hf : Continuous f := scalarPlantedCurvature_continuous hT α
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    (scalarCurvatureFlux_intervalIntegrable hT α a b).const_mul T
  have hi (k : ℕ) (hk : k < N) :
      ∫ x in (k:ℝ)*h..((k+1:ℕ):ℝ)*h, g x = f (((k+1:ℕ):ℝ)*h)-f ((k:ℝ)*h) := by
    obtain ⟨m,hm,hm1,hfla⟩ := hcell k hk
    have hkN : ((k:ℝ)+1)*h ≤ 1 := by
      have hc : (k:ℝ)+1 ≤ N := by exact_mod_cast hk
      exact (mul_le_mul_of_nonneg_right hc hh.le).trans hN
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    · push_cast
      nlinarith
    · exact hf.continuousOn
    · intro x hx
      simp only [Nat.cast_add,Nat.cast_one] at hx
      exact scalarPlantedCurvature_derivative_flux_plateau hT
        (mul_nonneg (Nat.cast_nonneg k) hh.le) hx hkN α hm hm1 hfla
    · exact hg _ _
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun k : ℕ => (k:ℝ)*h) (n:=N) (f:=g) (μ:=volume)
    (fun _ _ => hg _ _)
  have he : (∑ k ∈ Finset.range N, ∫ x in (k:ℝ)*h..((k+1:ℕ):ℝ)*h, g x)=
      ∑ k ∈ Finset.range N, (f (((k+1:ℕ):ℝ)*h)-f ((k:ℝ)*h)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hi k (Finset.mem_range.mp hk)
  rw [he,Finset.sum_range_sub (fun k : ℕ => f ((k:ℝ)*h)) N] at hs
  simpa only [Nat.cast_zero,zero_mul,intervalIntegral.integral_const_mul,f,g] using hs

theorem prefixGridProfile_curvature_integral {T q h ε : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hh : 0 < h)
    (hε : 0 < ε) (hεq : ε ≤ α.val q) (N : ℕ) (he : (N:ℝ)*h=q) :
    let β := prefixGridProfile α hq hh hε.le hεq
    scalarPlantedCurvature hT β q-scalarPlantedCurvature hT β 0=
      T*∫ x in 0..q, scalarCurvatureFlux hT β x := by
  let β := prefixGridProfile α hq hh hε.le hεq
  have hcell : ∀ k < N, ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ x ∈ Ioo ((k:ℝ)*h) (((k:ℝ)+1)*h), β.val x=m := by
    intro k hk
    have hkq : ((k:ℝ)+1)*h ≤ q := by
      rw [← he]
      apply mul_le_mul_of_nonneg_right _ hh.le
      exact_mod_cast hk
    refine ⟨max ε (α.val (((k:ℝ)+1)*h)),hε.trans_le (le_max_left _ _),?_,?_⟩
    · exact max_le (hεq.trans (α.property.1 q).2) (α.property.1 _).2
    · intro x hx
      exact prefixGridProfile_cell α hq hh hε.le hεq hkq hx
  have hi := scalarPlantedCurvature_grid_integral hT hh N (he.le.trans hq1) β hcell
  simpa only [he,β] using hi

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarCurvatureFlux_measurable {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Measurable (scalarCurvatureFlux hT α) :=
  (scalarPlantedJetPower_continuous hT α 2 2).measurable.sub
    ((measurable_const.mul α.property.2.measurable).mul
      (scalarPlantedJetPower_continuous hT α 1 3).measurable)

theorem scalarCurvatureFlux_abs_le {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) :
    |scalarCurvatureFlux hT α q| ≤
      (ReplicaTree.attachmentCount 1 2:ℝ)^2+2*(ReplicaTree.attachmentCount 1 1:ℝ)^3 := by
  have hB := scalarPlantedJetPower_abs_le hT α 2 2 q
  have hD := scalarPlantedJetPower_abs_le hT α 1 3 q
  have hm : |2*α.val q| ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (α.property.1 q).1)]
    linarith [(α.property.1 q).2]
  unfold scalarCurvatureFlux
  calc
    _ ≤ |scalarPlantedJetPower hT α 2 2 q|+
        |2*α.val q*scalarPlantedJetPower hT α 1 3 q| := by
      simpa only [Real.norm_eq_abs] using (norm_sub_le
        (scalarPlantedJetPower hT α 2 2 q) (2*α.val q*scalarPlantedJetPower hT α 1 3 q))
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add hB (mul_le_mul hm hD (abs_nonneg _) (by norm_num))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedCurvature_integral {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedCurvature hT α q-scalarPlantedCurvature hT α 0=
      T*∫ x in 0..q, scalarCurvatureFlux hT α x := by
  let h := fun N : ℕ => q/((N+1:ℕ):ℝ)
  let ε := fun N : ℕ => α.val q/((N+1:ℕ):ℝ)
  have hh (N) : 0 < h N := div_pos hq (by positivity)
  have hε (N) : 0 < ε N := div_pos hm (by positivity)
  have hεq (N) : ε N ≤ α.val q := by
    apply (div_le_iff₀ (show (0:ℝ) < ((N+1:ℕ):ℝ) by positivity)).mpr
    have hn : (1:ℝ) ≤ ((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith
  let β := fun N => prefixGridProfile α hq.le (hh N) (hε N).le (hεq N)
  have ht : Tendsto h atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat q).comp (tendsto_add_atTop_nat 1)
  have hεt : Tendsto ε atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (α.val q)).comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto β atTop (𝓝 α) :=
    prefixGridProfile_tendsto α hq.le hc hh (fun N => (hε N).le) hεq ht hεt
  have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F:=fun N x => scalarCurvatureFlux hT (β N) x)
    (f:=scalarCurvatureFlux hT α) (μ:=volume) (a:=0) (b:=q) (fun _ => (ReplicaTree.attachmentCount 1 2:ℝ)^2+2*(ReplicaTree.attachmentCount 1 1:ℝ)^3)
    (Eventually.of_forall (fun N => (scalarCurvatureFlux_measurable hT (β N)).aestronglyMeasurable))
    (Eventually.of_forall (fun N => Filter.Eventually.of_forall (fun x _ => by
      rw [Real.norm_eq_abs]
      exact scalarCurvatureFlux_abs_le hT (β N) x)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun x _ => scalarCurvatureFlux_parameter_tendsto hT hb x))
  have he (N) : scalarPlantedCurvature hT (β N) q-scalarPlantedCurvature hT (β N) 0=
      T*∫ x in 0..q, scalarCurvatureFlux hT (β N) x :=
    prefixGridProfile_curvature_integral hT α hq.le hq1 (hh N) (hε N) (hεq N) (N+1)
      (by dsimp only [h]; field_simp)
  have hl := (scalarPlantedCurvature_parameter_tendsto hT hb q).sub
    (scalarPlantedCurvature_parameter_tendsto hT hb 0)
  have hr := hi.const_mul T
  simp_rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem scalarPlantedCurvature_right_derivative {T p q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hp : 0 ≤ p) (hpq : p < q) (hq1 : q < 1)
    (hm : 0 < α.val p)
    (hc : ∀ x ∈ Ico (0:ℝ) 1, ContinuousWithinAt α.val (Ici x) x) :
    HasDerivWithinAt (scalarPlantedCurvature hT α) (T*scalarCurvatureFlux hT α q) (Ici q) q := by
  have hmF := (scalarCurvatureFlux_measurable hT α).stronglyMeasurable
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (s:=Ici q) (t:=Ioi q) (scalarCurvatureFlux_intervalIntegrable hT α 0 q)
    hmF.stronglyMeasurableAtFilter
    ((scalarCurvatureFlux_right_continuous hT α (hc q ⟨hp.trans hpq.le,hq1⟩)).mono Ioi_subset_Ici_self)
  have hh := (hd.const_mul T).add_const (scalarPlantedCurvature hT α 0)
  have he (r : ℝ) (hr : r ∈ Ioo p 1) : scalarPlantedCurvature hT α r=
      T*(∫ x in 0..r, scalarCurvatureFlux hT α x)+scalarPlantedCurvature hT α 0 := by
    have hi := scalarPlantedCurvature_integral hT α (hp.trans_lt hr.1) hr.2.le
      (hm.trans_le (α.property.2 hr.1.le)) (fun x hx => hc x ⟨hx.1,hx.2.trans hr.2⟩)
    linarith
  apply hh.congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioo_mem_nhds hpq hq1)] with r hr
    exact he r hr
  · exact he q ⟨hpq,hq1⟩

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedEnergy_grid_integral {T h : ℝ} (hT : 0 < T) (hh : 0 < h)
    (N : ℕ) (hN : (N:ℝ)*h ≤ 1) (α : boundedMassProfiles)
    (hcell : ∀ k < N, ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ x ∈ Ioo ((k:ℝ)*h) (((k:ℝ)+1)*h), α.val x=m) :
    scalarPlantedEnergy hT α ((N:ℝ)*h)-scalarPlantedEnergy hT α 0=
      T*∫ x in 0..(N:ℝ)*h, scalarPlantedCurvature hT α x := by
  let f := scalarPlantedEnergy hT α
  let g := fun x => T*scalarPlantedCurvature hT α x
  have hf : Continuous f := scalarPlantedEnergy_continuous hT α
  have hg : Continuous g := continuous_const.mul (scalarPlantedCurvature_continuous hT α)
  have hi (k : ℕ) (hk : k < N) :
      ∫ x in (k:ℝ)*h..((k+1:ℕ):ℝ)*h, g x = f (((k+1:ℕ):ℝ)*h)-f ((k:ℝ)*h) := by
    obtain ⟨m,hm,hm1,hfla⟩ := hcell k hk
    have hkN : ((k:ℝ)+1)*h ≤ 1 := by
      have hc : (k:ℝ)+1 ≤ N := by exact_mod_cast hk
      exact (mul_le_mul_of_nonneg_right hc hh.le).trans hN
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    · push_cast
      nlinarith
    · exact hf.continuousOn
    · intro x hx
      simp only [Nat.cast_add,Nat.cast_one] at hx
      exact scalarPlantedEnergy_derivative_plateau hT
        (mul_nonneg (Nat.cast_nonneg k) hh.le) hx hkN α hm hm1 hfla
    · exact hg.intervalIntegrable _ _
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun k : ℕ => (k:ℝ)*h) (n:=N) (f:=g) (μ:=volume)
    (fun _ _ => hg.intervalIntegrable _ _)
  have he : (∑ k ∈ Finset.range N, ∫ x in (k:ℝ)*h..((k+1:ℕ):ℝ)*h, g x)=
      ∑ k ∈ Finset.range N, (f (((k+1:ℕ):ℝ)*h)-f ((k:ℝ)*h)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hi k (Finset.mem_range.mp hk)
  rw [he,Finset.sum_range_sub (fun k : ℕ => f ((k:ℝ)*h)) N] at hs
  simpa only [Nat.cast_zero,zero_mul,intervalIntegral.integral_const_mul,f,g] using hs

theorem prefixGridProfile_energy_integral {T q h ε : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hh : 0 < h)
    (hε : 0 < ε) (hεq : ε ≤ α.val q) (N : ℕ) (he : (N:ℝ)*h=q) :
    let β := prefixGridProfile α hq hh hε.le hεq
    scalarPlantedEnergy hT β q-scalarPlantedEnergy hT β 0=
      T*∫ x in 0..q, scalarPlantedCurvature hT β x := by
  let β := prefixGridProfile α hq hh hε.le hεq
  have hcell : ∀ k < N, ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ x ∈ Ioo ((k:ℝ)*h) (((k:ℝ)+1)*h), β.val x=m := by
    intro k hk
    have hkq : ((k:ℝ)+1)*h ≤ q := by
      rw [← he]
      apply mul_le_mul_of_nonneg_right _ hh.le
      exact_mod_cast hk
    refine ⟨max ε (α.val (((k:ℝ)+1)*h)),hε.trans_le (le_max_left _ _),?_,?_⟩
    · exact max_le (hεq.trans (α.property.1 q).2) (α.property.1 _).2
    · intro x hx
      exact prefixGridProfile_cell α hq hh hε.le hεq hkq hx
  have hi := scalarPlantedEnergy_grid_integral hT hh N (he.le.trans hq1) β hcell
  simpa only [he,β] using hi

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedEnergy_integral {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedEnergy hT α q-scalarPlantedEnergy hT α 0=
      T*∫ x in 0..q, scalarPlantedCurvature hT α x := by
  let h := fun N : ℕ => q/((N+1:ℕ):ℝ)
  let ε := fun N : ℕ => α.val q/((N+1:ℕ):ℝ)
  have hh (N) : 0 < h N := div_pos hq (by positivity)
  have hε (N) : 0 < ε N := div_pos hm (by positivity)
  have hεq (N) : ε N ≤ α.val q := by
    apply (div_le_iff₀ (show (0:ℝ) < ((N+1:ℕ):ℝ) by positivity)).mpr
    have hn : (1:ℝ) ≤ ((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith
  let β := fun N => prefixGridProfile α hq.le (hh N) (hε N).le (hεq N)
  have ht : Tendsto h atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat q).comp (tendsto_add_atTop_nat 1)
  have hεt : Tendsto ε atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (α.val q)).comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto β atTop (𝓝 α) :=
    prefixGridProfile_tendsto α hq.le hc hh (fun N => (hε N).le) hεq ht hεt
  have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F:=fun N x => scalarPlantedCurvature hT (β N) x)
    (f:=scalarPlantedCurvature hT α) (μ:=volume) (a:=0) (b:=q) (fun _ => (1:ℝ))
    (Eventually.of_forall (fun N => (scalarPlantedCurvature_continuous hT (β N)).aestronglyMeasurable))
    (Eventually.of_forall (fun N => Filter.Eventually.of_forall (fun x _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedCurvature_bounds hT (β N) x).1]
      exact (scalarPlantedCurvature_bounds hT (β N) x).2)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun x _ => scalarPlantedCurvature_parameter_tendsto hT hb x))
  have he (N) : scalarPlantedEnergy hT (β N) q-scalarPlantedEnergy hT (β N) 0=
      T*∫ x in 0..q, scalarPlantedCurvature hT (β N) x :=
    prefixGridProfile_energy_integral hT α hq.le hq1 (hh N) (hε N) (hεq N) (N+1)
      (by dsimp only [h]; field_simp)
  have hl := (scalarPlantedEnergy_parameter_tendsto hT hb q).sub
    (scalarPlantedEnergy_parameter_tendsto hT hb 0)
  have hr := hi.const_mul T
  simp_rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem scalarPlantedEnergy_derivative {T p q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hp : 0 ≤ p) (hpq : p < q) (hq1 : q < 1)
    (hm : 0 < α.val p)
    (hc : ∀ x ∈ Ico (0:ℝ) 1, ContinuousWithinAt α.val (Ici x) x) :
    HasDerivAt (scalarPlantedEnergy hT α) (T*scalarPlantedCurvature hT α q) q := by
  have hC := scalarPlantedCurvature_continuous hT α
  have hd := intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable 0 q)
    hC.stronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  have hh := (hd.const_mul T).add_const (scalarPlantedEnergy hT α 0)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hpq hq1] with r hr
  have hi := scalarPlantedEnergy_integral hT α (hp.trans_lt hr.1) hr.2.le
    (hm.trans_le (α.property.2 hr.1.le)) (fun x hx => hc x ⟨hx.1,hx.2.trans hr.2⟩)
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarPrefixTest_pos {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    (A : (Fin 1 → ℝ) → ℝ) (hA : BddSmooth 2 A) (hpos : ∀ y, 0 < A y) :
    0 < ((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest
      (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0 := by
  obtain ⟨R,hv,_hR,hg,hn,ht⟩ := scalarPrefixResidualApproximation hT α hq hq1 hm hc
  let F := fun y => (scalarTailJet hT α q).F (fun _ => y)
  have hF : LipschitzWith 1 F := scalar_restrict_lipschitz (scalarTailJet hT α q).lipschitz
  let W := fun x => gaussianLinearEnvelope (T*q) (-2) x/gaussianLinearEnvelopeMass (T*q) 2
  have hs : 0 < T*q := mul_pos hT hq
  have hW (x : ℝ) : 0 < W x := div_pos
    (mul_pos (realGaussianKernel_pos hs x) (Real.exp_pos _)) (gaussianLinearEnvelopeMass_pos hs 2)
  have hiW : Integrable W := (gaussianLinearEnvelope_integrable hs (-2)).div_const _
  have hAc : Continuous (fun x : ℝ => A (fun _ => x)) :=
    hA.continuous.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨B,_hB,hB⟩ := hA.bound
  have hi : Integrable (fun x => W x*A (fun _ => x)) :=
    hiW.mul_bdd hAc.aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hB (fun _ => x))
  have hp : 0 < ∫ x, W x*A (fun _ => x) := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (mul_pos (hW x) (hpos _)).le) hi).mpr
    have he : Function.support (fun x => W x*A (fun _ => x))=univ := by
      ext x
      simp only [Function.mem_support,mem_univ,iff_true]
      exact (mul_pos (hW x) (hpos _)).ne'
    rw [he]
    simp
  apply hp.trans_le
  apply ge_of_tendsto (ht A hA)
  apply Eventually.of_forall
  intro N
  have hiN : Integrable (fun x => (R N).plantedDensity F (α.val q) x*A (fun _ => x)) :=
    ((R N).plantedDensity_integrable hF (α.val q)).mul_bdd hAc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (fun _ => x))
  apply integral_mono hi hiN
  intro x
  have hl := ((R N).plantedDensity_envelope (hg N) hF
    (by simpa only [abs_of_pos hm] using (α.property.1 q).2) (hn N) x).1
  rw [hv N] at hl
  exact mul_le_mul_of_nonneg_right hl (hpos _).le

theorem scalarPlantedEnergy_lt_one {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedEnergy hT α q < 1 := by
  let J := scalarTailJet hT α q
  let K := J.withTest (fun y => 1-(J.G 0 y)^2) ((BddSmooth.const 2 1).sub ((scalarTailJet_G_smooth hT α q 2 0).pow 2))
  have hp : 0 < K.nonnegativeProfileTest (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0 := by
    apply scalarPrefixTest_pos hT α hq hq1 hm hc
    intro y
    have hbound := scalarProfileJet_admissible (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) (y 0)
    have hstrict := scalarProfileJet_curvature_pos (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) (y 0)
    change 0 < 1-(scalarProfileJet (rescaledMassProfile α hT) (T*q)
      (Real.toNNReal (T*(1-q))) 1 (y 0))^2
    linarith [hbound.2]
  have he := J.square.nonnegativeProfileTest_affine K 1 (-1) rfl
    (by funext y; change 1-(J.G 0 y)^2=1+ -1*(J.G 0 y)^2; ring)
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal (T*q)) 0
  rw [he] at hp
  change 0 < 1+ -1*scalarPlantedEnergy hT α q at hp
  linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarPrefix_error (J : HeatJet 0) (hJ : ∀ i x, |J.G i x| ≤ 1)
    {T q p d : ℝ} (hT : 0 < T) (hq : 0 ≤ q) (hqp : q ≤ p)
    (α β : boundedMassProfiles) (he : ∀ s ∈ Ioo (0:ℝ) q, β.val s=α.val s)
    (hb : ∀ s ∈ Ioo q p, |β.val s-α.val s| ≤ d) (x : Fin 1 → ℝ) :
    |J.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (Real.toNNReal (T*p)) x-
      J.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) x| ≤
      T/2*d*(p-q) := by
  let f := fun s => |β.val (s/T)-α.val (s/T)|
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    ((rescaledMassProfile β hT).monotone.intervalIntegrable.sub
      (rescaledMassProfile α hT).monotone.intervalIntegrable).abs
  have hfirst : (∫ s in (0:ℝ)..T*q, f s)=0 := by
    trans ∫ _s in (0:ℝ)..T*q, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le (mul_nonneg hT.le hq)
      intro s hs
      dsimp [f]
      rw [he (s/T) ⟨div_pos hs.1 hT,(div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩,
        sub_self,abs_zero]
    · simp
  have hlast : (∫ s in T*q..T*p, f s) ≤ T*d*(p-q) := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume)
      (mul_le_mul_of_nonneg_left hqp hT.le) (hfi _ _) (intervalIntegrable_const (c:=d)) (by
        intro s hs
        exact hb (s/T) ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hs.1]),
          (div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hh
    nlinarith
  have hi : (∫ s in (0:ℝ)..T*p, f s) ≤ T*d*(p-q) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 (T*q)) (hfi (T*q) (T*p)),
      hfirst,zero_add]
    exact hlast
  have hh := J.nonnegativeProfileValue_L1_comparison (fun _ => 1) hJ
    (rescaledMassProfile β hT) (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) x
  norm_num only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Nat.reduceAdd,nsmul_eq_mul,Nat.cast_one,one_mul,
    Real.coe_toNNReal _ (mul_nonneg hT.le (hq.trans hqp)),zero_add] at hh
  change |_ - _| ≤ (1:ℝ)/2*(∫ s in (0:ℝ)..T*p, f s) at hh
  linarith

 theorem scalarPenalty_prefix_error {q p r a d : ℝ} (hq : 0 ≤ q)
    (hqp : q ≤ p) (hpr : p ≤ r) (hr : r ≤ 1) (α β : boundedMassProfiles)
    (hz : ∀ s ∈ Ioo (0:ℝ) q, β.val s=α.val s)
    (hb : ∀ s ∈ Ioo q p, |β.val s-α.val s| ≤ d)
    (hf : ∀ s ∈ Ioo p r, β.val s=a)
    (he : ∀ s ∈ Ioo r 1, β.val s=α.val s) :
    |scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a))| ≤ d*(p-q) := by
  let f := fun s => weightedProfile β s-weightedProfile α s
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    (weightedProfile_monotone β).intervalIntegrable.sub (weightedProfile_monotone α).intervalIntegrable
  have hzero : (∫ s in (0:ℝ)..q, f s)=0 := by
    trans ∫ _s in (0:ℝ)..q, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hq
      intro s hs
      dsimp only [f,weightedProfile]
      rw [hz s hs,sub_self]
    · simp
  have hlast : (∫ s in r..1, f s)=0 := by
    trans ∫ _s in r..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hr
      intro s hs
      dsimp only [f,weightedProfile]
      rw [he s hs,sub_self]
    · simp
  have hflat : (∫ s in p..r, f s)= -(∫ s in p..r, s*(α.val s-a)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le hpr
    intro s hs
    dsimp only [f,weightedProfile]
    rw [hf s hs,max_eq_left (hq.trans (hqp.trans hs.1.le))]
    ring
  have hmid : |∫ s in q..p, f s| ≤ d*(p-q) := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) hqp (hfi _ _).abs
      (intervalIntegrable_const (c:=d)) (by
        intro s hs
        change |max s 0*β.val s-max s 0*α.val s| ≤ d
        have hs0 : 0 ≤ s := hq.trans hs.1.le
        rw [← mul_sub,max_eq_left hs0,abs_mul,abs_of_nonneg hs0]
        have hd : 0 ≤ d := (abs_nonneg _).trans (hb s hs)
        calc
          s*|β.val s-α.val s| ≤ s*d := mul_le_mul_of_nonneg_left (hb s hs) hs0
          _ ≤ d := by nlinarith [hs.2.le.trans (hpr.trans hr)])
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hh
    exact (intervalIntegral.abs_integral_le_integral_abs hqp).trans (by nlinarith)
  have heq : scalarPenalty β-scalarPenalty α=
      (∫ s in q..p, f s)-(∫ s in p..r, s*(α.val s-a)) := by
    unfold scalarPenalty
    rw [← intervalIntegral.integral_sub (weightedProfile_monotone β).intervalIntegrable
      (weightedProfile_monotone α).intervalIntegrable]
    change (∫ s in (0:ℝ)..1, f s)=_
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 q) (hfi q 1),hzero,zero_add,
      ← intervalIntegral.integral_add_adjacent_intervals (hfi q p) (hfi p 1),
      ← intervalIntegral.integral_add_adjacent_intervals (hfi p r) (hfi r 1),hflat,hlast,add_zero]
    ring
  have hh : scalarPenalty β-(scalarPenalty α-∫ u in p..r, u*(α.val u-a))=
      ∫ s in q..p, f s := by linarith
  rw [hh]
  exact hmid

end SKFluctuations.Hierarchy

end

end OAI
