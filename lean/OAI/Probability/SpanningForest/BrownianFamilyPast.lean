import OAI.Probability.SpanningForest.BrownianBridge

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.BrownianFamilyPast

variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : I → ℝ≥0 → Ω → ℝ}

theorem indepFun_shift_past
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) (u : ℝ≥0) :
    IndepFun
      (fun ω (p : I × ℝ≥0) => B p.1 (u + p.2) ω - B p.1 u ω)
      (fun ω (p : I × Set.Iic u) => B p.1 p.2 ω) P := by
  classical
  have hG := BrownianBridge.isGaussianProcess_independent_family
    (fun i => (hB i).isGaussianProcess) hI
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hG.of_isGaussianProcess
    rintro (⟨i, t⟩ | ⟨i, ⟨t, ht⟩⟩)
    · exact ⟨{(i, u), (i, u + t)},
        { toFun x := x ⟨(i, u + t), by simp⟩ - x ⟨(i, u), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(i, t)},
        { toFun x := x ⟨(i, t), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p
    exact ((hB p.1).aemeasurable _).sub ((hB p.1).aemeasurable _)
  · intro p
    exact (hB p.1).aemeasurable _
  · rintro ⟨i, t⟩ ⟨j, s⟩
    have hf := (hB i).isGaussianProcess.hasGaussianLaw_sub
      (s := u + t) (t := u)
    have hg := (hB j).isGaussianProcess.hasGaussianLaw_eval (s : ℝ≥0)
    apply IndepFun.covariance_eq_zero _ hf.memLp_two hg.memLp_two
    by_cases hij : i = j
    · subst j
      exact ((hB i).indepFun_shift u).comp
        (measurable_pi_apply t) (measurable_pi_apply s)
    · exact (hI.indepFun hij).comp
        (show Measurable (fun f : ℝ≥0 → ℝ => f (u + t) - f u) by fun_prop)
        (measurable_pi_apply (s : ℝ≥0))

theorem indepFun_shift_hidden_past {A : Type*} [MeasurableSpace A]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → A} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P) (u : ℝ≥0) :
    IndepFun
      (fun ω (p : I × ℝ≥0) => B p.1 (u + p.2) ω - B p.1 u ω)
      (fun ω => (X ω, fun p : I × Set.Iic u => B p.1 p.2 ω)) P := by
  have : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hpair : IndepFun X
      (fun ω =>
        ((fun p : I × ℝ≥0 => B p.1 (u + p.2) ω - B p.1 u ω),
          fun p : I × Set.Iic u => B p.1 p.2 ω)) P := by
    exact hXB.comp measurable_id
      (show Measurable (fun f : I → ℝ≥0 → ℝ =>
        ((fun p : I × ℝ≥0 => f p.1 (u + p.2) - f p.1 u),
          fun p : I × Set.Iic u => f p.1 p.2)) by fun_prop)
  exact BrownianBridge.indepFun_regroup hX (by fun_prop) (by fun_prop)
    hpair (indepFun_shift_past hB hI u)

theorem indepFun_shift_hidden_observation
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P) (u : ℝ≥0) :
    IndepFun
      (fun ω (p : I × ℝ≥0) => B p.1 (u + p.2) ω - B p.1 u ω)
      (fun ω => (X ω, fun p : I × Set.Iic u =>
        (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω)) P := by
  exact (indepFun_shift_hidden_past hB hBm hI hX hXB u).comp measurable_id
    (show Measurable (fun q : (I → ℝ) × (I × Set.Iic u → ℝ) =>
      (q.1, fun p : I × Set.Iic u => (p.2 : ℝ≥0) * q.1 p.1 + q.2 p)) by fun_prop)

theorem indepFun_weighted_increment_observation
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    IndepFun (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω))
      (fun ω (p : I × Set.Iic u) =>
        (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) P := by
  exact (indepFun_shift_hidden_observation hB hBm hI hX hXB u).comp
    (show Measurable (fun f : I × ℝ≥0 → ℝ => ∑ i ∈ S, θ i * f (i, h)) by fun_prop)
    measurable_snd

theorem integral_weighted_increment_eq_zero
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    (∫ ω, ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω) ∂P) = 0 := by
  have hi (i : I) : Integrable (fun ω => θ i * (B i (u + h) ω - B i u ω)) P :=
    (((hB i).integrable_eval (u + h)).sub ((hB i).integrable_eval u)).const_mul (θ i)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_const_mul, integral_sub ((hB i).integrable_eval _)
    ((hB i).integrable_eval _), (hB i).integral_eval, (hB i).integral_eval]
  simp

theorem condExp_weighted_increment_observation_eq_zero
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    P[(fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) |
      MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
        (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hQ : Measurable (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) := by
    fun_prop
  have hH : Measurable (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) := by fun_prop
  have hc := condExp_indep_eq hQ.comap_le hH.comap_le
    (comap_measurable _).stronglyMeasurable
    (indepFun_weighted_increment_observation hB hBm hI hX hXB S θ u h)
  simpa only [integral_weighted_increment_eq_zero hB S θ u h] using hc

theorem setIntegral_weighted_increment_observation_eq_zero
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance] A) :
    (∫ ω in A, ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω) ∂P) = 0 := by
  have : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hH : Measurable (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) := by fun_prop
  have hQ : Integrable (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) P := by
    apply integrable_finsetSum
    intro i hi
    exact (((hB i).integrable_eval (u + h)).sub ((hB i).integrable_eval u)).const_mul _
  rw [← setIntegral_condExp hH.comap_le hQ hA]
  exact integral_eq_zero_of_ae (ae_restrict_of_ae
    (condExp_weighted_increment_observation_eq_zero hB hBm hI hX hXB S θ u h))

end Problem336.BrownianFamilyPast

end

end OAI
