import Mathlib
import OAI.Probability.Ballisticity.Estimates.SharedConditionedPairLawFst

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

namespace DirectionalTransience

noncomputable def noDropQuenchedKernel {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    Kernel (Environment d) (Path d) where
  toFun ω := (noDropQuenched ℓ x ω)⁻¹ • (quenchedKernel (ω,x)).restrict (NoDrop ℓ x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
    exact (measurable_noDropQuenched ℓ x).inv.mul
      (((fixedQuenchedKernel x).measurable_coe (hA.inter (measurableSet_noDrop ℓ x))))

lemma noDropQuenchedKernel_apply {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (A : Set (Path d)) (hA : MeasurableSet A) :
    noDropQuenchedKernel ℓ x ω A = (noDropQuenched ℓ x ω)⁻¹ *
      quenchedKernel (ω,x) (A ∩ NoDrop ℓ x) := by
  exact (Measure.smul_apply _ _ _).trans (by rw [Measure.restrict_apply hA]; rfl)

lemma noDropQuenched_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : noDropQuenched ℓ x ω ≤ 1 := prob_le_one

lemma noDropQuenched_ne_top {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : noDropQuenched ℓ x ω ≠ ⊤ := measure_ne_top _ _

instance noDropQuenchedKernel_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    IsFiniteKernel (noDropQuenchedKernel ℓ x) where
  exists_univ_le := by
    refine ⟨1, by simp, fun ω => ?_⟩
    rw [noDropQuenchedKernel_apply _ _ _ _ MeasurableSet.univ, Set.univ_inter]
    change (noDropQuenched ℓ x ω)⁻¹ * noDropQuenched ℓ x ω ≤ 1
    exact ENNReal.inv_mul_le_one _

lemma noDropQuenchedKernel_probability {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (hq : noDropQuenched ℓ x ω ≠ 0) :
    IsProbabilityMeasure (noDropQuenchedKernel ℓ x ω) := by
  constructor
  rw [noDropQuenchedKernel_apply _ _ _ _ MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel hq (noDropQuenched_ne_top ℓ x ω)

noncomputable def quenchedNoDropTest {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (F : Path d → ℝ) (ω : Environment d) : ℝ :=
  ∫ X, F X ∂noDropQuenchedKernel ℓ x ω

lemma measurable_quenchedNoDropTest {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (F : Path d → ℝ) (hF : Measurable F) : Measurable (quenchedNoDropTest ℓ x F) :=
  hF.stronglyMeasurable.integral_kernel.measurable

lemma noDrop_mass_smul_kernel {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : noDropQuenched ℓ x ω • noDropQuenchedKernel ℓ x ω =
      (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) := by
  change noDropQuenched ℓ x ω • ((noDropQuenched ℓ x ω)⁻¹ •
    (quenchedKernel (ω,x)).restrict (NoDrop ℓ x)) = _
  by_cases hq : noDropQuenched ℓ x ω = 0
  · rw [hq, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hq).symm
  · rw [smul_smul, ENNReal.mul_inv_cancel hq (noDropQuenched_ne_top ℓ x ω), one_smul]

lemma noDrop_pair_mass_smul_kernel {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (ω : Environment d) :
    (noDropQuenched ℓ x ω * noDropQuenched ℓ y ω) •
      ((noDropQuenchedKernel ℓ x).prod (noDropQuenchedKernel ℓ y)) ω =
        (sharedPairKernel x y ω).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y) := by
  rw [Kernel.prod_apply]
  calc
    _ = (noDropQuenched ℓ x ω • noDropQuenchedKernel ℓ x ω).prod
        (noDropQuenched ℓ y ω • noDropQuenchedKernel ℓ y ω) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = _ := by
      rw [noDrop_mass_smul_kernel, noDrop_mass_smul_kernel, Measure.prod_restrict,
        sharedPairKernel, Kernel.prod_apply]
      rfl

noncomputable def noDropPairEnvironment {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : Measure (Environment d) :=
  (sharedNoDropMass ν ℓ x y)⁻¹ • (environmentLaw ν).withDensity
    (fun ω => noDropQuenched ℓ x ω * noDropQuenched ℓ y ω)

lemma noDropPairEnvironment_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (hp : sharedNoDropMass ν ℓ x y ≠ 0) :
    IsProbabilityMeasure (noDropPairEnvironment ν ℓ x y) := by
  constructor
  rw [noDropPairEnvironment, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (ne_of_lt ((sharedNoDropMass_le_one ν ℓ x y).trans_lt (by simp)))

lemma noDrop_pair_disintegration {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) :
    ((noDropQuenchedKernel ℓ x).prod (noDropQuenchedKernel ℓ y)) ∘ₘ
      noDropPairEnvironment ν ℓ x y = sharedConditionedPairLaw ν ℓ x y := by
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), noDropPairEnvironment,
    lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul (environmentLaw ν)
      (show Measurable (fun ω => noDropQuenched ℓ x ω * noDropQuenched ℓ y ω) from
        (measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y))
      (((noDropQuenchedKernel ℓ x).prod (noDropQuenchedKernel ℓ y)).measurable_coe hA),
    sharedConditionedPairLaw, Measure.smul_apply,
    Measure.restrict_apply hA, sharedPairLaw,
    Measure.bind_apply (hA.inter ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y)))
      (Kernel.aemeasurable _)]
  congr 1
  apply lintegral_congr
  intro ω
  have hm := congrArg (fun μ : Measure (Path d × Path d) => μ A)
    (noDrop_pair_mass_smul_kernel ℓ x y ω)
  simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
    Pi.mul_apply] using hm

lemma noDropPairEnvironment_ae_positive {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : ∀ᵐ ω ∂noDropPairEnvironment ν ℓ x y,
      noDropQuenched ℓ x ω ≠ 0 ∧ noDropQuenched ℓ y ω ≠ 0 := by
  apply Measure.smul_absolutelyContinuous.ae_le
  apply (ae_withDensity_iff
    (show Measurable (fun ω => noDropQuenched ℓ x ω * noDropQuenched ℓ y ω) from
      (measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y))).mpr
  exact ae_of_all _ fun ω h => ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

lemma integral_kernel_average {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) (κ : Kernel Ω S) (F : S → ℝ)
    (hF : Integrable F (κ ∘ₘ μ)) :
    ∫ z, F z ∂κ ∘ₘ μ = ∫ ω, ∫ z, F z ∂κ ω ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hF ⊢
  exact Kernel.integral_comp hF

lemma noDrop_pair_test_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (hp : sharedNoDropMass ν ℓ x y ≠ 0)
    (F G : Path d → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ X, ‖F X‖ ≤ CF) (hGb : ∀ X, ‖G X‖ ≤ CG) :
    ∫ ω, quenchedNoDropTest ℓ x F ω * quenchedNoDropTest ℓ y G ω
      ∂noDropPairEnvironment ν ℓ x y =
    ∫ P, F P.1 * G P.2 ∂sharedConditionedPairLaw ν ℓ x y := by
  let := sharedConditionedPairLaw_probability ν ℓ x y hp
  have hFG : Integrable (fun P : Path d × Path d => F P.1 * G P.2)
      (sharedConditionedPairLaw ν ℓ x y) := by
    apply Integrable.of_bound ((hF.comp measurable_fst).mul
      (hG.comp measurable_snd)).aestronglyMeasurable (CF*CG)
    exact ae_of_all _ fun P => by
      change ‖F P.1 * G P.2‖ ≤ CF*CG
      rw [norm_mul]
      exact mul_le_mul (hFb P.1) (hGb P.2) (norm_nonneg _) ((norm_nonneg _).trans (hFb P.1))
  rw [← noDrop_pair_disintegration ν ℓ x y] at hFG ⊢
  rw [integral_kernel_average _ _ _ hFG]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [Kernel.prod_apply, integral_prod_mul]
    rfl

lemma noDrop_pair_test_first_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (hp : sharedNoDropMass ν ℓ x y ≠ 0)
    (F : Path d → ℝ) (hF : Measurable F) (C : ℝ) (hFb : ∀ X, ‖F X‖ ≤ C) :
    ∫ ω, quenchedNoDropTest ℓ x F ω ∂noDropPairEnvironment ν ℓ x y =
    ∫ P, F P.1 ∂sharedConditionedPairLaw ν ℓ x y := by
  have h := noDrop_pair_test_moment ν ℓ x y hp F (fun _ => 1) hF measurable_const
    C 1 hFb (fun _ => by simp)
  simp only [mul_one] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [noDropPairEnvironment_ae_positive ν ℓ x y] with ω hω
  let := noDropQuenchedKernel_probability ℓ y ω hω.2
  simp [quenchedNoDropTest]

lemma noDrop_pair_test_second_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (hp : sharedNoDropMass ν ℓ x x ≠ 0)
    (F : Path d → ℝ) (hF : Measurable F) (C : ℝ) (hFb : ∀ X, ‖F X‖ ≤ C) :
    ∫ ω, (quenchedNoDropTest ℓ x F ω)^2 ∂noDropPairEnvironment ν ℓ x x =
    ∫ P, F P.1 * F P.2 ∂sharedConditionedPairLaw ν ℓ x x := by
  simpa only [pow_two] using noDrop_pair_test_moment ν ℓ x x hp F F hF hF C C hFb hFb

noncomputable def medianFirstHitPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (x : Lattice d)
    (r n T : ℝ) (X : Path d) : C(unitInterval,ℝ) :=
  heightPolygon (fun h => signedCoordinate f
    (recordIndexPosition ℓ h (fun j => X j-x))-(recordMedian ν ℓ hp f h:ℝ)) r n T

lemma measurable_medianFirstHitPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (x : Lattice d)
    (r n T : ℝ) : Measurable (medianFirstHitPath ν ℓ hp f x r n T) := by
  apply measurable_heightPolygon
  intro h
  exact (((measurable_of_countable (signedCoordinate f)).comp
    (measurable_recordIndexPosition ℓ h)).comp (by fun_prop)).sub_const _

noncomputable def quenchedMedianPathTest {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (x : Lattice d)
    (r n T : ℝ) (F : C(unitInterval,ℝ) →ᵇ ℝ) : Environment d → ℝ :=
  quenchedNoDropTest ℓ x (fun X => F (medianFirstHitPath ν ℓ hp f x r n T X))

lemma measurable_quenchedMedianPathTest {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (x : Lattice d)
    (r n T : ℝ) (F : C(unitInterval,ℝ) →ᵇ ℝ) :
    Measurable (quenchedMedianPathTest ν ℓ hp f x r n T F) :=
  measurable_quenchedNoDropTest _ _ _ (F.continuous.measurable.comp
    (measurable_medianFirstHitPath ν ℓ hp f x r n T))

lemma quenchedMedianPathTest_moments {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d)
    (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ)
    (f : Direction d) (x : Lattice d) (r n T : ℝ) (F : C(unitInterval,ℝ) →ᵇ ℝ) :
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let pathMap := medianFirstHitPath ν ℓ hp f x r n T
    let M := quenchedMedianPathTest ν ℓ hp f x r n T F
    (∫ ω, M ω ∂noDropPairEnvironment ν ℓ x x) =
      ∫ P, F (pathMap P.1) ∂sharedConditionedPairLaw ν ℓ x x ∧
    (∫ ω, (M ω)^2 ∂noDropPairEnvironment ν ℓ x x) =
      ∫ P, F (pathMap P.1) * F (pathMap P.2) ∂sharedConditionedPairLaw ν ℓ x x := by
  dsimp only
  have hpos := ne_of_gt (sharedNoDropMass_pos ν hue ℓ hℓ htrans x x)
  have hf := F.continuous.measurable.comp (measurable_medianFirstHitPath ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) f x r n T)
  exact ⟨noDrop_pair_test_first_moment ν ℓ x x hpos _ hf ‖F‖ (fun _ => F.norm_coe_le_norm _),
    noDrop_pair_test_second_moment ν ℓ x hpos _ hf ‖F‖ (fun _ => F.norm_coe_le_norm _)⟩

end DirectionalTransience

end

end

end OAI
