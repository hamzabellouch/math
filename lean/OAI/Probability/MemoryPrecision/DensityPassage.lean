import Mathlib
import OAI.Probability.GaussianRegression.Main

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

section FiberSmoothing
variable {Ω Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (γ : Measure Ω) (τ : Measure Y) [SigmaFinite τ]

def fiberSmoothing (F : Ω × Y → ℝ≥0∞) (ρ : Y → ℝ≥0∞) (z : Ω × Y) : ℝ≥0∞ :=
  ∫⁻ b, ρ (z.2 - b) * F (z.1, b) ∂τ

@[fun_prop] lemma measurable_fiberSmoothing {F : Ω × Y → ℝ≥0∞} {ρ : Y → ℝ≥0∞}
    (hF : Measurable F) (hρ : Measurable ρ) :
    Measurable (fiberSmoothing τ F ρ) := by
  unfold fiberSmoothing
  exact Measurable.lintegral_prod_right (by fun_prop)

lemma lintegral_fiberSmoothing_test {F : Ω × Y → ℝ≥0∞} {ρ : Y → ℝ≥0∞}
    (hF : Measurable F) (hρ : Measurable ρ) (f : Ω × Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, fiberSmoothing τ F ρ z * f z ∂γ.prod τ) =
      ∫⁻ z, (∫⁻ y, ρ (y - z.2) * f (z.1, y) ∂τ) ∂(γ.prod τ).withDensity F := by
  have hK : Measurable (fun z : Ω × Y => ∫⁻ y, ρ (y-z.2) * f (z.1,y) ∂τ) :=
    Measurable.lintegral_prod_right (by fun_prop)
  rw [lintegral_withDensity_eq_lintegral_mul _ hF hK]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun z => fiberSmoothing τ F ρ z * f z)
      ((measurable_fiberSmoothing τ hF hρ).mul hf).aemeasurable,
    lintegral_prod (fun z => F z * ∫⁻ y, ρ (y-z.2) * f (z.1,y) ∂τ)
      (hF.mul hK).aemeasurable]
  apply lintegral_congr
  intro A
  dsimp only [fiberSmoothing]
  have hmul (y : Y) : (∫⁻ b, ρ (y-b) * F (A,b) ∂τ) * f (A,y) =
      ∫⁻ b, (ρ (y-b) * F (A,b)) * f (A,y) ∂τ :=
    (lintegral_mul_const _ (by fun_prop)).symm
  simp_rw [hmul]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro b
  rw [← lintegral_const_mul _ (by fun_prop : Measurable (fun y => ρ (y-b) * f (A,y)))]
  apply lintegral_congr
  intro y
  ring
end FiberSmoothing

section ProjectionSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance density_reference_sigmaFinite (m : ℕ) :
    SigmaFinite (matrixLabelReference (E := E) m) := by
  unfold matrixLabelReference
  infer_instance

lemma lintegral_projectionSmoothing_test (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ)
    (f : (Fin m → E) × (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, projectionSmoothing ν φ m z * f z ∂matrixLabelReference m) =
      ∫⁻ z, (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - z.2 j)) * f (z.1, y))
        ∂projectionLaw ν m := by
  have hK : Measurable (fun z : (Fin m → E) × (Fin m → ℝ) =>
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j-z.2 j)) * f (z.1,y)) :=
    Measurable.lintegral_prod_right (by fun_prop)
  rw [projectionLaw, lintegral_map hK (by fun_prop), matrixLabelReference,
    lintegral_prod (fun z => projectionSmoothing ν φ m z * f z)
      ((measurable_projectionSmoothing ν φ hφ m).mul hf).aemeasurable,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  dsimp only [projectionSmoothing]
  have hmul (y : Fin m → ℝ) : (∫⁻ t : E, ∏ j, φ (y j-⟪t,A j⟫) ∂ν) * f (A,y) =
      ∫⁻ t : E, (∏ j, φ (y j-⟪t,A j⟫)) * f (A,y) ∂ν :=
    (lintegral_mul_const _ (by fun_prop)).symm
  simp_rw [hmul]
  rw [lintegral_lintegral_swap (by fun_prop)]

lemma projectionSmoothing_ae_eq_fiberSmoothing (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (F : (Fin m → E) × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hden : (matrixLabelReference m).withDensity F = projectionLaw ν m)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    projectionSmoothing ν φ m =ᵐ[matrixLabelReference m]
      fiberSmoothing volume F (fun y : Fin m → ℝ => ∏ j, φ (y j)) := by
  apply (withDensity_eq_iff_of_sigmaFinite
    (measurable_projectionSmoothing ν φ hφ m).aemeasurable
    (measurable_fiberSmoothing volume hF (by fun_prop)).aemeasurable).mp
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_projectionSmoothing ν φ hφ m) hf,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_fiberSmoothing volume hF (by fun_prop)) hf]
  simp only [Pi.mul_apply]
  rw [lintegral_projectionSmoothing_test ν φ hφ m f hf]
  change _ = ∫⁻ z, fiberSmoothing volume F (fun y : Fin m → ℝ => ∏ j, φ (y j)) z * f z
    ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod volume
  rw [lintegral_fiberSmoothing_test _ volume hF (by fun_prop) f hf]

  unfold matrixLabelReference at hden
  rw [hden]
  rfl
end ProjectionSmoothing

def boxScalar (δ : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2*δ))⁻¹ * (Icc (-δ) δ).indicator 1 t

@[fun_prop] lemma measurable_boxScalar (δ : ℝ) : Measurable (boxScalar δ) := by
  exact measurable_const.mul (measurable_const.indicator measurableSet_Icc)

lemma lintegral_boxScalar {δ : ℝ} (hδ : 0 < δ) : ∫⁻ t, boxScalar δ t = 1 := by
  unfold boxScalar
  rw [lintegral_const_mul _ (show Measurable ((Icc (-δ) δ).indicator (1 : ℝ → ℝ≥0∞)) from
    measurable_one.indicator measurableSet_Icc), lintegral_indicator measurableSet_Icc]
  simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_neg_eq_add]
  rw [← two_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

lemma box_product_eq (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : Fin m → ℝ) :
    (∏ j, boxScalar δ (y j)) =
      ((volume : Measure (Fin m → ℝ)) (Metric.closedBall 0 δ))⁻¹ *
        (Metric.closedBall 0 δ).indicator 1 y := by
  have hv : (volume : Measure (Fin m → ℝ)) (Metric.closedBall 0 δ) =
      (ENNReal.ofReal (2*δ))^m := by
    rw [volume_pi, closedBall_pi _ hδ.le, Measure.pi_pi]
    simp [Real.closedBall_eq_Icc, ← two_mul]
  rw [hv]
  simp only [boxScalar, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]
  congr 1
  by_cases hy : y ∈ Metric.closedBall (0 : Fin m → ℝ) δ
  · rw [Set.indicator_of_mem hy]
    have hy' : ∀ j, y j ∈ Icc (-δ) δ := by
      intro j
      rw [closedBall_pi _ hδ.le] at hy
      simpa [Real.closedBall_eq_Icc] using hy j (mem_univ j)
    simp [hy']
  · rw [Set.indicator_of_notMem hy]
    have hy' : ∃ j, y j ∉ Icc (-δ) δ := by
      by_contra h
      apply hy
      rw [closedBall_pi _ hδ.le]
      intro j _
      have hh := not_not.mp (not_exists.mp h j)
      simpa [Real.closedBall_eq_Icc] using hh
    obtain ⟨j,hj⟩ := hy'
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)

section Differentiation
variable {Ω : Type*} [MeasurableSpace Ω]

lemma fiberSmoothing_box_eq_average (m : ℕ)
    (F : Ω × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    {δ : ℝ} (hδ : 0 < δ) (A : Ω) (y : Fin m → ℝ) :
    fiberSmoothing volume F (fun x : Fin m → ℝ => ∏ j, boxScalar δ (x j)) (A,y) =
      (∫⁻ b in Metric.closedBall y δ, F (A,b)) /
        (volume : Measure (Fin m → ℝ)) (Metric.closedBall y δ) := by
  unfold fiberSmoothing
  simp_rw [box_product_eq m hδ]
  have he (b : Fin m → ℝ) :
      (Metric.closedBall (0 : Fin m → ℝ) δ).indicator (1 : (Fin m → ℝ) → ℝ≥0∞) (y-b) * F (A,b) =
      (Metric.closedBall y δ).indicator (fun b => F (A,b)) b := by
    have hb : y-b ∈ Metric.closedBall (0 : Fin m → ℝ) δ ↔ b ∈ Metric.closedBall y δ := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    by_cases h : b ∈ Metric.closedBall y δ
    · rw [Set.indicator_of_mem (hb.mpr h), Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem (mt hb.mp h), Set.indicator_of_notMem h]; simp
  simp_rw [mul_assoc, he]
  rw [lintegral_const_mul _ (show Measurable ((Metric.closedBall y δ).indicator
    (fun b => F (A,b))) from (hF.comp (measurable_const.prodMk measurable_id)).indicator
      Metric.isClosed_closedBall.measurableSet), lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    div_eq_mul_inv, Measure.addHaar_closedBall_center volume y δ, mul_comm]

lemma ae_tendsto_fiberSmoothing_box (γ : Measure Ω) [SigmaFinite γ] (m : ℕ)
    (F : Ω × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hfin : (∫⁻ z, F z ∂γ.prod volume) ≠ ∞) :
    ∀ᵐ z ∂γ.prod volume,
      Tendsto (fun k : ℕ => fiberSmoothing volume F
        (fun x : Fin m → ℝ => ∏ j, boxScalar (1 / ((k:ℝ)+1)) (x j)) z)
        atTop (𝓝 (F z)) := by
  have hmeas (k : ℕ) : Measurable (fiberSmoothing volume F
      (fun x : Fin m → ℝ => ∏ j, boxScalar (1 / ((k:ℝ)+1)) (x j))) :=
    measurable_fiberSmoothing volume hF (by fun_prop)
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hmeas hF)]
  have hinner : (∫⁻ A, ∫⁻ y : Fin m → ℝ, F (A,y) ∂volume ∂γ) ≠ ∞ := by
    rwa [← lintegral_prod _ hF.aemeasurable]
  filter_upwards [ae_lt_top (Measurable.lintegral_prod_right
    (show Measurable (fun z : Ω × (Fin m → ℝ) => F (z.1,z.2)) from hF)) hinner] with A hA
  have hFA : Measurable (fun y : Fin m → ℝ => F (A,y)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Fin m → ℝ))).ae_tendsto_lintegral_div
    hFA.aemeasurable hA.ne] with y hy
  have hδ : Tendsto (fun k : ℕ => 1 / ((k:ℝ)+1)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun k => by change 0 < 1 / ((k:ℝ)+1); positivity)⟩
  convert (hy.comp (Besicovitch.tendsto_filterAt volume y)).comp hδ using 1
  ext k
  exact fiberSmoothing_box_eq_average m F hF (by positivity) A y
end Differentiation

section MomentPassage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance passage_reference_sigmaFinite (m : ℕ) :
    SigmaFinite (matrixLabelReference (E := E) m) := by
  unfold matrixLabelReference
  infer_instance
local instance passage_projection_finite (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    IsFiniteMeasure (projectionLaw ν m) := by
  unfold projectionLaw
  infer_instance

lemma projectionLaw_set_bound_of_moment (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (hn : 1 ≤ n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing ν φ m Ay ^ (n+1) ∂matrixLabelReference m) ≤ C)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤ C^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one] using
    hbound (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv)

lemma projectionLaw_ac_of_moment (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (hn : 1 ≤ n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing ν φ m Ay ^ (n+1) ∂matrixLabelReference m) ≤ C) :
    projectionLaw ν m ≪ matrixLabelReference m := by
  intro S hS
  have hh := projectionLaw_set_bound_of_moment ν m n hn C hC hbound S
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  rw [hS, ENNReal.zero_rpow_of_pos hα, mul_zero] at hh
  exact le_zero_iff.mp hh

lemma projectionLaw_rnDeriv_moment (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (hn : 1 ≤ n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing ν φ m Ay ^ (n+1) ∂matrixLabelReference m) ≤ C) :
    (∫⁻ Ay, ((projectionLaw ν m).rnDeriv (matrixLabelReference m) Ay)^(n+1)
      ∂matrixLabelReference m) ≤ C := by
  let F := (projectionLaw ν m).rnDeriv (matrixLabelReference m)
  have hF : Measurable F := Measure.measurable_rnDeriv _ _
  have hden : (matrixLabelReference m).withDensity F = projectionLaw ν m :=
    Measure.withDensity_rnDeriv_eq _ _ (projectionLaw_ac_of_moment ν m n hn C hC hbound)
  let f : ℕ → ((Fin m → E) × (Fin m → ℝ)) → ℝ≥0∞ := fun k =>
    projectionSmoothing ν (boxScalar (1/((k:ℝ)+1))) m
  have hf (k : ℕ) : Measurable (f k) :=
    measurable_projectionSmoothing ν _ (measurable_boxScalar _) m
  have heq (k : ℕ) : f k =ᵐ[matrixLabelReference m]
      fiberSmoothing volume F (fun y : Fin m → ℝ => ∏ j, boxScalar (1/((k:ℝ)+1)) (y j)) :=
    projectionSmoothing_ae_eq_fiberSmoothing ν m F hF hden _ (measurable_boxScalar _)
  have ht : ∀ᵐ Ay ∂matrixLabelReference m, Tendsto (fun k => f k Ay) atTop (𝓝 (F Ay)) := by
    filter_upwards [ae_all_iff.mpr heq,
      ae_tendsto_fiberSmoothing_box (Measure.pi (fun _ : Fin m => stdGaussian E)) m F hF
        (Measure.lintegral_rnDeriv_lt_top (projectionLaw ν m) (matrixLabelReference m)).ne]
      with Ay he ht
    exact ht.congr (fun k => (he k).symm)
  calc
    _ = ∫⁻ Ay, atTop.liminf (fun k => (f k Ay)^(n+1)) ∂matrixLabelReference m := by
      apply lintegral_congr_ae
      filter_upwards [ht] with Ay hAy
      exact (((ENNReal.continuous_pow (n+1)).tendsto _ |>.comp hAy).liminf_eq).symm
    _ ≤ atTop.liminf (fun k => ∫⁻ Ay, (f k Ay)^(n+1) ∂matrixLabelReference m) :=
      lintegral_liminf_le (fun k => (hf k).pow_const _)
    _ ≤ C := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      exact (Filter.Eventually.of_forall (fun k =>
        hbound _ (measurable_boxScalar _) (lintegral_boxScalar (by positivity)))).frequently
end MomentPassage

end MemoryPrecision


end

end OAI
