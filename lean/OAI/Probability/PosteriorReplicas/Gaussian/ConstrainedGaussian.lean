import OAI.Probability.PosteriorReplicas.Gaussian.GaussianDensity

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def pairingsDensity {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
    Real.exp (-‖pairingLift v y‖^2 / 2) / Real.sqrt (Matrix.gram ℝ v).det)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma continuous_pairingsDensity
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} (v : Fin n → E) :
    Continuous (pairingsDensity v) := by
  unfold pairingsDensity
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

lemma gaussian_pairingsDensity {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) =
      volume.withDensity (pairingsDensity v) := gaussian_pairings_density hv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairingsDensity_le_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) :
    pairingsDensity v y ≤ pairingsDensity v 0 := by
  have hzero : pairingLift v 0 = 0 := by simp [pairingLift]
  unfold pairingsDensity
  rw [hzero, norm_zero, zero_pow (by decide), neg_zero, zero_div, Real.exp_zero, mul_one]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have he : Real.exp (-‖pairingLift v y‖^2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  simpa using mul_le_mul_of_nonneg_left he
    (show 0 ≤ (2 * Real.pi) ^ (-(n : ℝ) / 2) by positivity)

lemma rows_pairings_residual_joint {n : ℕ} (v : Fin n → E) (k : ℕ) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map
      (fun A => ((fun j i => ⟪v i, A j⟫),
        (fun j => (Submodule.span ℝ (Set.range v))ᗮ.starProjection (A j)))) =
    (Measure.pi (fun _ : Fin k => (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫))).prod
      (Measure.pi (fun _ : Fin k =>
        (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection)) := by
  let U := Submodule.span ℝ (Set.range v)
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) E (Fin k)
  have h := (gaussian_pairings_residual_indep v).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)
  have hm : (fun A : Fin k → E => ((fun j i => ⟪v i, A j⟫),
      fun j => Uᗮ.starProjection (A j))) =
      e ∘ (fun A => fun j => ((fun i => ⟪v i, A j⟫), Uᗮ.starProjection (A j))) := rfl
  change (Measure.pi _).map (fun A => ((fun j i => ⟪v i, A j⟫), fun j => Uᗮ.starProjection (A j))) = _
  rw [hm, ← Measure.map_map e.measurable (by fun_prop),
    Measure.pi_map_pi (fun _ => (show Measurable (fun x : E =>
      ((fun i => ⟪v i, x⟫), Uᗮ.starProjection x)) by fun_prop).aemeasurable)]
  dsimp only [U]
  simp_rw [h]
  exact (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) E (Fin k) _ _).map_eq

lemma rows_pairings_disintegration {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (k : ℕ) :
    ((Measure.pi (fun _ : Fin k => (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫))).prod
      (Measure.pi (fun _ : Fin k =>
        (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection))).map
      (fun z j => pairingLift v (z.1 j) + z.2 j) =
        Measure.pi (fun _ : Fin k => stdGaussian E) := by
  rw [← rows_pairings_residual_joint, Measure.map_map (by fun_prop) (by fun_prop)]
  convert (Measure.map_id (μ := Measure.pi (fun _ : Fin k => stdGaussian E))) using 1
  congr 1
  funext A j
  simp only [Function.comp_apply]
  rw [← starProjection_eq_pairingLift hv,
    Submodule.starProjection_add_starProjection_orthogonal]
  rfl

lemma rows_pairings_density {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) (k : ℕ) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map (fun A j i => ⟪v i, A j⟫) =
      (volume : Measure (Fin k → Fin n → ℝ)).withDensity
        (fun y => ∏ j, pairingsDensity v (y j)) := by
  have : IsProbabilityMeasure (volume.withDensity (pairingsDensity v)) := by
    rw [← gaussian_pairingsDensity hv]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  rw [Measure.pi_map_pi (fun _ => (show Measurable
    (fun x : E => fun i => ⟪v i, x⟫) by fun_prop).aemeasurable)]
  simp_rw [gaussian_pairingsDensity hv]
  exact pi_withDensity _ _ (fun _ => (continuous_pairingsDensity v).measurable)

lemma constrained_gaussian_integral {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (k : ℕ) {g : (Fin k → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ A, g A ∂Measure.pi (fun _ : Fin k => stdGaussian E) =
      ∫⁻ y : Fin k → Fin n → ℝ, (∏ j, pairingsDensity v (y j)) *
        ∫⁻ R, g (fun j => pairingLift v (y j) + R j)
          ∂Measure.pi (fun _ : Fin k =>
            (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection) := by
  have hp : IsProbabilityMeasure (volume.withDensity (pairingsDensity v)) := by
    rw [← gaussian_pairingsDensity hv]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  conv_lhs => rw [← rows_pairings_disintegration hv k]
  rw [lintegral_map hg (by fun_prop), lintegral_prod _ (by fun_prop)]
  simp_rw [gaussian_pairingsDensity hv]
  rw [pi_withDensity _ _ (fun _ => (continuous_pairingsDensity v).measurable),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairingsDensity_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (v : Fin n → E) :
    pairingsDensity v 0 = ENNReal.ofReal
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) / Real.sqrt (Matrix.gram ℝ v).det) := by
  simp [pairingsDensity, pairingLift]

lemma rows_pairingsDensity_zero {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (k : ℕ) :
    (∏ _j : Fin k, pairingsDensity v 0) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-((k : ℝ) * n) / 2)) *
        (ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ v).det))⁻¹ ^ k := by
  have hd : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
    Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pairingsDensity_zero,
    ENNReal.ofReal_div_of_pos hd, div_eq_mul_inv, mul_pow]
  congr 1
  rw [← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  congr 2
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_rows_pairingsDensity [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (v : Fin n → E) (k : ℕ) :
    Continuous (fun y : Fin k → Fin n → ℝ => ∏ j, pairingsDensity v (y j)) := by
  have he (y : Fin k → Fin n → ℝ) : (∏ j, pairingsDensity v (y j)) =
      ENNReal.ofReal (∏ j, ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖pairingLift v (y j)‖^2 / 2) / Real.sqrt (Matrix.gram ℝ v).det)) := by
    symm
    exact ENNReal.ofReal_prod_of_nonneg (by intro j hj; positivity)
  simp_rw [he]
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

lemma constrained_gaussian_approximation_limit {n : ℕ} (v : Fin n → E) (k : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Fin k → Fin n → ℝ) (hZ : ∀ q, Measurable (Z q))
    (hZ0 : ∀ᵐ z ∂μ, Filter.Tendsto (fun q => Z q z) Filter.atTop (nhds 0))
    {g : (Fin k → E) → ℝ≥0∞} (hg : Continuous g)
    (b : ℝ≥0∞) (hb : b ≠ ∞) (hgb : ∀ A, g A ≤ b) :
    Filter.Tendsto (fun q => ∫⁻ z, ∫⁻ R,
        (∏ j, pairingsDensity v (Z q z j)) *
          g (fun j => pairingLift v (Z q z j) + R j)
        ∂Measure.pi (fun _ : Fin k =>
          (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection) ∂μ)
      Filter.atTop (nhds ((∏ _j : Fin k, pairingsDensity v 0) *
        ∫⁻ R, g R ∂Measure.pi (fun _ : Fin k =>
          (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection))) := by
  let ρ := Measure.pi (fun _ : Fin k =>
    (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection)
  have : IsProbabilityMeasure ((stdGaussian E).map
      (Submodule.span ℝ (Set.range v))ᗮ.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hc : (∏ _j : Fin k, pairingsDensity v 0) ≠ ∞ :=
    ENNReal.prod_ne_top (by intro j hj; exact ENNReal.ofReal_ne_top)
  have hlim := tendsto_lintegral_of_dominated_convergence
    (μ := μ.prod ρ) (fun _ => (∏ _j : Fin k, pairingsDensity v 0) * b)
    (F := fun q z => (∏ j, pairingsDensity v (Z q z.1 j)) *
      g (fun j => pairingLift v (Z q z.1 j) + z.2 j))
    (f := fun z => (∏ _j : Fin k, pairingsDensity v 0) * g z.2)
    (fun q => by fun_prop)
    (fun q => Filter.Eventually.of_forall fun z => mul_le_mul'
      (Finset.prod_le_prod (fun j hj => pairingsDensity_le_zero _ _)) (hgb _))
    (by simpa using ENNReal.mul_ne_top hc hb)
    (by
      have hZ' : ∀ᵐ z ∂μ.prod ρ,
          Filter.Tendsto (fun q => Z q z.1) Filter.atTop (nhds 0) :=
        Measure.quasiMeasurePreserving_fst.ae hZ0
      filter_upwards [hZ'] with z hz
      apply ENNReal.Tendsto.mul
        ((continuous_rows_pairingsDensity v k).tendsto 0 |>.comp hz)
        (Or.inr ((lt_of_le_of_lt (hgb _) (lt_top_iff_ne_top.mpr hb)).ne))
      · apply hg.tendsto z.2 |>.comp
        have ht : Filter.Tendsto
            (fun q => fun j => pairingLift v (Z q z.1 j) + z.2 j)
            Filter.atTop (nhds (fun j => pairingLift v 0 + z.2 j)) :=
          (show Continuous (fun y : Fin k → Fin n → ℝ =>
            fun j => pairingLift v (y j) + z.2 j) by fun_prop).tendsto 0 |>.comp hz
        simpa [pairingLift] using ht
      · exact Or.inr hc)
  have heq : (fun q => ∫⁻ z, ∫⁻ R,
        (∏ j, pairingsDensity v (Z q z j)) *
          g (fun j => pairingLift v (Z q z j) + R j) ∂ρ ∂μ) =
      (fun q => ∫⁻ z : Ω × (Fin k → E),
        (∏ j, pairingsDensity v (Z q z.1 j)) *
          g (fun j => pairingLift v (Z q z.1 j) + z.2 j) ∂μ.prod ρ) := by
    funext q
    symm
    exact lintegral_prod _ (by fun_prop)
  change Filter.Tendsto (fun q => ∫⁻ z, ∫⁻ R,
    (∏ j, pairingsDensity v (Z q z j)) *
      g (fun j => pairingLift v (Z q z j) + R j) ∂ρ ∂μ) _ _
  rw [heq]
  convert hlim using 1
  rw [lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const_mul _ hg.measurable, lintegral_const, measure_univ, mul_one]
  rfl

end Rows
end PosteriorReplicas
end

end OAI
