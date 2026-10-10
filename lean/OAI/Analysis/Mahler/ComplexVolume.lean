import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

open MeasureTheory WithLp
open scoped ENNReal
namespace SymmetricMahler

variable (n : ℕ)

/-- Realification with the Euclidean norm on both groups of real coordinates. -/
noncomputable def complexEuclideanRealification :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) where
  toFun z := toLp 2 (toLp 2 (fun i => (z i).re), toLp 2 (fun i => (z i).im))
  invFun z := toLp 2 (fun i => ⟨(ofLp z).1 i, (ofLp z).2 i⟩)
  left_inv z := by ext i; rfl
  right_inv z := by rfl
  map_add' z w := by rfl
  map_smul' c z := by
    apply ofLp_injective 2
    apply Prod.ext <;> ext i <;> simp
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      Real.norm_eq_abs, sq_abs]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (z i).re ^ 2 + (z i).im ^ 2 = ‖z i‖ ^ 2
    simpa only [Complex.normSq_apply, pow_two] using (Complex.sq_norm (z i)).symm

/-- Euclidean complex coordinates to separated real coordinates, with exact volume. -/
theorem volume_preserving_complexEuclidean_split :
    MeasurePreserving (fun z : EuclideanSpace ℂ (Fin n) =>
      ((fun i => (z i).re), (fun i => (z i).im))) := by
  have h := ((PiLp.volume_preserving_ofLp (Fin n)).prod
      (PiLp.volume_preserving_ofLp (Fin n))).comp
    ((WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))).comp
      (complexEuclideanRealification n).measurePreserving)
  exact h

/-- Forgetting the L2 wrapper on complex coordinates preserves standard volume. -/
theorem volume_preserving_complex_ofLp :
    MeasurePreserving (@WithLp.ofLp 2 (Fin n → ℂ)) := by
  have hsplit := volume_preserving_complexEuclidean_split n
  have hjoin := (volume_preserving_pi (ι := Fin n)
    (fun _ => Complex.volume_preserving_equiv_real_prod.symm)).comp
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  convert hjoin.comp hsplit using 1
  ext z i
  rfl

/-- The inverse transport from coordinate product volume to Euclidean volume. -/
theorem volume_preserving_complex_toLp :
    MeasurePreserving (@WithLp.toLp 2 (Fin n → ℂ)) :=
  (show MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm volume volume from
    volume_preserving_complex_ofLp n).symm

/-- Explicit equality of the two measures, with scale factor exactly one. -/
theorem map_volume_complex_ofLp :
    Measure.map (@WithLp.ofLp 2 (Fin n → ℂ))
      (volume : Measure (EuclideanSpace ℂ (Fin n))) =
        (volume : Measure (Fin n → ℂ)) :=
  (volume_preserving_complex_ofLp n).map_eq

/-- Arbitrary nonnegative densities transport without finiteness assumptions. -/
theorem lintegral_complex_ofLp (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ z : EuclideanSpace ℂ (Fin n), g (WithLp.ofLp z)) = ∫⁻ z, g z :=
  (volume_preserving_complex_ofLp n).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm.measurableEmbedding g

/-- Restricted density integrals agree on the literal preimage domain.
No measurability or finite-mass premise is needed because this is an equivalence. -/
theorem setLIntegral_complex_ofLp (S : Set (Fin n → ℂ))
    (g : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ z in (@WithLp.ofLp 2 (Fin n → ℂ)) ⁻¹' S, g (WithLp.ofLp z)) =
      ∫⁻ z in S, g z :=
  (volume_preserving_complex_ofLp n).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm.measurableEmbedding g S

/-- The opposite direction lets a Euclidean density be integrated in coordinates. -/
theorem setLIntegral_complex_toLp (S : Set (EuclideanSpace ℂ (Fin n)))
    (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    (∫⁻ z in (@WithLp.toLp 2 (Fin n → ℂ)) ⁻¹' S, g (WithLp.toLp 2 z)) =
      ∫⁻ z in S, g z :=
  (volume_preserving_complex_toLp n).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℂ)).measurableEmbedding g S

end SymmetricMahler

end OAI
