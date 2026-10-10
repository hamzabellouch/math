import OAI.Geometry.Zonotope.Volume
import OAI.Geometry.Zonotope.Product
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma volume_scaled_centered (c : ℝ) (hc : 0 ≤ c) :
    volume ((fun y : ι → ℝ => c • y) '' centered) =
      ENNReal.ofReal (c ^ Fintype.card ι) * ((Fintype.card ι : ℝ≥0∞) + 1) := by
  change volume (c • (centered : Set (ι → ℝ))) = _
  rw [Measure.addHaar_smul_of_nonneg volume hc, Module.finrank_pi, volume_centered]

/-- The coordinate calculation gives actual Euclidean Lebesgue volume. -/
theorem volume_euclidean (c : ℝ) (hc : 0 ≤ c) :
    volume (euclidean c : Set (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (c ^ Fintype.card ι) * ((Fintype.card ι : ℝ≥0∞) + 1) := by
  have hs : (euclidean c : Set (EuclideanSpace ℝ ι)) =
      WithLp.ofLp ⁻¹' ((fun y : ι → ℝ => c • y) '' centered) := by
    ext x
    exact mem_euclidean_iff c x
  rw [hs, (PiLp.volume_preserving_ofLp ι).measure_preimage
    (isCompact_scaled_centered c).measurableSet.nullMeasurableSet,
    volume_scaled_centered c hc]

lemma finAdd_measurePreserving (n m : ℕ) :
    MeasurePreserving (@EuclideanSpace.finAddEquivProd ℝ _ n m) := by
  exact (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m))).comp
      ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℝ)).measurePreserving.comp
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).measurePreserving)

/-- The block product has the product of its two Euclidean volumes. -/
theorem volume_euclideanProduct (n m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    volume (euclideanProduct n m c) =
      (ENNReal.ofReal (c ^ n) * ((n : ℝ≥0∞) + 1)) *
      (ENNReal.ofReal (c ^ m) * ((m : ℝ≥0∞) + 1)) := by
  rw [euclideanProduct, (finAdd_measurePreserving n m).measure_preimage
    ((isCompact_euclidean c).prod (isCompact_euclidean c)).measurableSet.nullMeasurableSet]
  change (volume.prod volume) ((euclidean c : Set (EuclideanSpace ℝ (Fin n))) ×ˢ
    (euclidean c : Set (EuclideanSpace ℝ (Fin m)))) = _
  rw [Measure.prod_prod, volume_euclidean c hc, volume_euclidean c hc]
  simp only [Fintype.card_fin]

/-- Real-valued Euclidean volume for the normalized-ratio calculation. -/
theorem volume_euclidean_toReal (c : ℝ) (hc : 0 ≤ c) :
    (volume (euclidean c : Set (EuclideanSpace ℝ ι))).toReal =
      c ^ Fintype.card ι * ((Fintype.card ι : ℝ) + 1) := by
  rw [volume_euclidean c hc]
  simp [ENNReal.toReal_mul, ENNReal.toReal_add, pow_nonneg hc]

/-- Real-valued volume of the two-block product. -/
theorem volume_euclideanProduct_toReal (n m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (volume (euclideanProduct n m c)).toReal =
      c ^ (n + m) * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
  rw [volume_euclideanProduct n m c hc]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc n),
    ENNReal.toReal_ofReal (pow_nonneg hc m)]
  simp [ENNReal.toReal_add, pow_add]
  ring

end DiagonalZonotope

end

end OAI
