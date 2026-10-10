import OAI.Geometry.ProjectionVolume.ProductVolume

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Paper092

def splitEuclideanProduct (r s : ℕ) : Euclidean (r + s) ≃L[ℝ] Euclidean r × Euclidean s :=
  letI : ContinuousSMul ℝ (Euclidean r × Euclidean s) := Prod.continuousSMul
  let equiv : Euclidean (r + s) ≃ₗ[ℝ] Euclidean r × Euclidean s :=
    (((WithLp.linearEquiv 2 ℝ (Fin (r + s) → ℝ)).trans
      (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (r + s) => ℝ)
        (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))).symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℝ ℝ) |>.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Fin r → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Fin s → ℝ)).symm))
  equiv.toContinuousLinearEquiv

theorem splitEuclideanProduct_measurePreserving (r s : ℕ) :
    MeasurePreserving (splitEuclideanProduct r s) volume volume := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin (r + s))
  have h₂ := (volume_measurePreserving_piCongrLeft (fun _ : Fin (r + s) => ℝ)
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin s => ℝ)
  have h₄ := (PiLp.volume_preserving_toLp (Fin r)).prod
    (PiLp.volume_preserving_toLp (Fin s))
  convert h₄.comp (h₃.comp (h₂.comp h₁)) using 1
  all_goals rfl

theorem splitEuclideanProduct_volume (r s : ℕ) (A : Set (Euclidean r))
    (B : Set (Euclidean s)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) = volume A * volume B := by
  rw [(splitEuclideanProduct_measurePreserving r s).measure_preimage
    (hA.prod hB).nullMeasurableSet]
  exact Measure.prod_prod _ _

def simplexProduct (r s : ℕ) : Set (Euclidean (r + s)) :=
  splitEuclideanProduct r s ⁻¹' (standardSimplex r ×ˢ standardSimplex s)

theorem simplexProduct_volume (r s : ℕ) :
    volume (simplexProduct r s) =
      ENNReal.ofReal ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ))) := by
  rw [simplexProduct, splitEuclideanProduct_volume r s _ _
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet,
    standardSimplex_volume, standardSimplex_volume, ← ENNReal.ofReal_mul (by positivity)]

end Paper092

end

end OAI
