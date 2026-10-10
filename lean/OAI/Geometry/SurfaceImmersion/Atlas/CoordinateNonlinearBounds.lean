import OAI.Geometry.SurfaceImmersion.Geometry.TensorRealVariationBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LocalIsometryBounds
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticInteraction

namespace OAI

/-! Coordinate realizations of the actual bilinear and cubic polynomial
terms in the nonlinear increment identity. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateQuadraticPolynomial_eq_cross {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X : RealModes.RField 4) (t : ℝ) :
    coordinateQuadraticPolynomial P ε G X t = fun p => (1 / 2 : ℝ) •
      tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (X ∘ planeCoordinateIsometry) t
        (planeCoordinateIsometry.symm p) := by
  funext p k
  simp only [coordinateQuadraticPolynomial, tensorQuadraticCross, quadraticCross,
    realVariation, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma coordinateQuadraticInteraction_eq_cross {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X Y : RealModes.RField 4) :
    coordinateQuadraticInteraction P ε G X Y = fun p =>
      (RealModes.realLinearizedTensor X Y p + RealModes.realMetricTensor Y p) +
      tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (Y ∘ planeCoordinateIsometry) 0
        (planeCoordinateIsometry.symm p) + coordinateQuadraticPolynomial P ε G Y 0 p := by
  funext p k
  simp only [coordinateQuadraticInteraction, tensorQuadraticCross, quadraticCross,
    realVariation, Pi.add_apply]
  congr 1
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma coordinateTaylorRemainder_eq_tensor {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X : RealModes.RField 4) :
    coordinateTaylorRemainder P ε G X =
      tensorTaylorRemainder P ε G (X ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm := rfl

theorem coordinateCross_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X Y : RealModes.RField 4)
      (s ε C D : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      WeightedBound Set.univ s (m + tensorOrder P) C X →
      WeightedBound Set.univ s (m + tensorOrder P) D Y →
        WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m (E * ε * C * D / s ^ tensorLoss P)
          (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
            (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) := by
  obtain ⟨E,hE,he⟩ := tensorQuadraticCross_bound hU hQ P hP m B hB
  refine ⟨E,hE,?_⟩
  intro G X Y s ε C D hs hs1 hε hε1 hC hD hG hX hY hGQ hGb hXb hYb
  have hx := weightedBound_comp_isometry planeCoordinateIsometry hX hXb
  have hy := weightedBound_comp_isometry planeCoordinateIsometry hY hYb
  have hb := he G (X ∘ planeCoordinateIsometry) (Y ∘ planeCoordinateIsometry)
    s ε C D hs hs1 hε hε1 hC hD hG (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) hGQ hGb
    (fun j hj p hp => by
      simpa only [iteratedFDerivWithin_of_isOpen j hU hp, iteratedFDerivWithin_univ]
        using hx j hj p (Set.mem_univ p))
    (fun j hj p hp => by
      simpa only [iteratedFDerivWithin_of_isOpen j hU hp, iteratedFDerivWithin_univ]
        using hy j hj p (Set.mem_univ p)) 0 (by constructor <;> norm_num)
  exact weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU
    (tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
      (hY.comp planeCoordinateIsometry.contDiff) ε 0) hb

theorem coordinateTaylorRemainder_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X : RealModes.RField 4)
      (s ε C : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p))) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + tensorOrder P) B
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p)))) →
      WeightedBound Set.univ s (m + tensorOrder P) C X →
        WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m
          (E * ε * C ^ 3 / s ^ tensorLoss P) (coordinateTaylorRemainder P ε G X) := by
  obtain ⟨E,hE,he⟩ := tensorTaylorRemainder_bound hU hQ P hP m B hB
  refine ⟨E,hE,?_⟩
  intro G X s ε C hs hs1 hε hε1 hC hG hX hGQ hGb hXb
  have hx := weightedBound_comp_isometry planeCoordinateIsometry hX hXb
  have hb := he G (X ∘ planeCoordinateIsometry) s ε C hs hs1 hε hε1 hC hG
    (hX.comp planeCoordinateIsometry.contDiff) hGQ hGb
    (fun j hj p hp => by
      simpa only [iteratedFDerivWithin_of_isOpen j hU hp, iteratedFDerivWithin_univ]
        using hx j hj p (Set.mem_univ p)) 0 (by constructor <;> norm_num)
  rw [coordinateTaylorRemainder_eq_tensor]
  exact weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU
    (tensorTaylorRemainder_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff) ε 0) hb

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
