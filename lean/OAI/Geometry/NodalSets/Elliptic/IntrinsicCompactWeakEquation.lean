import OAI.Geometry.NodalSets.Elliptic.CompactWeightedWeakEquation
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRealCoordinates

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsicRealVector_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (fun y ↦ ∑ j, intrinsicRealPrincipal A p y i j*
      Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) :=
  ContDiff.sum (fun j _ ↦ (intrinsicRealPrincipal_smooth A hA hs hp p i j).mul
    (real_coordPartial_smooth _ (spherePullback_smooth w hw p) j))

lemma intrinsic_real_divergence_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (w : Base → ℝ) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base) (x : Yau.Jets.Coord) :
    Yau.weightedDiv roundCoordDensity
      (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x +
      intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x) = 0 := by
  have h := he p (seedCoordEquiv x)
  rw [intrinsicRealOperator_pullback] at h
  change -((rho (sphereChartCoordMap p x))⁻¹ * _) = lam*w (sphereChartCoordMap p x) at h
  have hmul := congrArg (fun t : ℝ ↦ rho (sphereChartCoordMap p x)*t) h
  rw [mul_neg,← mul_assoc,mul_inv_cancel₀ (hrp _).ne',one_mul] at hmul
  dsimp [intrinsicRealPotential]
  linarith

theorem intrinsic_compact_weak_equation (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (fun x ↦ roundCoordDensity x *
      ∑ i, ∑ j, Yau.coordPartial phi x i*intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) ∧
    Integrable (fun x ↦ roundCoordDensity x*phi x*
      (intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x))) ∧
    (∫ x, roundCoordDensity x * ∑ i, ∑ j,
      Yau.coordPartial phi x i*intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) =
    ∫ x, roundCoordDensity x*phi x*(intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x)) := by
  have h := compact_weighted_weak_equation roundCoordDensity phi
    (fun x ↦ intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x))
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hphi hc
    (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
      Yau.coordPartial (w ∘ sphereChartCoordMap p) y j)
    (intrinsicRealVector_smooth A hA hs hp w hw p)
    (intrinsic_real_divergence_equation A rho hrp w lam he p)
  simpa only [Yau.pairing,Finset.mul_sum,mul_assoc] using h

end
end Yau.Target

end OAI
