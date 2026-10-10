import OAI.Geometry.NodalSets.Elliptic.IntrinsicCompactWeakEquation
import OAI.Geometry.NodalSets.Elliptic.RealWeightedElliptic

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

def intrinsicDivergencePrincipal (A : IntrinsicTensor) (p : Base) (x : Yau.Jets.Coord) :
    Matrix (Fin 4) (Fin 4) ℝ := roundCoordDensity x • intrinsicRealPrincipal A p x

def intrinsicDivergencePotential (rho : Base → ℝ) (lam : ℝ) (p : Base) (x : Yau.Jets.Coord) : ℝ :=
  roundCoordDensity x * intrinsicRealPotential rho lam p x

lemma intrinsicDivergencePrincipal_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (i j : Fin 4) : ContDiff ℝ ∞ (fun x ↦ intrinsicDivergencePrincipal A p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth A hA hs hp p i j)

lemma intrinsicDivergencePrincipal_symmetric (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (p : Base) (x : Yau.Jets.Coord) (i j : Fin 4) :
    intrinsicDivergencePrincipal A p x i j = intrinsicDivergencePrincipal A p x j i := by
  change roundCoordDensity x * _ = roundCoordDensity x * _
  rw [intrinsicRealPrincipal_symmetric A hs]

lemma intrinsicDivergencePrincipal_posDef (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (x : Yau.Jets.Coord) : (intrinsicDivergencePrincipal A p x).PosDef :=
  (intrinsicRealPrincipal_posDef A hs hp p x).smul (roundCoordDensity_pos x)

lemma intrinsicDivergencePotential_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (lam : ℝ) (p : Base) :
    ContDiff ℝ ∞ (intrinsicDivergencePotential rho lam p) :=
  roundCoordDensity_smooth.mul (intrinsicRealPotential_smooth rho hr lam p)

theorem intrinsic_unweighted_divergence_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (w : Base → ℝ) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base) (x : Yau.Jets.Coord) :
    Yau.coordDiv (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x +
      intrinsicDivergencePotential rho lam p x * (w ∘ sphereChartCoordMap p) x = 0 := by
  have h := intrinsic_real_divergence_equation A rho hrp w lam he p x
  rw [Yau.weightedDiv] at h
  have hh := congrArg (fun s : ℝ ↦ roundCoordDensity x*s) h
  rw [mul_add,← mul_assoc,mul_inv_cancel₀ (roundCoordDensity_pos x).ne',one_mul,mul_zero] at hh
  have hf : realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p) =
      fun y i ↦ roundCoordDensity y * ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j := by
    funext y i
    simp [realMatrixFlux,intrinsicDivergencePrincipal,Finset.mul_sum,mul_assoc]
  rw [hf]
  simpa only [intrinsicDivergencePotential,Function.comp_apply,mul_assoc] using hh

end
end Yau.Target

end OAI
