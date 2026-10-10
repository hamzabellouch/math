import OAI.Geometry.NodalSets.Charts.AbsolutePiola
import OAI.Geometry.NodalSets.Charts.SphereTransitionScalar
import OAI.Geometry.NodalSets.Charts.SphereTransitionTensor

namespace OAI

noncomputable section

namespace Yau.Geometry
open Matrix

lemma inverse_contravariant_gradient (J B : Matrix (Fin 4) (Fin 4) ℝ)
    (hJ : J.det ≠ 0) (v : Fin 4 → ℝ) :
    (J⁻¹ * B * J⁻¹.transpose).mulVec (J.transpose.mulVec v) =
      J⁻¹.mulVec (B.mulVec v) := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_mul _ (by simpa using (isUnit_iff_ne_zero.mpr hJ)),Matrix.mul_one,
    ← Matrix.mulVec_mulVec]

lemma absolute_inverse_flux (J : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    |J.det| * (J⁻¹.mulVec v) i = |J.det| / J.det * ∑ j, J.adjugate i j * v j := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.mulVec,Matrix.smul_apply,
    smul_eq_mul,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Yau.Geometry
namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix
open scoped ContDiff

def sphereCoordFlux (A : IntrinsicTensor) (f : Base → ℝ) (p : Base)
    (i : Fin 4) (x : Coord) : ℂ :=
  (intrinsicRoundFlux A f p i (seedCoordEquiv x) : ℂ)

lemma sphereChartTransition_flux (A : IntrinsicTensor) (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p q : Base) {x : Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) (i : Fin 4) :
    sphereCoordFlux A f p i x =
      absolutePiola (sphereChartTransition p q) (sphereCoordFlux A f q) i x := by
  let J := jacobian (sphereChartTransition p q) x
  let B := intrinsicSphereChartTensor A q (seedCoordEquiv (sphereChartTransition p q x))
  let v := fun j ↦ sphereScalarPartial f q j (sphereChartTransition p q x)
  have hg : (fun j ↦ sphereScalarPartial f p j x) = J.transpose.mulVec v := by
    funext j
    exact sphereChartTransition_scalar f hf p q hx j
  have ht := inverse_contravariant_gradient J B (sphereChartTransition_jacobian_ne_zero p q hx) v
  have hreal : intrinsicRoundFlux A f p i (seedCoordEquiv x) =
      |J.det| / J.det * ∑ j, J.adjugate i j *
        intrinsicRoundFlux A f q j (seedCoordEquiv (sphereChartTransition p q x)) := by
    change roundChartDensity p (seedCoordEquiv x) *
      ((intrinsicSphereChartTensor A p (seedCoordEquiv x)).mulVec
        (fun j ↦ sphereScalarPartial f p j x)) i = _
    rw [sphereChartTransition_round_density p q hx,sphereChartTransition_intrinsic_tensor A p q hx,hg]
    change (|J.det| * _) * ((J⁻¹*B*J⁻¹.transpose).mulVec (J.transpose.mulVec v)) i = _
    rw [ht]
    calc
      _ = roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)) *
          (|J.det| * (J⁻¹.mulVec (B.mulVec v)) i) := by ring
      _ = _ := by
        rw [absolute_inverse_flux]
        change _ = |J.det| / J.det * ∑ j, J.adjugate i j *
          (roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)) * (B.mulVec v) j)
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  unfold sphereCoordFlux absolutePiola signedPiola
  dsimp only
  dsimp only [J] at hreal
  exact_mod_cast hreal

end Yau.Target

end

end OAI
