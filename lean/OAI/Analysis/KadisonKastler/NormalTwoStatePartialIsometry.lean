import OAI.Analysis.KadisonKastler.NormalTwoStateGeometry
import OAI.Analysis.KadisonKastler.PartialIsometryCorner

namespace OAI

/-! # A spatial bridge from the left and right two-by-two matrix units -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
  (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))
  (Ω : H) (ξ : K)
  (hcyc : DenseRange (algebraVectorMap (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ)))
  (d : ModularConjugationData (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ))

def normalTwoStateBridge : TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K :=
  normalTwoStateSlot θ hθ 1 0 1 *
    conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1)

include hcyc in
private theorem bridge_right_initial :
    star (conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1)) *
      conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1) =
        twoStateSummandProjection 0 := by
  rw [← conjugationOperator_star _ d.involutive,
    ← conjugationOperator_mul _ d.involutive,
    normalTwoStateSlot_star, star_one, normalTwoStateSlot_mul, one_mul]
  exact normalTwoStateProjection_conjugation θ hθ Ω ξ hcyc d 0

include hcyc in
private theorem bridge_right_final :
    conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1) *
      star (conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1)) =
        twoStateSummandProjection 1 := by
  rw [← conjugationOperator_star _ d.involutive,
    ← conjugationOperator_mul _ d.involutive,
    normalTwoStateSlot_star, star_one, normalTwoStateSlot_mul, one_mul]
  exact normalTwoStateProjection_conjugation θ hθ Ω ξ hcyc d 1

private theorem bridge_right_mem :
    conjugationOperator d.conjugation (normalTwoStateSlot θ hθ 1 0 1) ∈
      (normalTwoStateAlgebra θ).commutant :=
  d.right_mem le_rfl (normalTwoStateEquiv θ hθ (matrixSlot 1 0 1))

include hcyc in
theorem normalTwoStateBridge_initial :
    (normalTwoStateBridge θ hθ Ω ξ d).adjoint.comp (normalTwoStateBridge θ hθ Ω ξ d) =
      (twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.comp
        (twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint := by
  rw [twoStateSourceEmbedding_rangeProjection θ hθ]
  change star (normalTwoStateBridge θ hθ Ω ξ d) * normalTwoStateBridge θ hθ Ω ξ d = _
  let v := normalTwoStateSlot θ hθ 1 0 1
  let q := conjugationOperator d.conjugation v
  have hq : q ∈ (normalTwoStateAlgebra θ).commutant := bridge_right_mem θ hθ Ω ξ d
  have hs : star q ∈ (normalTwoStateAlgebra θ).commutant :=
    (normalTwoStateAlgebra θ).commutant.toStarSubalgebra.star_mem' hq
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hs
    (normalTwoStateSlot θ hθ 0 0 1) (normalTwoStateEquiv θ hθ (matrixSlot 0 0 1)).property
  change star (v * q) * (v * q) = _
  calc
    _ = star q * (star v * v) * q := by simp only [star_mul]; noncomm_ring
    _ = star q * normalTwoStateSlot θ hθ 0 0 1 * q := by
      rw [show star v * v = normalTwoStateSlot θ hθ 0 0 1 by
        dsimp [v]; rw [normalTwoStateSlot_star, star_one, normalTwoStateSlot_mul, one_mul]]
    _ = normalTwoStateSlot θ hθ 0 0 1 * (star q * q) := by rw [← hc]; simp only [mul_assoc]
    _ = _ := by rw [bridge_right_initial θ hθ Ω ξ hcyc d]

include hcyc in
theorem normalTwoStateBridge_final :
    (normalTwoStateBridge θ hθ Ω ξ d).comp (normalTwoStateBridge θ hθ Ω ξ d).adjoint =
      (twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.comp
        (twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint := by
  rw [twoStateTargetEmbedding_rangeProjection θ hθ]
  change normalTwoStateBridge θ hθ Ω ξ d * star (normalTwoStateBridge θ hθ Ω ξ d) = _
  let v := normalTwoStateSlot θ hθ 1 0 1
  let q := conjugationOperator d.conjugation v
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp
    (twoStateSummandProjection_mem_commutant θ hθ 1)
    (normalTwoStateSlot θ hθ 0 1 1) (normalTwoStateEquiv θ hθ (matrixSlot 0 1 1)).property
  change (v * q) * star (v * q) = _
  calc
    _ = v * (q * star q) * star v := by simp only [star_mul]; noncomm_ring
    _ = v * twoStateSummandProjection 1 * star v := by
      rw [bridge_right_final θ hθ Ω ξ hcyc d]
    _ = (v * star v) * twoStateSummandProjection 1 := by
      dsimp [v]
      rw [normalTwoStateSlot_star, star_one]
      rw [mul_assoc, ← hc, ← mul_assoc]
    _ = _ := by
      dsimp [v]
      rw [normalTwoStateSlot_star, star_one, normalTwoStateSlot_mul, one_mul]

end

end KadisonKastler

end OAI
