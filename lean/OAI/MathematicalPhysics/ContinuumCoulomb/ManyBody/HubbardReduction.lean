import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.DiagonalPenalty
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Perturbation

namespace OAI

/-!
# Second-order estimate with the global charge penalty

The occupation configurations determine the penalty, its inverse, its
positivity and its spectral gap. The resulting bottom-energy comparison
retains every electron and spin configuration.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

abbrev HubbardLowSpace (m : ℕ) := EuclideanSpace ℂ (Fin m → Fin 2)

def hubbardLowUnit (m : ℕ) : HubbardLowSpace m :=
  EuclideanSpace.single (fun _ => 0) 1

theorem hubbardLowUnit_norm (m : ℕ) : ‖hubbardLowUnit m‖ = 1 := by
  simp [hubbardLowUnit, PiLp.norm_single]

/-- The zero first-order block Hubbard estimate, with its concrete global
charge penalty and explicit cubic error. All electron and spin configurations
are represented by the low space and the supplied high occupations. -/
theorem hubbard_charge_second_order {m : ℕ} {Basis : Type*} [Fintype Basis]
    (U R : ℝ) (V : Fin m → Fin m → ℝ) (occupation : Basis → Fin m → Fin 3)
    (hsymm : ∀ i j, V i j = V j i) (hrow : ∀ i, ∑ j, |V i j| ≤ R)
    (hUR : R < U) (hfill : ∀ s, ∑ i, (occupation s i : ℕ) = m)
    (B : HubbardLowSpace m →L[ℝ] EuclideanSpace ℂ (ChargeHighBasis occupation))
    (D : EuclideanSpace ℂ (ChargeHighBasis occupation) →L[ℝ]
      EuclideanSpace ℂ (ChargeHighBasis occupation))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (hB : ‖B‖ ≤ epsilon * (U - R)) (hD : ‖D‖ ≤ epsilon * (U - R)) :
    let weight : ChargeHighBasis occupation → ℝ :=
      fun s => chargePenalty U V (occupation s.val)
    |Perturbation.blockBottom (diagonalPenalty weight) D B -
      Perturbation.effectiveBottom (0 : HubbardLowSpace m →L[ℝ] HubbardLowSpace m)
        (diagonalPenalty (fun s => (weight s)⁻¹)) B| ≤
      2 * (U - R) * epsilon ^ 3 := by
  classical
  intro weight
  have hg : 0 < U - R := sub_pos.mpr hUR
  obtain ⟨hAT, hT, hgap⟩ := chargePenalty_inverse_data U R V occupation hsymm hrow hUR hfill
  apply Perturbation.finite_blockBottom_second_order
    (diagonalPenalty weight) (diagonalPenalty (fun s => (weight s)⁻¹)) D B
    hg hepsilon hsmall hAT (diagonalPenalty_symmetric weight)
    (fun x => (mul_nonneg hg.le (sq_nonneg ‖x‖)).trans (hgap x))
    hgap hT hB hD (hubbardLowUnit m) (hubbardLowUnit_norm m)

end ContinuumCoulomb

end

end OAI
