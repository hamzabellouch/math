import OAI.GroupTheory.PolycyclicRecognition.Algebra.NegativeRayDescent
import Mathlib.Algebra.Group.Submonoid.Membership

namespace OAI

/-! # Bounded representatives along an integral negative ray -/

noncomputable section
namespace PolycyclicRecognition
open scoped InnerProductSpace
variable {Q E : Type} [CommGroup Q] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rayLatticeHeight (e : Q →* Multiplicative E) (t q : Q) : ℕ :=
  ⌈‖negativeRayResidual (e t).toAdd (e q).toAdd‖ ^ 2⌉₊

theorem bounded_ray_layer_representatives (e : Q →* Multiplicative E) (t : Q)
    (hbounded : ∀ R : ℝ, Set.Finite {q : Q | ‖(e q).toAdd‖ ≤ R}) (D : ℕ) :
    ∃ B : Finset Q, ∀ q, rayLatticeHeight e t q ≤ D →
      ∃ b ∈ B, ∃ u : Submonoid.powers t⁻¹, (u : Q) * b = q := by
  classical
  let R := (D : ℝ) + 1 + ‖(e t).toAdd‖
  let B := (hbounded R).toFinset
  refine ⟨B, ?_⟩
  intro q hq
  let c := negativeRayCoefficient (e t).toAdd (e q).toAdd
  let n := ⌊-c⌋₊
  have hc : c ≤ 0 := negativeRayCoefficient_nonpos _ _
  have hcn : |c + (n : ℝ)| ≤ 1 := by
    have h := Nat.abs_sub_floor_le (show 0 ≤ -c by linarith)
    have he : -c - (⌊-c⌋₊ : ℝ) = -(c + (n : ℝ)) := by dsimp [n]; ring
    rw [he, abs_neg] at h
    exact h
  have hsq : ‖negativeRayResidual (e t).toAdd (e q).toAdd‖ ^ 2 ≤ (D : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hq)
  have hnorm : ‖negativeRayResidual (e t).toAdd (e q).toAdd‖ ≤ (D : ℝ) + 1 := by
    have hn := norm_nonneg (negativeRayResidual (e t).toAdd (e q).toAdd)
    have hd : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
    nlinarith [sq_nonneg (D : ℝ)]
  have he : (e (q * t ^ n)).toAdd =
      negativeRayResidual (e t).toAdd (e q).toAdd +
        (c + (n : ℝ)) • (e t).toAdd := by
    rw [map_mul, toAdd_mul, map_pow, toAdd_pow,
      ← Nat.cast_smul_eq_nsmul ℝ]
    dsimp [negativeRayResidual, c]
    module
  have hb : q * t ^ n ∈ B := by
    change q * t ^ n ∈ (hbounded R).toFinset
    rw [Set.Finite.mem_toFinset]
    change ‖(e (q * t ^ n)).toAdd‖ ≤ R
    rw [he]
    calc
      _ ≤ ‖negativeRayResidual (e t).toAdd (e q).toAdd‖ +
          ‖(c + (n : ℝ)) • (e t).toAdd‖ := norm_add_le _ _
      _ ≤ ((D : ℝ) + 1) + ‖(e t).toAdd‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add hnorm (by simpa using
          mul_le_mul_of_nonneg_right hcn (norm_nonneg (e t).toAdd))
      _ = R := rfl
  refine ⟨q * t ^ n, hb, ⟨t⁻¹ ^ n, ⟨n, rfl⟩⟩, ?_⟩
  simp [inv_pow, mul_comm]

end PolycyclicRecognition

end

end OAI
