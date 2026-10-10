import OAI.Analysis.Pureness.GroupAlgebra.PowersProjectionEstimate
import OAI.Analysis.Pureness.Operators.UnitaryAverages
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped BigOperators
variable {B : Type*} [CStarAlgebra B]

theorem powers_unitaryAverage_bound {n : ℕ} (u : Fin n → unitary B) (p x : B)
    (hp : star p = p) (hn : ‖p‖ ≤ 1) (hcn : ‖1-p‖ ≤ 1)
    (hz : (1-p)*x*(1-p) = 0)
    (ho : ∀ i j, i ≠ j →
      ((u i : B)*p*star (u i : B))*((u j : B)*p*star (u j : B)) = 0) :
    ‖unitaryAverage u x‖ ≤ (n : ℝ)⁻¹*(2*Real.sqrt n*‖x‖) := by
  let e := fun i => Unitary.conjStarAlgAut ℂ B (u i)
  have he (i : Fin n) (a : B) : e i a = (u i : B)*a*star (u i : B) := rfl
  have hen (i : Fin n) (a : B) : ‖e i a‖ = ‖a‖ := by
    rw [he, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hb := powers_projection_sum_bound (fun i => e i p) (fun i => e i x) ‖x‖ (norm_nonneg _)
    (fun i => by rw [← map_star, hp]) (fun i j hij => ho i j hij)
    (fun i => (hen i p).le.trans hn)
    (fun i => by rw [← map_one (e i), ← map_sub, hen]; exact hcn)
    (fun i => (hen i x).le)
    (fun i => by rw [← map_one (e i), ← map_sub, ← map_mul, ← map_mul, hz, map_zero])
  calc
    _ = (n : ℝ)⁻¹ * ‖∑ i, e i x‖ := by
      simp only [unitaryAverage, ← he, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [Fintype.card_fin] using hb)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
end CuntzPureness

end

end OAI
