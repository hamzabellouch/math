import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedKernelSpatialScale_inverse_exp {τ P : ℝ}
    (hτ : 0 < τ) (hP : 0 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hτinv : τ⁻¹ ≤ Real.exp P) :
    8 * (1 + allocatedPhysicalRootBudget B U basis S (fun _ => 0)) /
      ((S.value : ℝ) * τ) ≤ Real.exp (2 * P + 4) := by
  have hratio := allocatedPhysicalRootBudget_zero_ratio B U basis S hP hvars
  rw [(allocatedPrimitiveRootRatio_bounds hP).1] at hratio
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
  have hcount : P + 1 ≤ Real.exp P := Real.add_one_le_exp P
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have he : Real.exp (4 : ℝ) = Real.exp 2 * Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith
  calc
    _ = 8 * ((1 + allocatedPhysicalRootBudget B U basis S (fun _ => 0)) /
      (S.value : ℝ)) * τ⁻¹ := by ring
    _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by
      apply mul_le_mul
      · exact mul_le_mul h8 (hratio.trans hcount) (by positivity) (Real.exp_nonneg _)
      · exact hτinv
      · exact inv_nonneg.mpr hτ.le
      · positivity
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
