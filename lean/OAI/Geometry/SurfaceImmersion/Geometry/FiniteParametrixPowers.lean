import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrixSize

namespace OAI

/-! The initial residual already contains one small factor. Finite
improvement retains that factor in both residual and amplitude estimates. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.FiniteParametrix

lemma boundProfile_const_mul (L : ℕ) (K C : ℕ → ℝ) (a : ℝ) (j m : ℕ) :
    boundProfile L K (fun r => a * C r) j m = a * boundProfile L K C j m := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih => rw [boundProfile, ih, boundProfile]; ring

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem residual_bound_succ (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (L : ℕ) (K C : ℕ → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hK : ∀ m, 0 ≤ K m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ η * C m) (j m : ℕ) :
    p m (residual A S b z j) ≤ η ^ (j + 1) * boundProfile L K C j m := by
  have hh := residual_bound A S b z p L K (fun r => η * C r) hη hK hdef hinit j m
  rw [boundProfile_const_mul] at hh
  convert hh using 1
  rw [pow_succ]
  ring

theorem improve_sub_initial_small (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (q : ℕ → Seminorm ℝ E) (L : ℕ) (K C B : ℕ → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hK : ∀ m, 0 ≤ K m)
    (hC : ∀ m, 0 ≤ C m) (hB : ∀ m, 0 ≤ B m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hS : ∀ m f, q m (S f) ≤ B m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ η * C m) (j m : ℕ) :
    q m (improve A S b z j - z) ≤
      η * ∑ i ∈ Finset.range j, B m * boundProfile L K C i (m + L) := by
  have hh := improve_sub_initial_bound A S b z p q L K (fun r => η * C r) B
    hη hK hB hdef hS hinit j m
  apply hh.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [boundProfile_const_mul]
  calc
    _ = η * (B m * boundProfile L K C i (m + L)) * η ^ i := by ring
    _ ≤ η * (B m * boundProfile L K C i (m + L)) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hη hη1)
        (mul_nonneg hη (mul_nonneg (hB m) (boundProfile_nonneg hK hC i (m + L))))
    _ = _ := mul_one _

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
