import Mathlib

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def improve (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) : ℕ → E
  | 0 => z
  | j + 1 => improve A S b z j - S (A (improve A S b z j) - b)

def residual (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) : F :=
  A (improve A S b z j) - b

def defect (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) : F →ₗ[ℝ] F :=
  A.comp S - LinearMap.id

lemma residual_succ (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) :
    residual A S b z (j + 1) = -defect A S (residual A S b z j) := by
  simp only [residual, improve, map_sub, defect, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.id_apply]
  abel

lemma improve_difference (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) :
    improve A S b z (j + 1) - improve A S b z j = -S (residual A S b z j) := by
  simp only [improve, residual]
  abel

def boundProfile (L : ℕ) (K C : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => C m
  | j + 1, m => K m * boundProfile L K C j (m + L)

lemma boundProfile_nonneg {L : ℕ} {K C : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (hC : ∀ m, 0 ≤ C m) (j m : ℕ) :
    0 ≤ boundProfile L K C j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih => exact mul_nonneg (hK m) (ih (m + L))

/-- Each finite correction gains one small factor while paying only the
stated finite number of additional input derivatives. -/
theorem residual_bound (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (L : ℕ) (K C : ℕ → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hK : ∀ m, 0 ≤ K m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ C m) (j m : ℕ) :
    p m (residual A S b z j) ≤ η ^ j * boundProfile L K C j m := by
  induction j generalizing m with
  | zero => simpa only [residual, improve, boundProfile, pow_zero, one_mul] using hinit m
  | succ j ih =>
    rw [residual_succ, map_neg_eq_map]
    calc
      _ ≤ η * K m * p (m + L) (residual A S b z j) := hdef m _
      _ ≤ η * K m * (η ^ j * boundProfile L K C j (m + L)) :=
        mul_le_mul_of_nonneg_left (ih (m + L)) (mul_nonneg hη (hK m))
      _ = _ := by simp only [boundProfile, pow_succ]; ring

/-- The corrections inherit the size and derivative loss of the initial
parametrix, with the improved residual as forcing. -/
theorem increment_bound (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (q : ℕ → Seminorm ℝ E) (L : ℕ) (K C B : ℕ → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ m, 0 ≤ K m) (hB : ∀ m, 0 ≤ B m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hS : ∀ m f, q m (S f) ≤ B m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ C m) (j m : ℕ) :
    q m (improve A S b z (j + 1) - improve A S b z j) ≤
      B m * η ^ j * boundProfile L K C j (m + L) := by
  rw [improve_difference, map_neg_eq_map]
  calc
    _ ≤ B m * p (m + L) (residual A S b z j) := hS m _
    _ ≤ B m * (η ^ j * boundProfile L K C j (m + L)) :=
      mul_le_mul_of_nonneg_left (residual_bound A S b z p L K C hη hK hdef hinit j (m + L)) (hB m)
    _ = _ := by ring

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
