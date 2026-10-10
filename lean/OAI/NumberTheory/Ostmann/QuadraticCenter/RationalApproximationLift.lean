import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterLiftBounds

namespace OAI

/-! # Turning the phase approximation into the common-center integer lift -/

namespace Ostmann

def approximationLift (a M : ℕ) (t b : ℤ) : ℤ := (a : ℤ) * t - b * M

theorem approximationLift_congruence (a M p : ℕ) (t b tp : ℤ)
    (hpM : p ∣ M) (ht : (p : ℤ) ∣ t - tp) :
    (p : ℤ) ∣ approximationLift a M t b - (a : ℤ) * tp := by
  have hpM' : (p : ℤ) ∣ (M : ℤ) := by exact_mod_cast hpM
  have h := dvd_sub (dvd_mul_of_dvd_right ht (a : ℤ)) (dvd_mul_of_dvd_right hpM' b)
  have heq : approximationLift a M t b - (a : ℤ) * tp =
      (a : ℤ) * (t - tp) - b * M := by
    unfold approximationLift
    ring
  rw [heq]
  exact h

theorem approximationLift_abs_bound (a M : ℕ) (hM : 0 < M) (t b : ℤ)
    (δ : ℝ) (happrox : |(a : ℝ) * ((t : ℝ) / M) - b| ≤ δ) :
    |(approximationLift a M t b : ℝ)| ≤ (M : ℝ) * δ := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : (approximationLift a M t b : ℝ) =
      (M : ℝ) * ((a : ℝ) * ((t : ℝ) / M) - b) := by
    dsimp [approximationLift]
    push_cast
    field_simp
  rw [heq, abs_mul, abs_of_pos hM0]
  exact mul_le_mul_of_nonneg_left happrox hM0.le

/-- The rational approximation supplies exactly the bounded integer and
the simultaneous congruences used by the lift-moment argument. -/
theorem approximationLift_tuple (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (a H : ℕ) (tM b : ℤ) (t : ℕ → ℤ)
    (δ : ℝ)
    (happrox : |(a : ℝ) * ((tM : ℝ) / primeTupleProduct P e) - b| ≤ δ)
    (hsize : (primeTupleProduct P e : ℝ) * δ ≤ H)
    (ht : ∀ i, ((e i).1 : ℤ) ∣ tM - t (e i).1) :
    ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
      ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  classical
  let n := approximationLift a (primeTupleProduct P e) tM b
  have hn : |n| ≤ (H : ℤ) := by
    have h := (approximationLift_abs_bound a (primeTupleProduct P e)
      (primeTupleProduct_pos P hprime e) tM b δ happrox).trans hsize
    exact_mod_cast h
  refine ⟨n, Finset.mem_Ico.mpr ?_, ?_⟩
  · obtain ⟨hlo, hhi⟩ := abs_le.mp hn
    constructor <;> omega
  · intro i
    apply approximationLift_congruence a (primeTupleProduct P e) (e i).1 tM b (t (e i).1)
    · exact Finset.dvd_prod_of_mem (fun j : Fin k => (e j).1) (Finset.mem_univ i)
    · exact ht i

end Ostmann

end OAI
