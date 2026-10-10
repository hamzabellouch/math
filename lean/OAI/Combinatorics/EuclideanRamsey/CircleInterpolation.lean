import OAI.Combinatorics.EuclideanRamsey.CircleGeometry

namespace OAI

/- The secant equations and quadratic isolators have coefficients in the coordinate field. -/
noncomputable section
namespace EuclideanRamsey.CircleConsequence

def secantRow {s : ℕ} (a : Fin s → Space 2) (i j : Fin s) :
    Option (Fin 2) → Coeff a
  | none => coordinate a i 0 * coordinate a j 1 - coordinate a j 0 * coordinate a i 1
  | some k => if k = 0 then coordinate a i 1 - coordinate a j 1
      else coordinate a j 0 - coordinate a i 0

def secantValue {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) : Coeff a :=
  (coordinate a j 0-coordinate a i 0)*(coordinate a k 1-coordinate a i 1) -
  (coordinate a j 1-coordinate a i 1)*(coordinate a k 0-coordinate a i 0)

theorem secantRow_eval {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) :
    (∑ α : Option (Fin 2), secantRow a i j α * augmented a k α) =
      secantValue a i j k := by
  simp [secantRow, secantValue, augmented, Fin.sum_univ_two]
  ring

def pairedSecantMatrix {s : ℕ} (a : Fin s → Space 2)
    (i j k l : Fin s) : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a) :=
  fun α β => secantRow a i j α * secantRow a k l β

theorem pairedSecantMatrix_eval {s : ℕ} (a : Fin s → Space 2)
    (i j k l m : Fin s) :
    (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
      pairedSecantMatrix a i j k l α β * augmented a m α * augmented a m β) =
      secantValue a i j m * secantValue a k l m := by
  rw [← secantRow_eval a i j m, ← secantRow_eval a k l m]
  rw [Finset.sum_mul]
  simp only [pairedSecantMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem pairedSecantMatrix_vanishes {s : ℕ} (a : Fin s → Space 2)
    (i j k l m : Fin s) (hm : m = i ∨ m = j ∨ m = k ∨ m = l) :
    (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
      pairedSecantMatrix a i j k l α β * augmented a m α * augmented a m β) = 0 := by
  rw [pairedSecantMatrix_eval]
  rcases hm with rfl | rfl | rfl | rfl <;> dsimp only [secantValue] <;> ring

/-- Nonzero evaluation follows from actual planar circle equations. -/
theorem secantValue_ne_zero {s : ℕ} (a : Fin s → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secantValue a i j k ≠ 0 := by
  have different (u v : Fin s) (huv : u ≠ v) :
      a u 0 ≠ a v 0 ∨ a u 1 ≠ a v 1 := by
    by_contra h
    push Not at h
    apply huv
    apply ha
    ext q
    fin_cases q <;> simp_all
  have h := secant_nonzero (a i 0) (a i 1) (a j 0) (a j 1)
    (a k 0) (a k 1) (c 0) (c 1) R (hc i) (hc j) (hc k)
    (different i j hij) (different i k hik) (different j k hjk)
  intro hz
  apply h
  have he := congrArg (fun z : Coeff a => (z : ℝ)) hz
  simpa [secantValue, coordinate] using he

/-- The five-point isolator is a concrete coordinate-field matrix.
The permutation is just a labeling, with e 0 the point being isolated. -/
theorem five_point_isolator (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (e : Equiv.Perm (Fin 5)) :
    ∃ M : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a),
      (∀ m, m ≠ e 0 →
        (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a m α * augmented a m β) = 0) ∧
      (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a (e 0) α * augmented a (e 0) β) ≠ 0 := by
  refine ⟨pairedSecantMatrix a (e 1) (e 2) (e 3) (e 4), ?_, ?_⟩
  · intro m hm
    apply pairedSecantMatrix_vanishes
    have hem : e (e.symm m) = m := e.apply_symm_apply m
    have hn : e.symm m ≠ 0 := by intro h; apply hm; simpa [h] using hem.symm
    generalize h : e.symm m = k at hem hn
    fin_cases k <;> simp_all
  · rw [pairedSecantMatrix_eval]
    apply mul_ne_zero
    · apply secantValue_ne_zero a ha c R hc <;> exact e.injective.ne (by decide)
    · apply secantValue_ne_zero a ha c R hc <;> exact e.injective.ne (by decide)

end EuclideanRamsey.CircleConsequence

end

end OAI
