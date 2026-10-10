import OAI.Analysis.MarkovType.FinitelyRepresentable

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure TriangularSystem (n : ℕ) (θ : ℝ) where
  vectors : Fin n → X
  functionals : Fin n → StrongDual ℝ X
  vectors_bound : ∀ i, ‖vectors i‖ ≤ 1
  functionals_bound : ∀ j, ‖functionals j‖ ≤ 1
  pairing : ∀ i j, functionals j (vectors i) = if j ≤ i then θ else 0

def FiniteTriangularObstruction : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ n : ℕ, 0 < n ∧ ¬ Nonempty (TriangularSystem X n θ)

variable {X}

namespace TriangularSystem

variable {n m : ℕ} {θ : ℝ}

def restrict (s : TriangularSystem X n θ) (h : m ≤ n) : TriangularSystem X m θ where
  vectors i := s.vectors (Fin.castLE h i)
  functionals j := s.functionals (Fin.castLE h j)
  vectors_bound i := s.vectors_bound (Fin.castLE h i)
  functionals_bound j := s.functionals_bound (Fin.castLE h j)
  pairing i j := by
    have hle : (Fin.castLE h j ≤ Fin.castLE h i) ↔ j ≤ i := Iff.rfl
    simpa only [hle] using s.pairing (Fin.castLE h i) (Fin.castLE h j)

theorem abs_parameter_le_one (s : TriangularSystem X n θ) (hn : 0 < n) : |θ| ≤ 1 := by
  let i : Fin n := ⟨0, hn⟩
  have hpair : s.functionals i (s.vectors i) = θ := by simpa using s.pairing i i
  calc
    |θ| = ‖s.functionals i (s.vectors i)‖ := by rw [hpair, Real.norm_eq_abs]
    _ ≤ ‖s.functionals i‖ * ‖s.vectors i‖ := (s.functionals i).le_opNorm _
    _ ≤ 1 * 1 := mul_le_mul (s.functionals_bound i) (s.vectors_bound i)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem no_longer_of_no_shorter (h : m ≤ n)
    (hm : ¬ Nonempty (TriangularSystem X m θ)) :
    ¬ Nonempty (TriangularSystem X n θ) := by
  rintro ⟨s⟩
  exact hm ⟨s.restrict h⟩

end TriangularSystem

end MarkovSuperreflexivity

end OAI
