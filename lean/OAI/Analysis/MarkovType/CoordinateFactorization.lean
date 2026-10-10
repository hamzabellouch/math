import OAI.Analysis.MarkovType.OrderedNorm
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem CoordinatesRepresentable.of_factorization (N : OrderedNorm)
    (p : Seminorm ℝ C00)
    (hNp : ∀ (m : ℕ) (η : ℝ), 0 < η →
      ∃ (k : ℕ) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ)), ∀ a,
        N (C00.ofArray a) ≤ p (C00.ofArray (A a)) ∧
          p (C00.ofArray (A a)) ≤ (1 + η) * N (C00.ofArray a))
    (hpY : ∀ (k : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin k → ℝ) →ₗ[ℝ] Y, ∀ b,
        p (C00.ofArray b) ≤ ‖T b‖ ∧
          ‖T b‖ ≤ (1 + η) * p (C00.ofArray b)) :
    CoordinatesRepresentable Y N := by
  intro m ε hε
  let δ : ℝ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  have hfactor : (1 + δ) * (1 + δ) ≤ 1 + ε := by
    have hsquare : δ * δ ≤ δ := by nlinarith
    nlinarith
  obtain ⟨k, A, hA⟩ := hNp m δ hδ
  obtain ⟨T, hT⟩ := hpY k δ hδ
  refine ⟨T.comp A, ?_⟩
  intro a
  constructor
  · exact (hA a).1.trans (hT (A a)).1
  · calc
      ‖(T.comp A) a‖ ≤ (1 + δ) * p (C00.ofArray (A a)) := (hT (A a)).2
      _ ≤ (1 + δ) * ((1 + δ) * N (C00.ofArray a)) :=
        mul_le_mul_of_nonneg_left (hA a).2 (by linarith)
      _ = ((1 + δ) * (1 + δ)) * N (C00.ofArray a) :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + ε) * N (C00.ofArray a) :=
        mul_le_mul_of_nonneg_right hfactor (N.nonneg _)

end MarkovSuperreflexivity

end OAI
