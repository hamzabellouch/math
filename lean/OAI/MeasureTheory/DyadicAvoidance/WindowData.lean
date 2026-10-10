import Mathlib

namespace OAI

noncomputable section

namespace Problem310

/-- An edge is identified with the nonempty path to its child. -/
def ValidWindowEdge {q : ℕ} (d : ℕ) (P : List (Fin q)) : Prop :=
  P ≠ [] ∧ P.length ≤ d

/-- Deterministic window interface shared by the finite router and its
geometric/probabilistic estimates. `q` is the TOTAL number of children.
Only the two ordering comparisons actually used by routing are required;
a preorder construction can supply them from its general rank gap bound. -/
structure WindowData (q d g r₀ : ℕ) where
  r : ℕ → ℕ
  a : List (Fin q) → ℕ
  b : List (Fin q) → ℕ
  bstar : List (Fin q) → ℕ
  length_pos : ∀ P : List (Fin q), ValidWindowEdge d P → 1 ≤ r (d + 1 - P.length)
  length_threshold : ∀ P : List (Fin q), ValidWindowEdge d P → r₀ ≤ r (d + 1 - P.length)
  start_three : ∀ P, ValidWindowEdge d P → 3 ≤ a P
  endpoint : ∀ P, ValidWindowEdge d P →
    b P + 1 = a P + r (d + 1 - P.length)
  gap_prefix : ∀ P Q, ValidWindowEdge d P → ValidWindowEdge d Q →
    P.IsPrefix Q → P ≠ Q → b P + g < a Q
  gap_sibling : ∀ (P : List (Fin q)) (i j : Fin q) (tail : List (Fin q)),
    i < j → ValidWindowEdge d (P ++ [i]) → ValidWindowEdge d (P ++ j :: tail) →
      b (P ++ [i]) + g < a (P ++ j :: tail)
  descendant_bounds : ∀ P Q, ValidWindowEdge d P → ValidWindowEdge d Q →
    P.IsPrefix Q → b P ≤ b Q ∧ b Q ≤ bstar P
  padding : ∀ P, ValidWindowEdge d P →
    bstar P + 1 ≤ a P + 2 * r (d + 1 - P.length)

namespace WindowData

variable {q d g r₀ : ℕ} (W : WindowData q d g r₀)

abbrev length (P : List (Fin q)) : ℕ := W.r (d + 1 - P.length)

def window (P : List (Fin q)) : Finset ℕ := Finset.Icc (W.a P) (W.b P)

def testIndex (P : List (Fin q)) (k : Fin (W.length P)) : ℕ := W.a P + k.val

lemma start_le_end (P : List (Fin q)) (hP : ValidWindowEdge d P) : W.a P ≤ W.b P := by
  have hlen := W.length_pos P hP
  have hend := W.endpoint P hP
  omega

lemma card_window (P : List (Fin q)) (hP : ValidWindowEdge d P) :
    (W.window P).card = W.length P := by
  rw [window, Nat.card_Icc]
  have hend := W.endpoint P hP
  dsimp [length]
  omega

lemma testIndex_mem (P : List (Fin q)) (hP : ValidWindowEdge d P)
    (k : Fin (W.length P)) : W.testIndex P k ∈ W.window P := by
  apply Finset.mem_Icc.mpr
  have hend := W.endpoint P hP
  have hk := k.isLt
  dsimp [testIndex, length] at *
  omega

lemma testIndex_three (P : List (Fin q)) (hP : ValidWindowEdge d P)
    (k : Fin (W.length P)) : 3 ≤ W.testIndex P k := by
  have hstart := W.start_three P hP
  dsimp [testIndex]
  omega

lemma testIndex_injective (P : List (Fin q)) : Function.Injective (W.testIndex P) := by
  intro i j h
  apply Fin.ext
  dsimp [testIndex] at h
  omega

/-- Every tested point sees at most `2*r+2` finest-grid exponent levels. -/
lemma testIndex_padding (P : List (Fin q)) (hP : ValidWindowEdge d P)
    (k : Fin (W.length P)) :
    W.bstar P + 2 ≤ W.testIndex P k + (2 * W.length P + 2) := by
  have hpad := W.padding P hP
  dsimp [testIndex, length]
  omega

/-- The global finite-index set may include every edge window. -/
def indices : Set ℕ := {n | ∃ P : List (Fin q), ValidWindowEdge d P ∧ n ∈ W.window P}

lemma indices_positive : ∀ n ∈ W.indices, 1 ≤ n := by
  rintro n ⟨P, hP, hn⟩
  have hstart := W.start_three P hP
  have hnlow := (Finset.mem_Icc.mp hn).1
  omega

end WindowData
end Problem310

end

end OAI
