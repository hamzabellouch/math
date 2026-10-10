import OAI.Analysis.KadisonKastler.FreeCuts

namespace OAI

/-! # Individual cuts of an ordered centered word -/

namespace KadisonKastler

open Finset

noncomputable section

variable {ι B : Type*} [Semiring B]

def noPreservationCut (C A : ι → B) : List ι → ℕ → B
  | [], 0 => 1
  | [], _ + 1 => 0
  | i :: l, 0 => A i * annihilationProduct A l
  | i :: l, k + 1 => C i * noPreservationCut C A l k

def preservationCut (C D A : ι → B) : List ι → ℕ → B
  | [], _ => 0
  | i :: l, 0 => D i * annihilationProduct A l
  | i :: l, k + 1 => C i * preservationCut C D A l k

theorem noPreservationCut_zero (C A : ι → B) (l : List ι) :
    noPreservationCut C A l 0 = annihilationProduct A l := by
  cases l <;> rfl

/-- Cutting between two subwords leaves exactly the creation prefix and
the annihilation suffix, in their original order. -/
theorem noPreservationCut_append (C A : ι → B) (l₁ l₂ : List ι) :
    noPreservationCut C A (l₁ ++ l₂) l₁.length =
      (l₁.map C).prod * annihilationProduct A l₂ := by
  induction l₁ with
  | nil => simp [noPreservationCut_zero]
  | cons i l ih =>
    simp only [List.cons_append, List.length_cons, noPreservationCut,
      List.map_cons, List.prod_cons, ih, mul_assoc]

theorem preservationCut_append (C D A : ι → B) (l₁ l₂ : List ι) (i : ι) :
    preservationCut C D A (l₁ ++ i :: l₂) l₁.length =
      (l₁.map C).prod * D i * annihilationProduct A l₂ := by
  induction l₁ with
  | nil => simp [preservationCut]
  | cons j l ih =>
    simp only [List.cons_append, List.length_cons, preservationCut,
      List.map_cons, List.prod_cons, ih, mul_assoc]

/-- There are `n+1` cuts without preservation and `n` with preservation. -/
theorem freeCutSum_eq_indexedCuts (C D A : ι → B) (l : List ι) :
    freeCutSum C D A l =
      (∑ k ∈ range (l.length + 1), noPreservationCut C A l k) +
      ∑ k ∈ range l.length, preservationCut C D A l k := by
  induction l with
  | nil => simp [freeCutSum, noPreservationCut]
  | cons i l ih =>
    have hn : (∑ k ∈ range (l.length + 2), noPreservationCut C A (i :: l) k) =
        A i * annihilationProduct A l +
          C i * ∑ k ∈ range (l.length + 1), noPreservationCut C A l k := by
      rw [sum_range_succ']
      simp only [noPreservationCut, ← mul_sum]
      exact add_comm _ _
    have hp : (∑ k ∈ range (l.length + 1), preservationCut C D A (i :: l) k) =
        D i * annihilationProduct A l + C i * ∑ k ∈ range l.length, preservationCut C D A l k := by
      rw [sum_range_succ']
      simp only [preservationCut, ← mul_sum]
      exact add_comm _ _
    simp only [List.length_cons, Nat.add_assoc, hn, hp, freeCutSum, ih, mul_add]
    ac_rfl

theorem centeredLetterProduct_eq_indexedCuts (C D A : ι → B)
    (hAC : ∀ i j, i ≠ j → A i * C j = 0)
    (hAD : ∀ i j, i ≠ j → A i * D j = 0)
    (hDC : ∀ i j, i ≠ j → D i * C j = 0)
    (hDD : ∀ i j, i ≠ j → D i * D j = 0)
    (l : List ι) (hl : l.Nodup) :
    centeredLetterProduct C D A l =
      (∑ k ∈ range (l.length + 1), noPreservationCut C A l k) +
      ∑ k ∈ range l.length, preservationCut C D A l k := by
  rw [centeredLetterProduct_eq_freeCutSum C D A hAC hAD hDC hDD l hl,
    freeCutSum_eq_indexedCuts]

end

end KadisonKastler

end OAI
