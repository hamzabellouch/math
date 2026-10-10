import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorWholeFutureEntropy

namespace OAI

/-! # Finite predecessor words encode the same past as the countable observation -/

noncomputable section
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Given the terminal symbol, the finite predecessor labels recover the
whole countable word, and conversely. -/
theorem predecessor_word_eq_iff {Y A : Type*} (T : Y → Y) (Q : Y → ℕ)
    (B : Y → A)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → A → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) (x y : Y) (ht : Q (T^[N] x)=Q (T^[N] y)) :
    orbitName T Q N x=orbitName T Q N y ↔
      orbitName T B N x=orbitName T B N y := by
  induction N with
  | zero =>
      constructor <;> intro _ <;> funext i <;> exact Fin.elim0 i
  | succ N ih =>
      rw [orbitName_eq_iff_last_initial,orbitName_eq_iff_last_initial]
      constructor
      · rintro ⟨hlast,hword⟩
        refine ⟨href _ _ hlast ?_,(ih hlast).mp hword⟩
        simpa only [Function.iterate_succ_apply'] using ht
      · rintro ⟨hlast,hword⟩
        have hq : Q (T^[N] x)=Q (T^[N] y) := by
          rw [←hdecode (T^[N] x),←hdecode (T^[N] y),hlast]
          congr 1
          simpa only [Function.iterate_succ_apply'] using ht
        exact ⟨hq,(ih hq).mpr hword⟩

end DukePrimeDegree

end

end OAI
