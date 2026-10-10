import OAI.Combinatorics.EditApproximation.Coarse.CoarseRootExecution
import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- The empty case is unreachable for the dyadic guess list. The fallback
is its already computed first entry, so no coarse call is repeated. -/


private theorem rationalMinimum_lower (fallback : ℚ) (values : List ℚ) (z : ℚ)
    (hf : z ≤ fallback) (hv : ∀ a ∈ values, z ≤ a) : z ≤ rationalMinimum fallback values := by
  induction values with
  | nil => exact hf
  | cons a rest ih =>
    exact le_min (hv a List.mem_cons_self)
      (ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)))

private theorem rationalMinimum_le_mem (fallback : ℚ) (values : List ℚ) (z : ℚ)
    (hz : z ∈ values) : rationalMinimum fallback values ≤ z := by
  induction values with
  | nil => cases hz
  | cons a rest ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hz)

private theorem rationalMinimum_le_fallback (fallback : ℚ) (values : List ℚ) :
    rationalMinimum fallback values ≤ fallback := by
  induction values with
  | nil => exact le_rfl
  | cons a rest ih => exact (min_le_right _ _).trans ih

 theorem coarseMinimumWithWork_ofFn {n : ℕ} [NeZero n] (f : Fin n → BinaryFraction) :
    (coarseMinimumWithWork (List.ofFn f)).1.value =
      Finset.univ.inf' Finset.univ_nonempty (fun i => (f i).value) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hne : List.ofFn f ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at this
    omega
  obtain ⟨a, rest, heq⟩ := List.exists_cons_of_ne_nil hne
  rw [heq, coarseMinimumWithWork, minimumWithWork_value]
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    have hm : f i ∈ a :: rest := heq ▸ List.mem_ofFn.mpr ⟨i, rfl⟩
    rcases List.mem_cons.mp hm with h | h
    · rw [h]
      exact rationalMinimum_le_fallback _ _
    · exact rationalMinimum_le_mem _ _ _ (List.mem_map.mpr ⟨f i, h, rfl⟩)
  · apply rationalMinimum_lower
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp (heq.symm ▸ List.mem_cons_self (a := a) (l := rest))
      rw [← hi]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    · intro z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp (heq.symm ▸ List.mem_cons_of_mem a hb)
      rw [← hi]
      exact Finset.inf'_le _ (Finset.mem_univ i)

/-- A candidate executes the whole root recurrence, then adds its literal
guess and doubles the result using Boolean arithmetic. -/
def coarseCandidateWithWork {B d : ℕ} {α : Type*} [DecidableEq α]
    (q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    BinaryFraction × ℕ :=
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseRootWithWork k q L hB hq hL
    (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
    (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
  let shifted := canonicalAddWithWork root.1 (nat k)
  let doubled := canonicalMulWithWork (nat 2) shifted.1
  (doubled.1, root.2 + shifted.2 + doubled.2 + Nat.size k + 3)

 theorem coarseCandidateWithWork_value {B d : ℕ} {α : Type*} [DecidableEq α]
    (q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    (coarseCandidateWithWork q L hB hq hL x y i draws).1.value =
      coarseInitialCandidate B d q (1 / L) x y i draws := by
  unfold coarseCandidateWithWork
  dsimp only
  rw [canonicalMulWithWork_value, canonicalAddWithWork_value, nat_value, nat_value,
    coarseRootWithWork_value]
  · rfl
  · unfold coarseGuess; positivity

end BinaryFraction
end EditApproximation

end OAI
