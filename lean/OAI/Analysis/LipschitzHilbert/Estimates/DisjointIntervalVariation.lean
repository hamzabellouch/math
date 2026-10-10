import OAI.Analysis.LipschitzHilbert.Estimates.IntervalOscillation
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Reorder an actual finite family of disjoint residual intervals before
applying the common cubic variation bound. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- Positive-length disjoint intervals can be sorted by their actual
starting indices. Their number is bounded by the finite horizon. -/
theorem disjoint_intervalOscillation_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, intervalOscillation F N (a i) (b i) ^ 3) ≤
      finiteCubicVariation (fun n => F (min n N)) (2 * N) := by
  classical
  have hinj : Function.Injective a := by
    intro i j heq
    by_contra hne
    rcases hdisjoint i j hne with h | h
    · have hi := hab i
      omega
    · have hj := hab j
      omega
  let index : ι → Fin N := fun i => ⟨a i, (hab i).trans_le (hb i)⟩
  have hiinj : Function.Injective index := by
    intro i j hij
    apply hinj
    exact congrArg Fin.val hij
  have hcard : Fintype.card ι ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective index hiinj
  let : LinearOrder ι := LinearOrder.lift' a hinj
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have horder (i j : Fin (Fintype.card ι)) (hij : i < j) : b (e i) ≤ a (e j) := by
    have hlt : a (e i) < a (e j) := e.strictMono hij
    rcases hdisjoint (e i) (e j) (e.injective.ne hij.ne) with h | h
    · exact h
    · have hj := hab (e j)
      omega
  have h := intervalOscillation_cube_sum F N (Fintype.card ι)
    (fun i => a (e i)) (fun i => b (e i)) hcard (fun i => (hab (e i)).le)
    (fun i => hb (e i)) horder
  calc
    _ = ∑ i : Fin (Fintype.card ι), intervalOscillation F N (a (e i)) (b (e i)) ^ 3 :=
      (e.toEquiv.sum_comp (fun i => intervalOscillation F N (a i) (b i) ^ 3)).symm
    _ ≤ _ := h

end LipschitzHilbert

end

end OAI
