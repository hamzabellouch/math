import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.UltrafilterDiagonal

theorem depth {l : Filter ℕ} (hl : l≤atTop) (p : ℕ → ℕ → Prop)
    (hp : ∀ n, ∀ᶠ i in l, p n i) :
    ∃ d : ℕ → ℕ, Tendsto d l atTop ∧ ∀ i j, j<d i → p j i := by
  classical
  let d (i : ℕ) := Nat.findGreatest (fun n => ∀ j<n, p j i) i
  have hd (i : ℕ) : ∀ j<d i, p j i :=
    Nat.findGreatest_spec (P := fun n => ∀ j<n, p j i) (Nat.zero_le i) (by intro j hj; omega)
  refine ⟨d,?_,hd⟩
  apply tendsto_atTop.2
  intro n
  have hn : ∀ᶠ i in l, ∀ j<n, p j i := by
    simpa only [Finset.mem_range] using
      (eventually_all_finset (Finset.range n)).mpr (fun j _ => hp j)
  filter_upwards [hn,hl (eventually_ge_atTop n)] with i hi hin
  exact Nat.le_findGreatest hin hi

lemma nonprincipal_le_atTop (ω : Ultrafilter ℕ) (hω : ∀ n, ω≠pure n) :
    (ω : Filter ℕ)≤atTop := by
  rcases ω.le_cofinite_or_eq_pure with h|⟨n,hn⟩
  · exact h.trans_eq Nat.cofinite_eq_atTop
  · exact (hω n hn).elim

end Kadison.UltrafilterDiagonal

end

end
end

end OAI
