import OAI.NumberTheory.TwoPoint.Bounds.AmbientLitOrigin

namespace OAI

/-! Choose the actual common origins for a finite numerical rank catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem ambient_tuple_lit_origins {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {R J : ℕ} {P : Fin J → Finset ℕ} (F : Finset α)
    (w : α → ColumnPrimeAssignment J R P)
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (label : α → Fin R × Fin J → ι)
    (hlabel : ∀ a ∈ F, ∀ i j, p (label a (i, j)) = (w a j i).val)
    (U : Finset (Fin R × Fin J)) (offset : α → Fin R → ℤ) (base : ι → Fin B)
    (perfect : Finset (Fin R)) (hperfect : ∀ a ∈ F, perfect ⊆ perfectRows (label a) U)
    (hL : ∀ a ∈ F, LitConsistent (nonsingletonSlots (label a) \ U) (label a)
      (fun t => forcedResidue B (p (label a t)) (hprime _).pos (hpB _) (offset a t.1))) :
    ∃ origin : α → ℤ, ∀ a ∈ F, ∀ i ∈ perfect, ∀ j,
      ((w a j i).val : ℤ) ∣ origin a + offset a i := by
  have he (a : α) : ∃ n : ℤ, a ∈ F → ∀ i ∈ perfect, ∀ j,
      ((w a j i).val : ℤ) ∣ n + offset a i := by
    by_cases ha : a ∈ F
    · obtain ⟨n, hn⟩ := ambient_tuple_lit_origin (w a) B p hprime hinj hpB (label a)
        (hlabel a ha) U (offset a) base perfect (hperfect a ha) (hL a ha)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose origin horigin using he
  exact ⟨origin, horigin⟩

end TwoPointCorrelations

end OAI
