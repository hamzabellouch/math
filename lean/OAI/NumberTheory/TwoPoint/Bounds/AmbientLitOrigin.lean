import OAI.NumberTheory.TwoPoint.Bounds.LitCommonOrigin
import OAI.NumberTheory.TwoPoint.Walks.TuplePerfectRows

namespace OAI

/-! Lit consistency in the full prime pool supplies the common tuple-column origins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem ambient_lit_common_origin {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (label : Fin R × Fin J → ι)
    (U : Finset (Fin R × Fin J)) (offset : Fin R → ℤ) (base : ι → Fin B)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t.1))) :
    ∃ n : ℤ, ∀ i ∈ perfectRows label U, ∀ j, (p (label (i, j)) : ℤ) ∣ n + offset i := by
  obtain ⟨n, hn⟩ := lit_consistency_common_origin B p hprime hinj hpB
    (nonsingletonSlots label \ U) label (fun t => offset t.1) base hL
  exact ⟨n, fun i hi j => hn (i, j) (perfectRows_lit label U i hi j)⟩

theorem ambient_tuple_lit_origin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R J : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val)
    (U : Finset (Fin R × Fin J)) (offset : Fin R → ℤ) (base : ι → Fin B)
    (perfect : Finset (Fin R)) (hperfect : perfect ⊆ perfectRows label U)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t.1))) :
    ∃ n : ℤ, ∀ i ∈ perfect, ∀ j, ((w j i).val : ℤ) ∣ n + offset i := by
  obtain ⟨n, hn⟩ := ambient_lit_common_origin B p hprime hinj hpB label U offset base hL
  refine ⟨n, ?_⟩
  intro i hi j
  simpa only [hlabel] using hn i (hperfect hi) j

end TwoPointCorrelations

end OAI
