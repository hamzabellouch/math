import OAI.NumberTheory.Ostmann.Construction.InitialWordAtomIntervals
import OAI.NumberTheory.Ostmann.Construction.InitialWordExpectation

namespace OAI

/-! # The nonword interval guards already hold under the original prime law -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialWordTuple_cell_set {C : Type*} (k m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (b : Bool) (c : C) (i : Fin (s c)) :
    Fin.append (Fin.append Q R) (Fin.append Q R)
      (initialWordTupleEquiv k m s cell ⟨(b, some c), i⟩) = R (cell ⟨c, i⟩) := by
  cases b with
  | false =>
    change Fin.append (Fin.append Q R) (Fin.append Q R)
      ((cell ⟨c, i⟩).natAdd k |>.natAdd (k + m)) = _
    simp only [Fin.append_right]
  | true =>
    change Fin.append (Fin.append Q R) (Fin.append Q R)
      ((cell ⟨c, i⟩).natAdd k |>.castAdd (k + m)) = _
    simp only [Fin.append_left, Fin.append_right]

theorem initialWordPrior_cell_product_bounds {C : Type*} [Fintype C]
    (k m : ℕ) (s : C → ℕ) (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (lo hi : (Σ c, Fin (s c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → lo i ≤ q ∧ q ≤ hi i)
    (x : (Σ v : Bool × Option C, Fin (initialWordSize k s v.2)) → P)
    (hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv k m s cell i)) (x i)) ≠ 0) :
    ∀ (b : Bool) (c : C),
      (∏ i, lo ⟨c, i⟩) ≤ ∏ i, (x ⟨(b, some c), i⟩ : ℕ) ∧
      (∏ i, (x ⟨(b, some c), i⟩ : ℕ)) ≤ ∏ i, hi ⟨c, i⟩ := by
  intro b c
  have hs (i : Fin (s c)) : lo ⟨c, i⟩ ≤ (x ⟨(b, some c), i⟩ : ℕ) ∧
      (x ⟨(b, some c), i⟩ : ℕ) ≤ hi ⟨c, i⟩ := by
    apply hcell
    have hp := primeSubsetPrior_support P _ (x ⟨(b, some c), i⟩)
      ((Finset.prod_ne_zero_iff.mp hx) ⟨(b, some c), i⟩ (Finset.mem_univ _))
    simpa only [initialWordTuple_cell_set] using hp
  exact ⟨Finset.prod_le_prod (fun i _ => (hs i).1),
    Finset.prod_le_prod (fun i _ => (hs i).2)⟩

theorem initialWordPrior_atomIntervals_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole)
    (k m j : ℕ) (s : C → ℕ) (cell : (Σ c, Fin (s c)) ≃ Fin m)
    (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (lo hi : (Σ c, Fin (s c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → lo i ≤ q ∧ q ≤ hi i)
    (x : (Σ v : Bool × Option C, Fin (initialWordSize k s v.2)) → P)
    (hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv k m s cell i)) (x i)) ≠ 0) :
    (∀ r ∈ atomIntervalRanges role
      (initialWordAtomLower j (fun c => ∏ i, lo ⟨c, i⟩))
      (initialWordAtomUpper j (fun c => ∏ i, hi ⟨c, i⟩)) 0,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) ↔
    ∀ r ∈ initialWordBinRanges role j,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) :=
  initialWordAtomIntervals_equiv role j _ _ _
    (initialWordPrior_cell_product_bounds k m s cell P Q R lo hi hcell x hx)

end Ostmann

end OAI
