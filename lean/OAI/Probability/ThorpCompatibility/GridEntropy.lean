import Mathlib
import OAI.Probability.ThorpCompatibility.Model
import OAI.Probability.ThorpCompatibility.EntropyChain

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

noncomputable def colHistory {A D : ℕ} (k : Fin D) (i : Fin A) (a : Grid A D) :=
  Law.history (fun h : Fin A => fun b : Grid A D => b.2 k h) i a

noncomputable def priorCols {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D)
    (a : Grid A D) : Fin D → Option (Equiv.Perm (Fin A)) :=
  fun l => if e l < e k then some (a.2 l) else none

noncomputable def gridPast {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A)
    (a : Grid A D) := ((a.1, priorCols e k a), colHistory k i a)

lemma priorCols_eq_iff {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D)
    (a b : Grid A D) :
    priorCols e k a = priorCols e k b ↔ ∀ l, e l < e k → a.2 l = b.2 l := by
  constructor
  · intro h l hl
    have h' := congrFun h l
    simpa [priorCols, hl] using h'
  · intro h
    funext l
    by_cases hl : e l < e k <;> simp [priorCols, hl, h l]

namespace Law
lemma condEntropy_eq_of_fibers {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : Law α) (X : α → β) (Y : α → γ) (Z : α → δ)
    (h : ∀ a b, Y a = Y b ↔ Z a = Z b) :
    P.condEntropy X Y = P.condEntropy X Z := by
  unfold condEntropy
  rw [P.entropy_eq_of_fibers Y Z h,
    P.entropy_eq_of_fibers (fun a => (X a, Y a)) (fun a => (X a, Z a))
      (by intro a b; simp only [Prod.mk.injEq, h a b])]

lemma condEntropy_out_eq_of_fibers {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : Law α) (X : α → β) (V : α → δ) (Y : α → γ)
    (h : ∀ a b, X a = X b ↔ V a = V b) :
    P.condEntropy X Y = P.condEntropy V Y := by
  unfold condEntropy
  rw [P.entropy_eq_of_fibers (fun a => (X a, Y a)) (fun a => (V a, Y a))
      (by intro a b; simp only [Prod.mk.injEq, h a b])]
end Law

lemma grid_inner_chain {A D : ℕ} (Q : Law (Grid A D))
    (e : Equiv.Perm (Fin D)) (k : Fin D) :
    (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i) (gridPast e k i)) =
      Q.condEntropy (fun a => a.2 k) (fun a => (a.1, priorCols e k a)) := by
  rw [show (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i) (gridPast e k i)) =
      (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i)
        (fun a => ((a.1, priorCols e k a),
          Law.history (fun h : Fin A => fun b : Grid A D => b.2 k h) i a))) from rfl,
    Q.entropy_chain_history]
  apply Q.condEntropy_out_eq_of_fibers
  intro a b
  constructor
  · intro h
    exact Equiv.ext (congrFun h)
  · intro h
    simp [h]

lemma grid_base_chain {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) :
    (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i) (colHistory k i)) =
      (Q.map (fun a => a.2 k)).entropy := by
  change (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i)
      (Law.history (fun h : Fin A => fun b : Grid A D => b.2 k h) i)) = _
  rw [Q.entropy_chain]
  apply Q.entropy_eq_of_fibers
  intro a b
  constructor
  · intro h
    exact Equiv.ext (congrFun h)
  · intro h
    simp [h]

lemma priorCols_history_fibers {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D)
    (a b : Grid A D) : priorCols e k a = priorCols e k b ↔
      Law.history (fun t : Fin D => fun c : Grid A D => c.2 (e.symm t)) (e k) a =
      Law.history (fun t : Fin D => fun c : Grid A D => c.2 (e.symm t)) (e k) b := by
  rw [priorCols_eq_iff, Law.history_eq_iff]
  constructor
  · intro h t ht
    exact h (e.symm t) (by simpa using ht)
  · intro h l hl
    simpa using h (e l) hl

lemma grid_outer_chain {A D : ℕ} (Q : Law (Grid A D)) (e : Equiv.Perm (Fin D)) :
    (∑ k : Fin D, Q.condEntropy (fun a => a.2 k) (fun a => (a.1, priorCols e k a))) =
      Q.entropy - (Q.map Prod.fst).entropy := by
  have h (k : Fin D) :
      Q.condEntropy (fun a => a.2 k) (fun a => (a.1, priorCols e k a)) =
      Q.condEntropy (fun a => a.2 (e.symm (e k))) (fun a => (a.1,
        Law.history (fun t : Fin D => fun c : Grid A D => c.2 (e.symm t)) (e k) a)) := by
    simp only [e.symm_apply_apply]
    apply Q.condEntropy_eq_of_fibers
    intro a b
    simp only [Prod.mk.injEq, priorCols_history_fibers]
  simp_rw [h]
  rw [Fintype.sum_equiv e _
    (fun t => Q.condEntropy (fun a => a.2 (e.symm t)) (fun a => (a.1,
      Law.history (fun s : Fin D => fun c : Grid A D => c.2 (e.symm s)) t a)))
    (fun k => rfl)]
  rw [Q.entropy_chain_history]
  unfold Law.condEntropy
  congr 1
  have hf := Q.entropy_eq_of_fibers
    (fun a : Grid A D => ((fun k => a.2 (e.symm k)), a.1)) id (by
      intro a b
      simp only [Prod.mk.injEq, id_eq]
      constructor
      · rintro ⟨hc, hr⟩
        apply Prod.ext hr
        funext k
        simpa using congrFun hc (e k)
      · intro hab
        simp [hab])
  rw [hf, Q.entropy_map_injective id Function.injective_id]

lemma grid_comparison_sum {A D : ℕ} (Q : Law (Grid A D)) (e : Equiv.Perm (Fin D)) :
    (∑ k : Fin D, ∑ i : Fin A,
      (Q.condEntropy (fun a => a.2 k i) (colHistory k i) -
        Q.condEntropy (fun a => a.2 k i) (gridPast e k i))) =
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) -
        Q.entropy := by
  simp_rw [Finset.sum_sub_distrib, grid_inner_chain, grid_base_chain]
  rw [grid_outer_chain]
  ring

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI
