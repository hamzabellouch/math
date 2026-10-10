import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNGeometry
import OAI.Combinatorics.Chromatic.Walls.HNRestrictionOrder

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ) (hc : ∀ i,0 < c i)
noncomputable def hnKeyLT (d e : I → ℕ) : Prop :=
  slope c η d < slope c η e ∨ slope c η d=slope c η e ∧ mass c d < mass c e
noncomputable def matrixPrefix {m n : ℕ} (q : Fin m → Fin n → I → ℕ) (k : ℕ) (j : Fin n) : I → ℕ :=
  ∑ i,if i.val < k then q i j else 0
omit [Fintype I] in
@[simp] lemma matrixPrefix_one {m n : ℕ} (q : Fin (m+1) → Fin n → I → ℕ) (j : Fin n) :
    matrixPrefix q 1 j=q 0 j := by
  simp [matrixPrefix]
omit [Fintype I] in
lemma matrixPrefix_succ {m n : ℕ} (q : Fin (m+1) → Fin n → I → ℕ) (k : ℕ) (j : Fin n) :
    matrixPrefix q (k+1) j=q 0 j+matrixPrefix (fun i=>q i.succ) k j := by
  simp only [matrixPrefix,Fin.sum_univ_succ,Fin.val_zero,Nat.zero_lt_succ,ite_true,Fin.val_succ,
    Nat.add_lt_add_iff_right]

structure HNSplitMatrix {m n : ℕ} (l : Fin m → I → ℕ) (r : Fin n → I → ℕ)
    (q : Fin m → Fin n → I → ℕ) : Prop where
  rowSum : ∀ i,∑ j,q i j=l i
  colSum : ∀ j,∑ i,q i j=r j
  prefixes : ∀ k j,mass η (matrixPrefix q k j) ≤ slope c η (r j)*mass c (matrixPrefix q k j)

lemma split_cell_le {m n : ℕ} {l : Fin m → I → ℕ} {r : Fin n → I → ℕ}
    {q : Fin m → Fin n → I → ℕ} (h : HNSplitMatrix c η l r q) (i : Fin m) (j : Fin n) : q i j ≤ r j := by
  rw [←h.colSum j]
  exact Finset.single_le_sum (f:=fun i=>q i j) (fun i _=>by exact zero_le) (Finset.mem_univ i)

include hc in
lemma split_first_row {m n : ℕ} {l : Fin (m+1) → I → ℕ} {r : Fin (n+1) → I → ℕ}
    {q : Fin (m+1) → Fin (n+1) → I → ℕ} (h : HNSplitMatrix c η l r q)
    (hl : l 0≠0) (hr : ∀ j,0 < j → slope c η (r j) < slope c η (r 0)) :
    hnKeyLT c η (l 0) (r 0) ∨
      (l 0=r 0 ∧ q 0 0=r 0 ∧ (∀ j,j≠0 → q 0 j=0) ∧ ∀ i,i≠0 → q i 0=0) := by
  have ht (j : Fin (n+1)) : slope c η (r j) ≤ slope c η (r 0) := by
    by_cases hj : j=0
    · rw [hj]
    · exact (hr j (Fin.pos_iff_ne_zero.mpr hj)).le
  have hp (j : Fin (n+1)) : mass η (q 0 j) ≤ slope c η (r j)*mass c (q 0 j) := by
    simpa only [matrixPrefix_one] using h.prefixes 1 j
  have hs := split_row_slope_le c η hc _ (q 0) r (l 0) hl (h.rowSum 0) ht hp
  rcases lt_or_eq_of_le hs with hs|hs
  · exact Or.inl (Or.inl hs)
  obtain ⟨hd,hz⟩:=split_row_max_single c η hc 0 (q 0) r (l 0) (h.rowSum 0) hs
    (fun j hj=>hr j (Fin.pos_iff_ne_zero.mpr hj)) hp
  have hle : l 0 ≤ r 0 := hd ▸ split_cell_le c η h 0 0
  have hm := mass_mono c hc hle
  rcases lt_or_eq_of_le hm with hm|hm
  · exact Or.inl (Or.inr ⟨hs,hm⟩)
  have he := mass_eq_of_le c hc hle hm
  refine Or.inr ⟨he,hd.trans he,hz,?_⟩
  intro i hi
  have hsum : (∑ b : Fin m,q b.succ 0)=0 := by
    have hh:=h.colSum 0
    rw [Fin.sum_univ_succ,hd,he] at hh
    exact add_eq_left.mp hh
  obtain ⟨b,rfl⟩:=Fin.eq_succ_of_ne_zero hi
  exact (Finset.sum_eq_zero_iff).mp hsum b (Finset.mem_univ b)

lemma split_tail {m n : ℕ} {l : Fin (m+1) → I → ℕ} {r : Fin (n+1) → I → ℕ}
    {q : Fin (m+1) → Fin (n+1) → I → ℕ} (h : HNSplitMatrix c η l r q)
    (hrow : ∀ j,j≠0 → q 0 j=0) (hcol : ∀ i,i≠0 → q i 0=0) :
    HNSplitMatrix c η (fun i=>l i.succ) (fun j=>r j.succ) (fun i j=>q i.succ j.succ) where
  rowSum i := by simpa only [Fin.sum_univ_succ,hcol i.succ (Fin.succ_ne_zero _),zero_add] using h.rowSum i.succ
  colSum j := by simpa only [Fin.sum_univ_succ,hrow j.succ (Fin.succ_ne_zero _),zero_add] using h.colSum j.succ
  prefixes k j := by
    have hh:=h.prefixes (k+1) j.succ
    simp only [matrixPrefix,Fin.sum_univ_succ,Fin.val_zero,Nat.zero_lt_succ,ite_true,Fin.val_succ,
      Nat.add_lt_add_iff_right,hrow j.succ (Fin.succ_ne_zero _),zero_add] at hh
    simpa only [matrixPrefix] using hh

include hc in

theorem hn_split_triangular {m n : ℕ} (l : Fin m → I → ℕ) (r : Fin n → I → ℕ)
    (q : Fin m → Fin n → I → ℕ) (h : HNSplitMatrix c η l r q)
    (hl : ∀ i,l i≠0) (hr : ∀ j,r j≠0)
    (ho : ∀ j k,j < k → slope c η (r k) < slope c η (r j)) :
    List.Lex (hnKeyLT c η) (List.ofFn l) (List.ofFn r) ∨ List.ofFn l=List.ofFn r := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact Or.inr (by simp)
    | succ n =>
      have hh := h.colSum 0
      simp only [Finset.univ_eq_empty,Finset.sum_empty] at hh
      exact (hr 0 hh.symm).elim
  | succ m ih =>
    cases n with
    | zero =>
      have hh:=h.rowSum 0
      simp only [Finset.univ_eq_empty,Finset.sum_empty] at hh
      exact (hl 0 hh.symm).elim
    | succ n =>
      rcases split_first_row c η hc h (hl 0) (fun j hj=>ho 0 j hj) with hk|⟨he,_,hrow,hcol⟩
      · exact Or.inl (by simpa only [List.ofFn_succ] using List.Lex.rel hk)
      obtain htail|htail:=ih (fun i=>l i.succ) (fun j=>r j.succ) (fun i j=>q i.succ j.succ)
        (split_tail c η h hrow hcol) (fun i=>hl i.succ) (fun j=>hr j.succ)
        (fun j k hjk=>ho j.succ k.succ (Fin.succ_lt_succ_iff.mpr hjk))
      · exact Or.inl (by simpa only [List.ofFn_succ,he] using List.Lex.cons htail)
      · exact Or.inr (by simp only [List.ofFn_succ,he,htail])
end ElementaryPositivity.SlopeArithmetic

end
section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ) (hc : ∀ i,0<c i)
include hc
omit hc in
lemma list_mass_bound (θ : ℝ) (l : List (I → ℕ))
    (h : ∀ d∈l,mass η d ≤ θ*mass c d) : mass η l.sum ≤ θ*mass c l.sum := by
  induction l with
  | nil => simp [mass]
  | cons d l ih =>
    simp only [List.sum_cons,mass_add,mul_add]
    exact add_le_add (h d (by simp)) (ih (fun e he=>h e (by simp [he])))
lemma list_slope_le (θ : ℝ) (l : List (I → ℕ)) (hn : l.sum≠0)
    (h : ∀ d∈l,slope c η d ≤ θ) : slope c η l.sum ≤ θ := by
  apply (div_le_iff₀ (mass_pos c hc _ hn)).mpr
  apply list_mass_bound c η θ l
  intro d hd
  rw [mass_eq c η hc d]
  exact mul_le_mul_of_nonneg_right (h d hd) (mass_nonneg c (fun i=>(hc i).le) d)
omit hc [Fintype I] in
lemma list_sum_ne_zero {l : List (I → ℕ)} (hn : ∀ d∈l,d≠0) (hl : l≠[]) : l.sum≠0 := by
  obtain ⟨d,l,rfl⟩:=List.exists_cons_of_ne_nil hl
  exact add_ne_zero_left d l.sum (hn d (by simp))
lemma ordered_sum_le_head {d : I → ℕ} {l : List (I → ℕ)} (h : HNOrdered c η (d::l)) :
    slope c η (d::l).sum ≤ slope c η d := by
  apply list_slope_le c η hc
  · exact list_sum_ne_zero h.1 (by simp)
  · intro e he
    rcases List.mem_cons.mp he with rfl|he
    · rfl
    · exact ((List.pairwise_cons.mp h.2).1 e he).le
lemma ordered_tail_lt_head {d : I → ℕ} {l : List (I → ℕ)} (h : HNOrdered c η (d::l))
    (hl : l≠[]) : slope c η l.sum<slope c η d := by
  obtain ⟨e,l,rfl⟩:=List.exists_cons_of_ne_nil hl
  exact (ordered_sum_le_head c η hc ⟨fun x hx=>h.1 x (by simp [hx]),h.2.tail⟩).trans_lt
    ((List.pairwise_cons.mp h.2).1 e (by simp))

omit hc in
lemma exists_uniform_cutoff (d : I → ℕ) (θ : ℝ) :
    ∃ κ : ℝ, κ<θ ∧ ∀ e : I → ℕ,e ≤ d → e≠0 → slope c η e<θ → slope c η e ≤ κ := by
  classical
  let E : Set (I → ℕ) := {e | e ≤ d ∧ e≠0 ∧ slope c η e<θ}
  have hE : E.Finite := (Set.finite_Iic d).subset (fun _ h=>h.1)
  by_cases hn : E.Nonempty
  · obtain ⟨e,he,hm⟩:=Set.exists_max_image E (slope c η) hE hn
    exact ⟨slope c η e,he.2.2,fun f hf hz hs=>hm f ⟨hf,hz,hs⟩⟩
  · refine ⟨θ-1,by linarith,?_⟩
    intro e hd he hs
    exact (hn ⟨e,hd,he,hs⟩).elim
end ElementaryPositivity.SlopeArithmetic

end

end OAI
