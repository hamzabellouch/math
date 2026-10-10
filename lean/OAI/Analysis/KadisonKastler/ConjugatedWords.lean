import OAI.Analysis.KadisonKastler.PrescribedTuples
import OAI.Analysis.KadisonKastler.PhaseCoefficients

namespace OAI

/-!
# Phase coefficients as sums of words in conjugated copies

Removing the first label gives an exact decomposition of a prescribed
multiset fibre. The phase-coefficient recursion is therefore precisely
the sum of interleaved projection words. A unitary moves every intervening
factor to the left and conjugates each projection by its remaining power.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private theorem prescribed_head_mem {r : ℕ} (s : Sym α (r + 1))
    (t : PrescribedLabelTuple s) : t.val 0 ∈ s := by
  apply Eq.mp (congrArg (fun m : Multiset α => t.val 0 ∈ m) t.property)
  exact List.mem_ofFn.mpr ⟨0, rfl⟩

omit [Fintype α] in
private theorem prescribed_tail {r : ℕ} (s : Sym α (r + 1))
    (t : PrescribedLabelTuple s) :
    (List.ofFn (Fin.tail t.val) : Multiset α) =
      (s.erase (t.val 0) (prescribed_head_mem s t) : Multiset α) := by
  have he : (t.val 0) ::ₘ (List.ofFn (Fin.tail t.val) : Multiset α) = s.val := by
    apply Eq.trans _ t.property
    rw [List.ofFn_succ]
    rfl
  calc
    _ = ((t.val 0) ::ₘ (List.ofFn (Fin.tail t.val) : Multiset α)).erase (t.val 0) :=
      (Multiset.erase_cons_head _ _).symm
    _ = s.val.erase (t.val 0) := congrArg (fun m : Multiset α => m.erase (t.val 0)) he
    _ = _ := rfl

/-- Splitting off the first position marks a label once, even when that
label occurs several times in the prescribed multiset. -/
def prescribedTupleHeadEquiv {r : ℕ} (s : Sym α (r + 1)) :
    PrescribedLabelTuple s ≃
      Σ a : {a : α // a ∈ s}, PrescribedLabelTuple (s.erase a.val a.property) where
  toFun t := ⟨⟨t.val 0, prescribed_head_mem s t⟩, ⟨Fin.tail t.val, prescribed_tail s t⟩⟩
  invFun t := ⟨Fin.cons t.1.val t.2.val, by
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, ← Multiset.cons_coe]
    rw [t.2.property]
    exact congrArg Subtype.val (Sym.cons_erase t.1.property)⟩
  left_inv t := by
    apply Subtype.ext
    exact Fin.cons_self_tail t.val
  right_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨f, hf⟩⟩
    rfl

/-- Exact head-and-tail reindexing, with no multiplicity factor. -/
theorem sum_prescribedTuple_head {B : Type*} [AddCommMonoid B] {r : ℕ}
    (s : Sym α (r + 1)) (f : (Fin (r + 1) → α) → B) :
    (∑ t : PrescribedLabelTuple s, f t.val) =
      ∑ a : {a : α // a ∈ s}, ∑ t : PrescribedLabelTuple (s.erase a.val a.property),
        f (Fin.cons a.val t.val) := by
  rw [← Fintype.sum_sigma']
  symm
  exact Fintype.sum_equiv (prescribedTupleHeadEquiv s).symm _ _ (fun _ => rfl)

section Algebra

variable {A : Type*} [Ring A]

/-- The word `e₀ v e₁ v ... v eᵣ₋₁`, with an empty-word convention. -/
def interleavedWord (e : α → A) (v : A) : (r : ℕ) → (Fin r → α) → A
  | 0, _ => 1
  | r + 1, t => e (t 0) * (if r = 0 then 1 else v) *
      interleavedWord e v r (Fin.tail t)

/-- Every phase coefficient is exactly the sum over its prescribed
multiset, including repeated labels. -/
theorem positivePhaseCoefficient_eq_sum_interleaved (e : α → A) (v : A)
    (r : ℕ) (s : Sym α r) :
    positivePhaseCoefficient e v r s =
      ∑ t : PrescribedLabelTuple s, interleavedWord e v r t.val := by
  induction r with
  | zero =>
    have hs : (s : Multiset α) = 0 := by
      rw [Sym.eq_nil_of_card_zero s]
      rfl
    let t : PrescribedLabelTuple s :=
      ⟨Fin.elim0, by simpa only [List.ofFn_zero, Multiset.coe_nil] using hs.symm⟩
    have hcard : Fintype.card (PrescribedLabelTuple s) = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨t, fun _ => Subsingleton.elim _ _⟩
    simp [positivePhaseCoefficient, interleavedWord, hcard]
  | succ r ih =>
    rw [positivePhaseCoefficient, sum_prescribedTuple_head]
    simp_rw [ih]
    simp only [mul_sum, interleavedWord, Fin.cons_zero, Fin.tail_cons]

variable [StarRing A]

def conjugatedCopy (e : α → A) (v : A) (n : ℕ) (a : α) : A :=
  star (v ^ n) * e a * v ^ n

/-- The `i`th letter is conjugated by the power remaining to its right. -/
def conjugatedProjectionWord (e : α → A) (v : A) {r : ℕ} (t : Fin r → α) : A :=
  (List.ofFn (fun i => conjugatedCopy e v (r - 1 - i.val) (t i))).prod

omit [Fintype α] [DecidableEq α] in
private theorem conjugatedProjectionWord_succ (e : α → A) (v : A) (r : ℕ)
    (t : Fin (r + 1) → α) :
    conjugatedProjectionWord e v t =
      conjugatedCopy e v r (t 0) * conjugatedProjectionWord e v (Fin.tail t) := by
  unfold conjugatedProjectionWord
  rw [List.ofFn_succ, List.prod_cons]
  simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [Fin.val_succ, Fin.tail]
  rw [show r - (i.val + 1) = r - 1 - i.val by omega]

omit [Fintype α] [DecidableEq α] in
/-- Moving the intervening unitary factors to the left produces words
in the conjugated copies, with no approximation. -/
theorem interleavedWord_eq_unitary_mul_conjugated (e : α → A) (v : A)
    (hv : v ∈ unitary A) (r : ℕ) (t : Fin r → α) :
    interleavedWord e v r t = v ^ (r - 1) * conjugatedProjectionWord e v t := by
  induction r with
  | zero => simp [interleavedWord, conjugatedProjectionWord]
  | succ r ih =>
    rw [interleavedWord, conjugatedProjectionWord_succ]
    cases r with
    | zero => simp [interleavedWord, conjugatedCopy, conjugatedProjectionWord]
    | succ n =>
      rw [ite_eq_right (by omega), ih]
      simp only [Nat.succ_sub_one, conjugatedCopy]
      have hvp : v ^ (n + 1) * star (v ^ (n + 1)) = 1 :=
        Unitary.mul_star_self_of_mem ((unitary A).pow_mem hv _)
      calc
        _ = e (t 0) * v ^ (n + 1) * conjugatedProjectionWord e v (Fin.tail t) := by
          simp only [pow_succ', mul_assoc]
        _ = _ := by simp only [← mul_assoc, hvp, one_mul]

theorem positivePhaseCoefficient_eq_unitary_mul_sum_conjugated (e : α → A) (v : A)
    (hv : v ∈ unitary A) (r : ℕ) (s : Sym α r) :
    positivePhaseCoefficient e v r s =
      v ^ (r - 1) * ∑ t : PrescribedLabelTuple s, conjugatedProjectionWord e v t.val := by
  rw [positivePhaseCoefficient_eq_sum_interleaved]
  simp_rw [interleavedWord_eq_unitary_mul_conjugated e v hv]
  rw [mul_sum]

end Algebra

section Norm

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- The coefficient has exactly the norm of the corresponding sum of
projection words in conjugated copies. -/
theorem norm_positivePhaseCoefficient_eq_sum_conjugated (e : α → A) (v : A)
    (hv : v ∈ unitary A) (r : ℕ) (s : Sym α r) :
    ‖positivePhaseCoefficient e v r s‖ =
      ‖∑ t : PrescribedLabelTuple s, conjugatedProjectionWord e v t.val‖ := by
  rw [positivePhaseCoefficient_eq_unitary_mul_sum_conjugated e v hv]
  exact CStarRing.norm_mem_unitary_mul _ ((unitary A).pow_mem hv _)

/-- The negative coefficient uses an adjoint and a unitary factor, so
its norm is exactly the positive coefficient norm. -/
theorem norm_negativePhaseCoefficient_eq_positive (e : α → A) (v : A)
    (hv : v ∈ unitary A) (r : ℕ) (s : Sym α r) :
    ‖negativePhaseCoefficient e v r s‖ = ‖positivePhaseCoefficient e v r s‖ := by
  rw [negativePhaseCoefficient, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hv), norm_star]

theorem norm_negativePhaseCoefficient_eq_sum_conjugated (e : α → A) (v : A)
    (hv : v ∈ unitary A) (r : ℕ) (s : Sym α r) :
    ‖negativePhaseCoefficient e v r s‖ =
      ‖∑ t : PrescribedLabelTuple s, conjugatedProjectionWord e v t.val‖ := by
  rw [norm_negativePhaseCoefficient_eq_positive e v hv]
  exact norm_positivePhaseCoefficient_eq_sum_conjugated e v hv r s

end Norm

end

end KadisonKastler

end OAI
