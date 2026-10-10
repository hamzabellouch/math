import Mathlib
import OAI.CategoryTheory.Thomason.PrismBasis

namespace OAI

/-! Ranked Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table

structure RankedAtoms (K : DirectedComplex.{u}) where
  Index : Type v
  finite : Fintype Index
  dim : Index → ℕ
  rank : Index → ℤ
  atom : Index → Table K
  bounded : ∀ b, truncate (dim b) false (atom b) = atom b
  coefficient : (b : Index) → (p : ℕ) → K.Chain p →+ ℤ
  homogeneous : ∀ b p x, coefficient b p x ≠ 0 → dim b = p
  ext : ∀ p (x y : K.Chain p), (∀ b, coefficient b p x = coefficient b p y) → x = y
  positive : ∀ p x, x ∈ K.positive p ↔ ∀ b, 0 ≤ coefficient b p x
  top : ∀ b c e, coefficient c (dim b) ((atom b).row (dim b) e) =
    (by classical exact if b = c then 1 else 0)
  ranked : ∀ b p, p < dim b → ∀ e c,
    coefficient c p ((atom b).row p e) ≠ 0 →
    if e then rank c < rank b else rank b < rank c

attribute [instance] RankedAtoms.finite
namespace RankedAtoms
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
open scoped Classical
include A
local instance rankedAtomsDecidableEq : DecidableEq A.Index := Classical.decEq _

def basis (p : ℕ) (b : A.Index) : K.Chain p :=
  if h : A.dim b = p then h ▸ (A.atom b).row (A.dim b) false else 0

lemma basis_own (b : A.Index) : A.basis (A.dim b) b = (A.atom b).row (A.dim b) false := by
  simp [basis]

lemma coefficient_basis (p : ℕ) (b c : A.Index) :
    A.coefficient c p (A.basis p b) =
      if A.dim b = p then (if b = c then 1 else 0) else 0 := by
  classical
  by_cases h : A.dim b = p
  · subst p
    rw [A.basis_own, A.top]
    simp
  · simp [basis,h]

lemma coefficient_eq_zero (b : A.Index) (p : ℕ) (x : K.Chain p) (h : A.dim b ≠ p) :
    A.coefficient b p x = 0 := by
  by_contra hn
  exact h (A.homogeneous b p x hn)

lemma expansion (p : ℕ) (x : K.Chain p) :
    ∑ b, A.coefficient b p x • A.basis p b = x := by
  classical
  apply A.ext p
  intro c
  rw [map_sum]
  simp only [map_zsmul, A.coefficient_basis]
  rw [Finset.sum_eq_single c]
  · by_cases h : A.dim c = p
    · simp [h]
    · simp [h,A.coefficient_eq_zero c p x h]
  · intro b _ hbc
    simp [hbc]
  · simp

lemma basis_positive (p : ℕ) (b : A.Index) : A.basis p b ∈ K.positive p := by
  classical
  apply (A.positive p _).mpr
  intro c
  rw [A.coefficient_basis]
  split_ifs <;> omega

lemma derivative_rank (p : ℕ) (b c : A.Index) (hb : A.dim b = p+1) :
    (0 < A.coefficient c p (K.d p (A.basis (p+1) b)) → A.rank c < A.rank b) ∧
    (A.coefficient c p (K.d p (A.basis (p+1) b)) < 0 → A.rank b < A.rank c) := by
  have hd : A.basis (p+1) b = (A.atom b).row (p+1) false := by
    rw [← hb,A.basis_own]
  rw [hd,(A.atom b).boundary,map_sub]
  have hs := (A.positive p _).mp ((A.atom b).positive p false) c
  have ht := (A.positive p _).mp ((A.atom b).positive p true) c
  constructor
  · intro h
    exact A.ranked b p (by omega) true c (by omega)
  · intro h
    exact A.ranked b p (by omega) false c (by omega)

def mass (p : ℕ) : K.Chain p →+ ℤ := ∑ b, A.coefficient b p

lemma mass_apply (p : ℕ) (x : K.Chain p) :
    A.mass p x = ∑ b, A.coefficient b p x := by simp [mass]

lemma mass_nonneg (p : ℕ) (x : K.Chain p) (hx : x ∈ K.positive p) :
    0 ≤ A.mass p x := by
  rw [A.mass_apply]
  exact Finset.sum_nonneg (fun b _ => (A.positive p x).mp hx b)

lemma mass_basis (p : ℕ) (b : A.Index) (hb : A.dim b = p) :
    A.mass p (A.basis p b) = 1 := by
  classical
  rw [A.mass_apply]
  simp only [A.coefficient_basis, ite_eq_left hb]
  simp

lemma mass_pos (p : ℕ) (x : K.Chain p) (hx : x ∈ K.positive p)
    (b : A.Index) (hb : 0 < A.coefficient b p x) : 0 < A.mass p x := by
  rw [A.mass_apply]
  exact Finset.sum_pos' (fun c _ => (A.positive p x).mp hx c)
    ⟨b,Finset.mem_univ _,hb⟩

lemma augmentation_basis (b : A.Index) :
    K.augmentation (A.basis 0 b) = if A.dim b = 0 then 1 else 0 := by
  by_cases h : A.dim b = 0
  · have he : A.basis 0 b = (A.atom b).row 0 false := by rw [← h,A.basis_own]
    rw [he,(A.atom b).augmentation,ite_eq_left h]
  · simp [basis,h]

lemma augmentation_eq_mass (x : K.Chain 0) : K.augmentation x = A.mass 0 x := by
  classical
  conv_lhs => rw [← A.expansion 0 x]
  rw [map_sum,A.mass_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_zsmul,A.augmentation_basis]
  by_cases h : A.dim b = 0
  · simp [h]
  · simp [h,A.coefficient_eq_zero b 0 x h]

lemma positive_augmentation_zero (x : K.Chain 0) (hx : x ∈ K.positive 0)
    (he : K.augmentation x = 0) : x = 0 := by
  apply A.ext 0
  intro b
  rw [map_zero]
  have hb := (A.positive 0 x).mp hx b
  by_contra hn
  have hp := A.mass_pos 0 x hx b (by omega)
  rw [A.augmentation_eq_mass x] at he
  omega

lemma peel_remainder (p : ℕ) (x : K.Chain p) (hx : x ∈ K.positive p)
    (b : A.Index) (hb : 0 < A.coefficient b p x) :
    x - A.basis p b ∈ K.positive p := by
  classical
  have hd := A.homogeneous b p x (ne_of_gt hb)
  apply (A.positive p _).mpr
  intro c
  rw [map_sub,A.coefficient_basis,ite_eq_left hd]
  by_cases h : b = c
  · subst c; simp only; omega
  · rw [ite_eq_right h,sub_zero]
    exact (A.positive p x).mp hx c

lemma objects_atomic (x : Table K) (hx : truncate 0 false x = x) :
    ∃ b : A.Index, A.dim b = 0 ∧ x = A.atom b := by
  classical
  have he : A.mass 0 (x.row 0 false) = 1 := by rw [← A.augmentation_eq_mass,x.augmentation]
  obtain ⟨b,hb⟩ : ∃ b, 0 < A.coefficient b 0 (x.row 0 false) := by
    by_contra h
    push Not at h
    have hz : A.mass 0 (x.row 0 false) ≤ 0 := by
      rw [A.mass_apply]
      exact Finset.sum_nonpos (fun b _ => h b)
    omega
  have hd := A.homogeneous b 0 (x.row 0 false) (ne_of_gt hb)
  have hb' : A.basis 0 b = (A.atom b).row 0 false := by rw [← hd,A.basis_own]
  have hrem := A.peel_remainder 0 (x.row 0 false) (x.positive 0 false) b hb
  have haug : K.augmentation (x.row 0 false - A.basis 0 b) = 0 := by
    rw [map_sub,x.augmentation,A.augmentation_basis,ite_eq_left hd,sub_self]
  have hr := sub_eq_zero.mp (A.positive_augmentation_zero _ hrem haug)
  refine ⟨b,hd,?_⟩
  have ha : truncate 0 false (A.atom b) = A.atom b := hd ▸ A.bounded b
  ext p e
  by_cases hp : p = 0
  · subst p
    cases e
    · exact hr.trans hb'
    · rw [← row_top_fixed x hx,← row_top_fixed (A.atom b) ha]
      exact hr.trans hb'
  · rw [row_above_fixed x hx (by omega) e,row_above_fixed (A.atom b) ha (by omega) e]

lemma peel_positive (p : ℕ) (z : K.Chain (p+1)) (x : K.Chain p)
    (hz : z ∈ K.positive (p+1)) (hx : x ∈ K.positive p)
    (hy : x + K.d p z ∈ K.positive p) (b : A.Index)
    (hb : 0 < A.coefficient b (p+1) z)
    (hmax : ∀ c, A.coefficient c (p+1) z ≠ 0 → A.rank c ≤ A.rank b) :
    x + K.d p (A.basis (p+1) b) ∈ K.positive p := by
  classical
  have hd := A.homogeneous b (p+1) z (ne_of_gt hb)
  apply (A.positive p _).mpr
  intro t
  rw [map_add]
  by_cases ht : 0 ≤ A.coefficient t p (K.d p (A.basis (p+1) b))
  · exact add_nonneg ((A.positive p x).mp hx t) ht
  have hrank := (A.derivative_rank p b t hd).2 (lt_of_not_ge ht)
  have hnonpos (c : A.Index) :
      A.coefficient c (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) c)) ≤ 0 := by
    by_cases hc : A.coefficient c (p+1) z = 0
    · simp [hc]
    have hdc := A.homogeneous c (p+1) z hc
    apply mul_nonpos_of_nonneg_of_nonpos ((A.positive (p+1) z).mp hz c)
    by_contra hn
    have hr := (A.derivative_rank p c t hdc).1 (lt_of_not_ge hn)
    have hm := hmax c hc
    omega
  have hbd : A.coefficient t p (K.d p z) ≤
      A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) := by
    conv_lhs => rw [← A.expansion (p+1) z]
    rw [map_sum,map_sum]
    simp only [map_zsmul,smul_eq_mul]
    calc
      _ ≤ ∑ c : A.Index, if c = b then
        A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) else 0 := by
          apply Finset.sum_le_sum
          intro c _
          by_cases h : c = b
          · subst c; simp only; exact le_rfl
          · rw [ite_eq_right h]; exact hnonpos c
      _ = _ := by simp
  have hmul : A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) ≤
      A.coefficient t p (K.d p (A.basis (p+1) b)) := by
    calc
      _ ≤ 1 * A.coefficient t p (K.d p (A.basis (p+1) b)) :=
        mul_le_mul_of_nonpos_right (by omega) (by omega)
      _ = _ := one_mul _
  have hy' := (A.positive p _).mp hy t
  rw [map_add] at hy'
  omega

inductive TopPasting (n : ℕ) : Table K → Prop
  | identity x : truncate n false x = x → TopPasting n x
  | basis (x : Table K) (b : A.Index) : truncate (n+1) false x = x →
      A.dim b = n+1 → x.row (n+1) false = A.basis (n+1) b → TopPasting n x
  | compose x y (h : truncate n true x = truncate n false y) :
      TopPasting n x → TopPasting n y → TopPasting n (comp n x y h)

lemma top_pasting {n : ℕ} (y : Table K) (hy : truncate (n+1) false y = y) :
    A.TopPasting n y := by
  classical
  generalize hm : (A.mass (n+1) (y.row (n+1) false)).toNat = m
  induction m using Nat.strong_induction_on generalizing y with
  | h m ih =>
    let z := y.row (n+1) false
    have hz : z ∈ K.positive (n+1) := y.positive (n+1) false
    by_cases he : z = 0
    · exact .identity y (fixed_of_top_zero hy he)
    let S := Finset.univ.filter (fun b => A.coefficient b (n+1) z ≠ 0)
    have hs : S.Nonempty := by
      by_contra hn
      apply he
      apply A.ext (n+1)
      intro b
      rw [map_zero]
      by_contra hb
      exact hn ⟨b,by simp [S,hb]⟩
    obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S A.rank hs
    have hb' : A.coefficient b (n+1) z ≠ 0 := (Finset.mem_filter.mp hb).2
    have hp : 0 < A.coefficient b (n+1) z :=
      lt_of_le_of_ne ((A.positive (n+1) z).mp hz b) (Ne.symm hb')
    have hd := A.homogeneous b (n+1) z hb'
    have hrem := A.peel_remainder (n+1) z hz b hp
    have hfinal : y.row n false + K.d n z ∈ K.positive n := by
      change y.row n false + K.d n (y.row (n+1) false) ∈ _
      rw [y.boundary]
      convert y.positive n true using 1; abel
    have hpos := A.peel_positive n z (y.row n false) hz (y.positive n false) hfinal b hp
      (fun c hc => hmax c (by simp [S,hc]))
    obtain ⟨x,w,hxw,hx,hw,hxt,hwt,heq⟩ :=
      split_top y hy (A.basis (n+1) b) (z - A.basis (n+1) b)
        (A.basis_positive (n+1) b) hrem (by dsimp [z]; abel) hpos
    have hlt : (A.mass (n+1) (w.row (n+1) false)).toNat < m := by
      rw [hwt,map_sub,A.mass_basis (n+1) b hd,← hm]
      change (A.mass (n+1) z - 1).toNat < (A.mass (n+1) z).toNat
      rw [Int.toNat_lt_toNat (A.mass_pos (n+1) z hz b hp)]
      omega
    rw [← heq]
    exact .compose x w hxw (.basis x b hx hd hxt) (ih _ hlt w hw rfl)

def cut (p : ℕ) (z : K.Chain p) (P : A.Index → Prop) : K.Chain p :=
  ∑ b, if P b then A.coefficient b p z • A.basis p b else 0

lemma coefficient_cut (p : ℕ) (z : K.Chain p) (P : A.Index → Prop) (b : A.Index) :
    A.coefficient b p (A.cut p z P) = if P b then A.coefficient b p z else 0 := by
  classical
  rw [cut,map_sum]
  simp only [apply_ite,map_zsmul,map_zero,A.coefficient_basis]
  rw [Finset.sum_eq_single b]
  · by_cases hd : A.dim b = p
    · by_cases hp : P b <;> simp [hd,hp]
    · simp [hd,A.coefficient_eq_zero b p z hd]
  · intro c _ hc
    by_cases hP : P c <;> simp [hP,hc]
  · simp

lemma cut_positive (p : ℕ) (z : K.Chain p) (hz : z ∈ K.positive p) (P : A.Index → Prop) :
    A.cut p z P ∈ K.positive p := by
  apply (A.positive p _).mpr
  intro b
  rw [A.coefficient_cut]
  split_ifs
  · exact (A.positive p z).mp hz b
  · exact le_rfl

lemma cut_add_complement (p : ℕ) (z : K.Chain p) (P : A.Index → Prop) :
    A.cut p z P + A.cut p z (fun b => ¬P b) = z := by
  apply A.ext p
  intro b
  rw [map_add,A.coefficient_cut,A.coefficient_cut]
  by_cases h : P b <;> simp [h]

lemma coefficient_derivative (p : ℕ) (z : K.Chain (p+1)) (t : A.Index) :
    A.coefficient t p (K.d p z) =
      ∑ b, A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) := by
  conv_lhs => rw [← A.expansion (p+1) z]
  rw [map_sum,map_sum]
  simp only [map_zsmul,smul_eq_mul]

lemma derivative_nonneg_of_before (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (hs : ∀ b, A.coefficient b (p+1) z ≠ 0 → r < A.rank b)
    (t : A.Index) (ht : A.rank t ≤ r) : 0 ≤ A.coefficient t p (K.d p z) := by
  classical
  rw [A.coefficient_derivative]
  apply Finset.sum_nonneg
  intro b _
  by_cases hb : A.coefficient b (p+1) z = 0
  · simp [hb]
  apply mul_nonneg ((A.positive (p+1) z).mp hz b)
  by_contra hn
  have hr := (A.derivative_rank p b t (A.homogeneous b (p+1) z hb)).2 (lt_of_not_ge hn)
  have hm := hs b hb
  omega

lemma derivative_nonpos_of_after (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (hs : ∀ b, A.coefficient b (p+1) z ≠ 0 → A.rank b ≤ r)
    (t : A.Index) (ht : r ≤ A.rank t) : A.coefficient t p (K.d p z) ≤ 0 := by
  classical
  rw [A.coefficient_derivative]
  apply Finset.sum_nonpos
  intro b _
  by_cases hb : A.coefficient b (p+1) z = 0
  · simp [hb]
  apply mul_nonpos_of_nonneg_of_nonpos ((A.positive (p+1) z).mp hz b)
  by_contra hn
  have hr := (A.derivative_rank p b t (A.homogeneous b (p+1) z hb)).1 (lt_of_not_ge hn)
  have hm := hs b hb
  omega

lemma cut_before_derivative (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (t : A.Index) (ht : A.rank t ≤ r) :
    0 ≤ A.coefficient t p (K.d p (A.cut (p+1) z (fun b => r < A.rank b))) := by
  apply A.derivative_nonneg_of_before p _ (A.cut_positive _ _ hz _) r _ t ht
  intro b hb
  rw [A.coefficient_cut] at hb
  by_contra hn
  exact hb (ite_eq_right hn)

lemma cut_after_derivative (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (t : A.Index) (ht : r ≤ A.rank t) :
    A.coefficient t p (K.d p (A.cut (p+1) z (fun b => ¬r < A.rank b))) ≤ 0 := by
  apply A.derivative_nonpos_of_after p _ (A.cut_positive _ _ hz _) r _ t ht
  intro b hb
  rw [A.coefficient_cut] at hb
  by_contra hn
  exact hb (ite_eq_right (not_not_intro (lt_of_not_ge hn)))

lemma rank_cut_positive (p : ℕ) (r : ℤ) (a b x y : K.Chain p) (z : K.Chain (p+1))
    (ha : a ∈ K.positive p) (hb : b ∈ K.positive p)
    (hx : x ∈ K.positive p) (hy : y ∈ K.positive p) (hz : z ∈ K.positive (p+1))
    (has : ∀ t, A.coefficient t p a ≠ 0 → r < A.rank t)
    (hbs : ∀ t, A.coefficient t p b ≠ 0 → A.rank t < r)
    (he : y - x = b - a + K.d p z) :
    x + K.d p (A.cut (p+1) z (fun t => r < A.rank t)) ∈ K.positive p ∧
    y - K.d p (A.cut (p+1) z (fun t => ¬r < A.rank t)) ∈ K.positive p := by
  have hh (t : A.Index) := congrArg (A.coefficient t p) he
  have dh : K.d p z = K.d p (A.cut (p+1) z (fun t => r < A.rank t)) +
      K.d p (A.cut (p+1) z (fun t => ¬r < A.rank t)) := by
    rw [← map_add,A.cut_add_complement]
  simp only [dh,map_sub,map_add] at hh
  constructor
  · apply (A.positive p _).mpr
    intro t
    rw [map_add]
    by_cases ht : A.rank t ≤ r
    · exact add_nonneg ((A.positive p x).mp hx t) (A.cut_before_derivative p z hz r t ht)
    · have hbt : A.coefficient t p b = 0 := by
        by_contra hn
        have := hbs t hn
        omega
      have hf := hh t
      rw [hbt] at hf
      have hf' := A.cut_after_derivative p z hz r t (by omega)
      have hp := (A.positive p y).mp hy t
      have hn := (A.positive p a).mp ha t
      omega
  · apply (A.positive p _).mpr
    intro t
    rw [map_sub]
    by_cases ht : r ≤ A.rank t
    · exact sub_nonneg.mpr (le_trans (A.cut_after_derivative p z hz r t ht) ((A.positive p y).mp hy t))
    · have hat : A.coefficient t p a = 0 := by
        by_contra hn
        have := has t hn
        omega
      have hf := hh t
      rw [hat] at hf
      have hf' := A.cut_before_derivative p z hz r t (by omega)
      have hp := (A.positive p x).mp hx t
      have hn := (A.positive p b).mp hb t
      omega

inductive AtomPasting : Table K → Prop
  | atom (b : A.Index) : AtomPasting (A.atom b)
  | compose (k : ℕ) (x y) (h : truncate k true x = truncate k false y) :
      AtomPasting x → AtomPasting y → AtomPasting (comp k x y h)

lemma common_atom_context (b : A.Index) (s : ℕ) (hs : s < A.dim b)
    (y : Table K) (hy : y.row (s+1) false = (A.atom b).row (s+1) false) :
    y.row s false - (A.atom b).row s false ∈ K.positive s ∧
      y.row s true - (A.atom b).row s true = y.row s false - (A.atom b).row s false := by
  have he : y.row s true - y.row s false = (A.atom b).row s true - (A.atom b).row s false := by
    rw [← y.boundary s false,hy,(A.atom b).boundary]
  constructor
  · apply (A.positive s _).mpr
    intro t
    rw [map_sub]
    by_cases ht : A.coefficient t s ((A.atom b).row s false) = 0
    · rw [ht,sub_zero]
      exact (A.positive s _).mp (y.positive s false) t
    have hf : A.coefficient t s ((A.atom b).row s true) = 0 := by
      by_contra hn
      have hs' := A.ranked b s hs false t ht
      have ht' := A.ranked b s hs true t hn
      simp only [Bool.false_eq_true,ite_false,ite_true] at hs' ht'
      omega
    have hh := congrArg (A.coefficient t s) he
    simp only [map_sub,hf] at hh
    have hp := (A.positive s _).mp (y.positive s true) t
    omega
  · apply A.ext s
    intro t
    have hh := congrArg (A.coefficient t s) he
    simp only [map_sub] at hh ⊢
    omega

lemma atom_context_pasting {n : ℕ} (b : A.Index) (hdim : A.dim b = n+1)
    (hsmall : ∀ x : Table K, truncate n false x = x → A.AtomPasting x)
    (k : ℕ) (hk : k ≤ n) (y : Table K)
    (hy : ∀ p, k < p → ∀ e, y.row p e = (A.atom b).row p e) : A.AtomPasting y := by
  induction k generalizing y with
  | zero =>
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b 0 (by omega) y (hy 1 (by omega) false)
    have haug : K.augmentation (y.row 0 false - (A.atom b).row 0 false) = 0 := by
      rw [map_sub,y.augmentation,(A.atom b).augmentation,sub_self]
    have hz₀ := A.positive_augmentation_zero _ hz haug
    have he : y = A.atom b := by
      ext p e
      cases p with
      | zero =>
        cases e
        · exact sub_eq_zero.mp hz₀
        · exact sub_eq_zero.mp (hcommon.trans hz₀)
      | succ p => exact hy (p+1) (by omega) e
    rw [he]
    exact .atom b
  | succ k ih =>
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b (k+1) (by omega) y (hy (k+2) (by omega) false)
    let z := y.row (k+1) false - (A.atom b).row (k+1) false
    let c := A.cut (k+1) z (fun t => A.rank b < A.rank t)
    let d := A.cut (k+1) z (fun t => ¬A.rank b < A.rank t)
    have hc : c ∈ K.positive (k+1) := A.cut_positive _ _ hz _
    have hd : d ∈ K.positive (k+1) := A.cut_positive _ _ hz _
    have hcd : c + d = z := A.cut_add_complement _ _ _
    have hrows (e : Bool) : y.row (k+1) e - c - d = (A.atom b).row (k+1) e := by
      have he : y.row (k+1) e - (A.atom b).row (k+1) e = z := by
        cases e
        · rfl
        · exact hcommon
      rw [sub_sub,hcd]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
    have ht : ∀ e, y.row (k+1) e - c - d ∈ K.positive (k+1) := by
      intro e
      rw [hrows]
      exact (A.atom b).positive _ _
    have hdiff : y.row k true - y.row k false = (A.atom b).row k true -
        (A.atom b).row k false + K.d k z := by
      dsimp [z]
      rw [map_sub,y.boundary,(A.atom b).boundary]
      abel
    obtain ⟨hstart,hend⟩ := A.rank_cut_positive k (A.rank b) _ _ _ _ z
      ((A.atom b).positive k false) ((A.atom b).positive k true)
      (y.positive k false) (y.positive k true) hz
      (fun t ht => A.ranked b k (by omega) false t ht)
      (fun t ht => A.ranked b k (by omega) true t ht) hdiff
    let m := removeContext k y c d ht hstart hend
    have hm : A.AtomPasting m := by
      apply ih (by omega) m
      intro p hp e
      change removeContextRow k y c d p e = (A.atom b).row p e
      by_cases hpk : p = k+1
      · subst p; rw [removeContextRow_top,hrows]
      · rw [removeContextRow_other k y c d p e (by omega) hpk]
        exact hy p (by omega) e
    obtain ⟨l,r,hlm,hmr,hl,hr,he⟩ := factor_context k y c d hc hd ht hstart hend
    rw [← he]
    exact .compose k _ _ hmr
      (.compose k _ _ hlm (hsmall l (K.nu.source_fixed_upwards hk hl)) hm)
      (hsmall r (K.nu.source_fixed_upwards hk hr))

theorem atomic_pasting (n : ℕ) (y : Table K) (hy : truncate n false y = y) : A.AtomPasting y := by
  induction n generalizing y with
  | zero =>
    obtain ⟨b,hd,rfl⟩ := A.objects_atomic y hy
    exact .atom b
  | succ n ih =>
    have htop := A.top_pasting y hy
    clear hy
    induction htop with
    | identity x hx => exact ih x hx
    | basis x b hx hb ht =>
      have ha : truncate (n+1) false (A.atom b) = A.atom b := hb ▸ A.bounded b
      have ht' : x.row (n+1) false = (A.atom b).row (n+1) false := by
        rw [ht,← hb,A.basis_own]
      apply A.atom_context_pasting b hb ih n le_rfl x
      intro p hp e
      exact NormalizedChains.rows_above_top_agree x (A.atom b) hx ha ht' p (by omega) e
    | compose x y h hx hy ihx ihy => exact .compose n x y h ihx ihy

theorem all_atomic (y : Table K) : A.AtomPasting y := by
  obtain ⟨n,hn⟩ := K.nu.finite_dimension y
  exact A.atomic_pasting n y hn

end RankedAtoms
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

namespace Word
variable {N p : ℕ}
instance finite (N : ℕ) : Finite (Word N) := inferInstanceAs (Finite {w : NormalizedChains.Word (Fin (N+1)) // w.val ≠ []})

lemma empty_coefficient (x : (complex (Fin (N+1))).Chain p)
    (w : NormalizedChains.Word (Fin (N+1))) (hw : w.val = []) : x.val w = 0 := by
  by_contra hn
  have h := (mem_grade_iff (p+1) x.val).mp x.property w hn
  simp [hw] at h

lemma chain_ext (x y : (complex (Fin (N+1))).Chain p)
    (h : ∀ w : Word N, x.val w.val = y.val w.val) : x = y := by
  apply Subtype.ext
  apply Finsupp.ext
  intro w
  by_cases hw : w.val = []
  · rw [empty_coefficient x w hw,empty_coefficient y w hw]
  · exact h ⟨w,hw⟩

lemma chain_positive (x : (complex (Fin (N+1))).Chain p) :
    x ∈ (complex (Fin (N+1))).positive p ↔ ∀ w : Word N, 0 ≤ x.val w.val := by
  constructor
  · intro hx w
    exact hx w.val
  · intro hx w
    by_cases hw : w.val = []
    · rw [empty_coefficient x w hw]
    · exact hx ⟨w,hw⟩
end Word

namespace Basis
variable {N : ℕ}

def indexEquiv : Basis N ≃ ((Bool × Word N) ⊕ Word N) where
  toFun b := match b with
    | .endpoint a w => .inl (a,w)
    | .vertical w => .inr w
  invFun b := match b with
    | .inl (a,w) => .endpoint a w
    | .inr w => .vertical w
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

instance finite (N : ℕ) : Finite (Basis N) := Finite.of_equiv _ indexEquiv.symm

lemma coefficient_homogeneous (b : Basis N) (p : ℕ)
    (x : (complex (Fin (N+1))).cylinder.Chain p) (hx : b.coefficient p x ≠ 0) : b.dim = p := by
  cases b with
  | endpoint a w =>
    cases p with
    | zero =>
      cases a
      · exact Word.dim_eq_of_coefficient x.1 w hx
      · exact Word.dim_eq_of_coefficient x.2 w hx
    | succ p =>
      cases a
      · exact Word.dim_eq_of_coefficient x.1 w hx
      · exact Word.dim_eq_of_coefficient x.2.1 w hx
  | vertical w =>
    cases p with
    | zero => exact False.elim (hx rfl)
    | succ p =>
      have h := Word.dim_eq_of_coefficient x.2.2 w hx
      change w.dim+1 = p+1
      omega

lemma coefficient_ext (p : ℕ) (x y : (complex (Fin (N+1))).cylinder.Chain p)
    (h : ∀ b : Basis N, b.coefficient p x = b.coefficient p y) : x = y := by
  cases p with
  | zero =>
    apply Prod.ext
    · apply Word.chain_ext
      intro w
      exact h (.endpoint false w)
    · apply Word.chain_ext
      intro w
      exact h (.endpoint true w)
  | succ p =>
    apply Prod.ext
    · apply Word.chain_ext
      intro w
      exact h (.endpoint false w)
    · apply Prod.ext
      · apply Word.chain_ext
        intro w
        exact h (.endpoint true w)
      · apply Word.chain_ext
        intro w
        exact h (.vertical w)

lemma positive_iff (p : ℕ) (x : (complex (Fin (N+1))).cylinder.Chain p) :
    x ∈ (complex (Fin (N+1))).cylinder.positive p ↔ ∀ b : Basis N, 0 ≤ b.coefficient p x := by
  constructor
  · exact fun hx b => b.coefficient_nonneg p x hx
  · intro hx
    cases p with
    | zero =>
      exact ⟨(Word.chain_positive x.1).mpr (fun w => hx (.endpoint false w)),
        (Word.chain_positive x.2).mpr (fun w => hx (.endpoint true w))⟩
    | succ p =>
      exact ⟨(Word.chain_positive x.1).mpr (fun w => hx (.endpoint false w)),
        (Word.chain_positive x.2.1).mpr (fun w => hx (.endpoint true w)),
        (Word.chain_positive x.2.2).mpr (fun w => hx (.vertical w))⟩

def rankedAtoms (N : ℕ) : RankedAtoms (complex (Fin (N+1))).cylinder where
  Index := Basis N
  finite := Fintype.ofFinite (Basis N)
  dim := Basis.dim
  rank := Basis.rank
  atom := Basis.atom
  bounded := Basis.atom_bounded
  coefficient := Basis.coefficient
  homogeneous := Basis.coefficient_homogeneous
  ext := Basis.coefficient_ext
  positive := Basis.positive_iff
  top := Basis.atom_top_coefficient
  ranked := Basis.atom_rank

theorem cylinder_all_atomic (y : Table (complex (Fin (N+1))).cylinder) :
    (rankedAtoms N).AtomPasting y := (rankedAtoms N).all_atomic y

end Basis
end Thomason.NormalizedChains.Prism

end

end OAI
