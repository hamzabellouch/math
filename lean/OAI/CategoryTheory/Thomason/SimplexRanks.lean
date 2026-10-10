import Mathlib
import OAI.CategoryTheory.Thomason.SimplexAtoms

namespace OAI

/-! Simplex Ranks. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

def simplexRank {N : ℕ} : List (Fin (N+1)) → ℤ
  | [] => 0
  | a :: l => (3 : ℤ) ^ (N-a.val) - simplexRank l

lemma simplexWeight_lt {N : ℕ} {a b : Fin (N+1)} (h : a < b) :
    3 * (3 : ℤ) ^ (N-b.val) ≤ (3 : ℤ) ^ (N-a.val) := by
  have he : N-b.val+1 ≤ N-a.val := by have := b.isLt; change a.val < b.val at h; omega
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) he
  simpa [pow_succ, mul_comm] using hh

lemma simplexRank_bounds {N : ℕ} {a : Fin (N+1)} {l : List (Fin (N+1))}
    (h : (a :: l).Pairwise (· < ·)) :
    0 < simplexRank (a :: l) ∧ simplexRank (a :: l) ≤ (3 : ℤ) ^ (N-a.val) := by
  induction l generalizing a with
  | nil => simp only [simplexRank, sub_zero]; exact ⟨pow_pos (by norm_num) _, le_rfl⟩
  | cons b l ih =>
    obtain ⟨hb, hb'⟩ := ih h.tail
    have hw := simplexWeight_lt ((List.pairwise_cons.mp h).1 b (by simp))
    change 0 < (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l) ∧
      (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l) ≤ (3 : ℤ) ^ (N-a.val)
    constructor <;> linarith

lemma simplexRank_tail_lt {N : ℕ} {a : Fin (N+1)} {l : List (Fin (N+1))}
    (h : (a :: l).Pairwise (· < ·)) : simplexRank l < simplexRank (a :: l) := by
  cases l with
  | nil => exact (simplexRank_bounds h).1
  | cons b l =>
    obtain ⟨hb, hb'⟩ := simplexRank_bounds h.tail
    have hw := simplexWeight_lt ((List.pairwise_cons.mp h).1 b (by simp))
    change simplexRank (b :: l) < (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l)
    linarith

variable {E : Type u} [PartialOrder E]

lemma prepend_apply_cons (a : E) (c : Chains E) (w : Word E)
    (h : (a :: w.val).Pairwise (· < ·)) :
    prepend a c ⟨a :: w.val, h⟩ = c w := by
  classical
  rw [prepend, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul,
    bracket_apply, List.cons.injEq, true_and]
  have he (t : Word E) : t.val = w.val ↔ t = w := Subtype.val_inj
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

lemma wordBoundary_rank {N : ℕ} (w t : Word (Fin (N+1))) :
    (wordBoundary w.val t > 0 → wordBoundary w.val t = 1 ∧ simplexRank t.val < simplexRank w.val) ∧
    (wordBoundary w.val t < 0 → wordBoundary w.val t = -1 ∧ simplexRank w.val < simplexRank t.val) := by
  rcases w with ⟨w, hw⟩
  induction w generalizing t with
  | nil => simp [wordBoundary]
  | cons a l ih =>
    have htail : l.Pairwise (· < ·) := hw.tail
    by_cases he : l = t.val
    · have hz : prepend a (wordBoundary l) t = 0 := by
        apply prepend_apply_zero
        intro q hq
        have ha : a ∈ l := he.symm ▸ hq ▸ (List.mem_cons_self : a ∈ a :: q)
        exact (lt_irrefl a) ((List.pairwise_cons.mp hw).1 a ha)
      rw [wordBoundary_cons, Finsupp.sub_apply, hz, sub_zero, bracket_apply, ite_eq_left he]
      constructor
      · intro _; exact ⟨rfl, he ▸ simplexRank_tail_lt hw⟩
      · norm_num
    · rw [wordBoundary_cons, Finsupp.sub_apply, bracket_apply, ite_eq_right he, zero_sub]
      cases ht : t.val with
      | nil =>
        have hz : prepend a (wordBoundary l) t = 0 :=
          prepend_apply_zero a _ t (by intro q; simp [ht])
        simp [hz]
      | cons b q =>
        by_cases hab : a = b
        · subst b
          have hq : (a :: q).Pairwise (· < ·) := ht ▸ t.property
          let t' : Word (Fin (N+1)) := ⟨q, hq.tail⟩
          have het : t = ⟨a :: t'.val, hq⟩ := Subtype.ext ht
          simp only [het, prepend_apply_cons]
          obtain ⟨hp, hn⟩ := ih t' htail
          constructor
          · intro h
            obtain ⟨hc, hr⟩ := hn (neg_pos.mp h)
            refine ⟨by simpa using congrArg Neg.neg hc, ?_⟩
            change (3 : ℤ) ^ (N-a.val) - simplexRank q <
              (3 : ℤ) ^ (N-a.val) - simplexRank l
            exact sub_lt_sub_left hr _
          · intro h
            obtain ⟨hc, hr⟩ := hp (neg_neg_iff_pos.mp h)
            refine ⟨by simpa using congrArg Neg.neg hc, ?_⟩
            change (3 : ℤ) ^ (N-a.val) - simplexRank l <
              (3 : ℤ) ^ (N-a.val) - simplexRank q
            exact sub_lt_sub_left hr _
        · have hz : prepend a (wordBoundary l) t = 0 := by
            apply prepend_apply_zero
            intro s hs
            have := (List.cons.inj (hs.trans ht)).1
            exact hab this
          simp [hz]

lemma boundary_apply (c : Chains E) (t : Word E) :
    boundary c t = c.sum (fun w a => a * wordBoundary w.val t) := by
  classical
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul]
  rfl

lemma simplex_peel_positive {N : ℕ} {z x : Chains (Fin (N+1))}
    (hz : Positive z) (hx : Positive x) (hy : Positive (x + boundary z))
    (w : Word (Fin (N+1))) (hw : 0 < z w)
    (hmax : ∀ q ∈ z.support, simplexRank q.val ≤ simplexRank w.val) :
    Positive (x + wordBoundary w.val) := by
  classical
  intro t
  change 0 ≤ x t + wordBoundary w.val t
  by_cases ht : 0 ≤ wordBoundary w.val t
  · exact add_nonneg (hx t) ht
  · obtain ⟨hcoef, hrank⟩ := (wordBoundary_rank w t).2 (lt_of_not_ge ht)
    have hnonpos (q : Word (Fin (N+1))) (hq : q ∈ z.support) :
        wordBoundary q.val t ≤ 0 := by
      by_contra hn
      have hr := ((wordBoundary_rank q t).1 (lt_of_not_ge hn)).2
      exact (not_lt_of_ge (hmax q hq)) (hrank.trans hr)
    have hbd : boundary z t ≤ -z w := by
      rw [boundary_apply, Finsupp.sum]
      calc
        ∑ q ∈ z.support, z q * wordBoundary q.val t ≤
            ∑ q ∈ z.support, if q = w then -z w else 0 := by
          apply Finset.sum_le_sum
          intro q hq
          by_cases he : q = w
          · subst q; simp only [hcoef, mul_neg, mul_one]; exact le_rfl
          · rw [ite_eq_right he]
            exact mul_nonpos_of_nonneg_of_nonpos (hz q) (hnonpos q hq)
        _ = -z w := by simp [Finsupp.mem_support_iff, ne_of_gt hw]
    have hyt := hy t
    change 0 ≤ x t + boundary z t at hyt
    rw [hcoef]
    omega

lemma simplex_peel_remainder {N : ℕ} {z : Chains (Fin (N+1))}
    (hz : Positive z) (w : Word (Fin (N+1))) (hw : 0 < z w) :
    Positive (z - bracket w.val) := by
  classical
  rw [bracket_of_pairwise w.property]
  intro t
  change 0 ≤ z t - (Finsupp.single w 1) t
  by_cases he : w = t
  · subst t; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne (Ne.symm he), sub_zero]; exact hz t

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

def extensionRow (n : ℕ) (x : Table K) (c : K.Chain (n+1)) : (p : ℕ) → Bool → K.Chain p :=
  Function.update (Function.update x.row n
    (fun b => x.row n false + if b then K.d n c else 0)) (n+1) (fun _ => c)

@[simp] lemma extensionRow_top (n : ℕ) (x : Table K) (c : K.Chain (n+1)) (b : Bool) :
    extensionRow n x c (n+1) b = c := by simp [extensionRow]

@[simp] lemma extensionRow_middle (n : ℕ) (x : Table K) (c : K.Chain (n+1)) (b : Bool) :
    extensionRow n x c n b = x.row n false + if b then K.d n c else 0 := by
  simp [extensionRow]

lemma extensionRow_other (n : ℕ) (x : Table K) (c : K.Chain (n+1))
    (p : ℕ) (b : Bool) (h₀ : p ≠ n) (h₁ : p ≠ n+1) :
    extensionRow n x c p b = x.row p b := by simp [extensionRow, h₀, h₁]

def extendTop (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) : Table K where
  row := extensionRow n x c
  positive p b := by
    by_cases h₀ : p = n
    · subst p
      rw [extensionRow_middle]
      cases b
      · simpa using x.positive n false
      · exact hp
    · by_cases h₁ : p = n+1
      · subst p; simpa using hc
      · rw [extensionRow_other n x c p b h₀ h₁]; exact x.positive p b
  boundary p b := by
    by_cases h₀ : p = n
    · subst p
      rw [extensionRow_top, extensionRow_middle, extensionRow_middle]
      simp
    · by_cases h₁ : p = n+1
      · subst p
        rw [extensionRow_top, extensionRow_top,
          extensionRow_other n x c (n+1+1) b (by omega) (by omega),
          row_above_fixed x hx (by omega : n < n+1+1) b, map_zero, sub_self]
      · by_cases h₂ : p+1 = n
        · subst n
          rw [extensionRow_middle,
            extensionRow_other (p+1) x c p true (by omega) (by omega),
            extensionRow_other (p+1) x c p false (by omega) (by omega)]
          cases b <;> simp only [Bool.false_eq_true, ite_false, add_zero, ite_true]
          · exact x.boundary p false
          · rw [map_add, K.d_d, add_zero]; exact x.boundary p false
        · rw [extensionRow_other n x c (p+1) b h₂ (by omega),
            extensionRow_other n x c p true h₀ h₁,
            extensionRow_other n x c p false h₀ h₁]
          exact x.boundary p b
  augmentation b := by
    by_cases hn : n = 0
    · subst n
      rw [extensionRow_middle]
      cases b <;> simp only [Bool.false_eq_true, ite_false, add_zero, ite_true]
      · exact x.augmentation false
      · rw [map_add, K.augmentation_d, add_zero]; exact x.augmentation false
    · rw [extensionRow_other n x c 0 b (Ne.symm hn) (by omega)]
      exact x.augmentation b
  bounded := ⟨n+1, fun p hp b => by
    rw [extensionRow_other n x c p b (by omega) (by omega)]
    exact row_above_fixed x hx (by omega) b⟩

@[simp] lemma extendTop_row (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) (p : ℕ) (b : Bool) :
    (extendTop n x hx c hc hp).row p b = extensionRow n x c p b := rfl

lemma extendTop_source (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) :
    truncate n false (extendTop n x hx c hc hp) = x := by
  ext p b
  rw [truncate_row]
  by_cases h₀ : p < n
  · rw [ite_eq_left h₀, extendTop_row, extensionRow_other n x c p b (by omega) (by omega)]
  · rw [ite_eq_right h₀]
    by_cases h₁ : p = n
    · subst p
      rw [ite_eq_left rfl, extendTop_row, extensionRow_middle]
      cases b
      · simp
      · simpa using row_top_fixed x hx
    · rw [ite_eq_right h₁, row_above_fixed x hx (by omega) b]

lemma extendTop_dimension (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) :
    truncate (n+1) false (extendTop n x hx c hc hp) = extendTop n x hx c hc hp := by
  ext p b
  rw [truncate_row]
  by_cases h₀ : p < n+1
  · exact ite_eq_left h₀
  · rw [ite_eq_right h₀]
    by_cases h₁ : p = n+1
    · subst p; simp
    · rw [ite_eq_right h₁, extendTop_row, extensionRow_other n x c p b (by omega) h₁,
        row_above_fixed x hx (by omega) b]

lemma eq_extendTop (n : ℕ) (y : Table K) (hy : truncate (n+1) false y = y) :
    ∃ (hc : y.row (n+1) false ∈ K.positive (n+1))
      (hp : (truncate n false y).row n false + K.d n (y.row (n+1) false) ∈ K.positive n),
      extendTop n (truncate n false y) (by rw [truncate_truncate_same]; simp)
        (y.row (n+1) false) hc hp = y := by
  have he : (truncate n false y).row n false + K.d n (y.row (n+1) false) = y.row n true := by
    rw [truncate_top_row, y.boundary]; abel
  refine ⟨y.positive (n+1) false, he ▸ y.positive n true, ?_⟩
  ext p b
  rw [extendTop_row]
  by_cases h₀ : p = n
  · subst p; rw [extensionRow_middle, truncate_top_row]
    cases b
    · simp
    · simpa only [ite_true, truncate_top_row] using he
  · by_cases h₁ : p = n+1
    · subst p; rw [extensionRow_top]
      cases b
      · rfl
      · exact row_top_fixed y hy
    · rw [extensionRow_other n _ _ p b h₀ h₁, truncate_row]
      by_cases hp : p < n
      · exact ite_eq_left hp
      · rw [ite_eq_right hp, ite_eq_right h₀, row_above_fixed y hy (by omega) b]

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def chainMass : Chains E →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ (fun _ => 1)

lemma chainMass_eq_sum (z : Chains E) : chainMass z = z.sum (fun _ a => a) := by
  rw [chainMass, Finsupp.linearCombination_apply]
  apply Finsupp.sum_congr
  intro w hw
  simp

@[simp] lemma chainMass_bracket (w : Word E) : chainMass (bracket w.val) = 1 := by
  rw [bracket_of_pairwise w.property, chainMass, Finsupp.linearCombination_single]
  rfl

lemma chainMass_nonneg {z : Chains E} (hz : Positive z) : 0 ≤ chainMass z := by
  classical
  rw [chainMass_eq_sum, Finsupp.sum]
  exact Finset.sum_nonneg (fun w _ => hz w)

lemma chainMass_pos {z : Chains E} (hz : Positive z) {w : Word E} (hw : 0 < z w) :
    0 < chainMass z := by
  classical
  rw [chainMass_eq_sum, Finsupp.sum]
  exact Finset.sum_pos' (fun t _ => hz t) ⟨w, Finsupp.mem_support_iff.mpr (ne_of_gt hw), hw⟩

def Executable (x : Chains E) : List (Word E) → Prop
  | [] => Positive x
  | w :: l => Positive x ∧ Executable (x + wordBoundary w.val) l

lemma positive_chain_execution {N : ℕ} (z x : Chains (Fin (N+1)))
    (hz : Positive z) (hx : Positive x) (hy : Positive (x + boundary z)) :
    ∃ l : List (Word (Fin (N+1))), (l.map (fun w => bracket w.val)).sum = z ∧ Executable x l := by
  classical
  generalize hm : (chainMass z).toNat = m
  induction m using Nat.strong_induction_on generalizing z x with
  | h m ih =>
    by_cases he : z = 0
    · subst z
      exact ⟨[], by simp, hx⟩
    have hs : z.support.Nonempty := by
      by_contra hs
      have hse : z.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      exact he (Finsupp.support_eq_empty.mp hse)
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image z.support (fun w => simplexRank w.val) hs
    have hwpos : 0 < z w := lt_of_le_of_ne (hz w) (Ne.symm (Finsupp.mem_support_iff.mp hw))
    have hz' := simplex_peel_remainder hz w hwpos
    have hx' := simplex_peel_positive hz hx hy w hwpos hmax
    have hbd : boundary (bracket w.val) = wordBoundary w.val := boundary_bracket (w.property.imp le_of_lt)
    have hy' : Positive ((x + wordBoundary w.val) + boundary (z - bracket w.val)) := by
      rw [map_sub, hbd]
      convert hy using 1; abel
    have hmass : chainMass (z - bracket w.val) = chainMass z - 1 := by
      rw [map_sub, chainMass_bracket]
    have hlt : (chainMass (z - bracket w.val)).toNat < m := by
      rw [← hm, Int.toNat_lt_toNat (chainMass_pos hz hwpos), hmass]
      omega
    obtain ⟨l, hl, hxl⟩ := ih _ hlt (z - bracket w.val) (x + wordBoundary w.val) hz' hx' hy' rfl
    refine ⟨w :: l, ?_, hx, hxl⟩
    simp only [List.map_cons, List.sum_cons, hl]
    abel

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

lemma ext_source_top {n : ℕ} {x y : Table K}
    (hx : truncate (n+1) false x = x) (hy : truncate (n+1) false y = y)
    (hs : truncate n false x = truncate n false y)
    (ht : x.row (n+1) false = y.row (n+1) false) : x = y := by
  obtain ⟨hcx, hpx, ex⟩ := eq_extendTop n x hx
  obtain ⟨hcy, hpy, ey⟩ := eq_extendTop n y hy
  rw [← ex, ← ey]
  congr 1

lemma fixed_of_top_zero {n : ℕ} {x : Table K}
    (hx : truncate (n+1) false x = x) (ht : x.row (n+1) false = 0) :
    truncate n false x = x := by
  have hm : x.row n true = x.row n false := by
    have h := x.boundary n false
    rw [ht, map_zero] at h
    exact sub_eq_zero.mp h.symm
  ext p b
  rw [truncate_row]
  by_cases hp : p < n
  · exact ite_eq_left hp
  · rw [ite_eq_right hp]
    by_cases he : p = n
    · subst p; rw [ite_eq_left rfl]; cases b <;> simp [hm]
    · rw [ite_eq_right he]
      by_cases he' : p = n+1
      · subst p
        cases b
        · exact ht.symm
        · exact (row_top_fixed x hx).symm.trans ht |>.symm
      · exact (row_above_fixed x hx (by omega) b).symm

lemma comp_dimension {n k : ℕ} (hkn : k < n) {x y : Table K}
    (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    truncate n false (comp k x y h) = comp k x y h := by
  have h' : truncate k true (truncate n false x) = truncate k false (truncate n false y) := by
    simpa only [hx, hy] using h
  rw [truncate_comp_gt n k hkn false x y h h']
  simp only [hx, hy]

lemma split_top {n : ℕ} (y : Table K) (hy : truncate (n+1) false y = y)
    (c d : K.Chain (n+1)) (hc : c ∈ K.positive (n+1)) (hd : d ∈ K.positive (n+1))
    (ht : c + d = y.row (n+1) false)
    (hp : y.row n false + K.d n c ∈ K.positive n) :
    ∃ a b : Table K, ∃ h : truncate n true a = truncate n false b,
      truncate (n+1) false a = a ∧ truncate (n+1) false b = b ∧
      a.row (n+1) false = c ∧ b.row (n+1) false = d ∧ comp n a b h = y := by
  let x := truncate n false y
  have hx : truncate n false x = x := by simp [x, truncate_truncate_same]
  have hp' : x.row n false + K.d n c ∈ K.positive n := by simpa [x] using hp
  let a := extendTop n x hx c hc hp'
  have ha := extendTop_dimension n x hx c hc hp'
  let m := truncate n true a
  have hm : truncate n false m = m := by simp [m, truncate_truncate]
  have hmrow : m.row n false = y.row n false + K.d n c := by
    simp [m, a, x]
  have hpd : m.row n false + K.d n d ∈ K.positive n := by
    rw [hmrow, add_assoc, ← map_add, ht, y.boundary]
    convert y.positive n true using 1; abel
  let b := extendTop n m hm d hd hpd
  have hb := extendTop_dimension n m hm d hd hpd
  have hab : truncate n true a = truncate n false b := (extendTop_source n m hm d hd hpd).symm
  refine ⟨a, b, hab, ha, hb, by simp [a], by simp [b], ?_⟩
  apply ext_source_top (comp_dimension (by omega : n < n+1) ha hb hab) hy
  · rw [source_comp_le n n le_rfl, extendTop_source]
  · simpa [a, b] using ht

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

inductive TopPasting (N n : ℕ) : Table (complex (Fin (N+1))) → Prop
  | identity (x) : truncate n false x = x → TopPasting N n x
  | basis (x : Table (complex (Fin (N+1)))) (w : Word (Fin (N+1))) : truncate (n+1) false x = x →
      (x.row (n+1) false).val = bracket w.val → TopPasting N n x
  | compose (x y) (h : truncate n true x = truncate n false y) :
      TopPasting N n x → TopPasting N n y → TopPasting N n (comp n x y h)

lemma oriental_top_pasting {N n : ℕ} (y : Table (complex (Fin (N+1))))
    (hy : truncate (n+1) false y = y) : TopPasting N n y := by
  classical
  generalize hm : (chainMass (y.row (n+1) false).val).toNat = m
  induction m using Nat.strong_induction_on generalizing y with
  | h m ih =>
    let z := (y.row (n+1) false).val
    have hz : Positive z := y.positive (n+1) false
    by_cases he : z = 0
    · exact .identity y (fixed_of_top_zero hy (Subtype.ext he))
    have hs : z.support.Nonempty := by
      by_contra hs
      exact he (Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs))
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image z.support (fun w => simplexRank w.val) hs
    have hwpos : 0 < z w := lt_of_le_of_ne (hz w) (Ne.symm (Finsupp.mem_support_iff.mp hw))
    have hwlen : w.val.length = n+1+1 := by
      have := (mem_grade_iff (n+1+1) z).mp (y.row (n+1) false).property w
      exact this (Finsupp.mem_support_iff.mp hw)
    let c : (complex (Fin (N+1))).Chain (n+1) :=
      ⟨bracket w.val, hwlen ▸ bracket_mem_grade w.val⟩
    let d := y.row (n+1) false - c
    have hc : c ∈ (complex (Fin (N+1))).positive (n+1) := bracket_positive w.val
    have hd : d ∈ (complex (Fin (N+1))).positive (n+1) := simplex_peel_remainder hz w hwpos
    have ht : c + d = y.row (n+1) false := by dsimp [d]; abel
    have hx : Positive (y.row n false).val := y.positive n false
    have hfinal : Positive ((y.row n false).val + boundary z) := by
      have hb := congrArg Subtype.val (y.boundary n false)
      change boundary z = (y.row n true).val - (y.row n false).val at hb
      rw [hb]
      convert (show Positive (y.row n true).val from y.positive n true) using 1; abel
    have hp : y.row n false + (complex (Fin (N+1))).d n c ∈
        (complex (Fin (N+1))).positive n := by
      change Positive ((y.row n false).val + boundary (bracket w.val))
      rw [boundary_bracket (w.property.imp le_of_lt)]
      exact simplex_peel_positive hz hx hfinal w hwpos hmax
    obtain ⟨a, b, hab, ha, hb, hat, hbt, hyab⟩ := split_top y hy c d hc hd ht hp
    have hmass : (chainMass (b.row (n+1) false).val).toNat < m := by
      have he : (b.row (n+1) false).val = z - bracket w.val := congrArg Subtype.val hbt
      rw [he, map_sub, chainMass_bracket, ← hm]
      change (chainMass z - 1).toNat < (chainMass z).toNat
      rw [Int.toNat_lt_toNat (chainMass_pos hz hwpos)]
      omega
    rw [← hyab]
    exact .compose a b hab (.basis a w ha (congrArg Subtype.val hat))
      (ih _ hmass b hb rfl)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped Topology Topology.Homotopy

variable {X : Type u} {Y : Type v} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def basedLoopMap (N : Type w) (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    GenLoop N X x → GenLoop N Y y :=
  fun p => ⟨f.comp p.val, fun t ht => (congrArg f (p.property t ht)).trans h⟩

def basedGroupMap (N : Type w) (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (basedLoopMap N f x y h) (fun _ _ hp => hp.comp_continuousMap f)

lemma basedGroupMap_comp (N : Type w) (f : C(X, Y)) (g : C(Y, Z))
    (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g y = z)
    (p : HomotopyGroup N X x) :
    basedGroupMap N g y z hg (basedGroupMap N f x y hf p) =
      basedGroupMap N (g.comp f) x z ((congrArg g hf).trans hg) p := by
  induction p using Quotient.inductionOn with
  | h p => rfl

lemma basedGroupMap_id (N : Type w) (x : X) (p : HomotopyGroup N X x) :
    basedGroupMap N (.id X) x x rfl p = p := by
  induction p using Quotient.inductionOn with
  | h p => rfl

lemma basedGroupMap_homotopic (N : Type w) {f g : C(X, Y)} (x : X) (y : Y)
    (hf : f x = y) (hg : g x = y) (H : f.HomotopicRel g {x})
    (p : HomotopyGroup N X x) :
    basedGroupMap N f x y hf p = basedGroupMap N g x y hg p := by
  rcases H with ⟨H⟩
  induction p using Quotient.inductionOn with
  | h p =>
    apply Quotient.sound
    refine ⟨{ toHomotopy :=
      { toFun := fun q => H (q.1, p q.2)
        continuous_toFun := H.continuous.comp
          (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
        map_zero_left := fun t => H.toHomotopy.apply_zero (p t)
        map_one_left := fun t => H.toHomotopy.apply_one (p t) }
              prop' := ?_ }⟩
    intro t q hq
    change H (t, p.val q) = f (p.val q)
    rw [p.property q hq]
    exact H.eq_fst t (Set.mem_singleton x)

lemma componentsMap_comp (f : C(X, Y)) (g : C(Y, Z)) (p : ZerothHomotopy X) :
    componentsMap g (componentsMap f p) = componentsMap (g.comp f) p := by
  induction p with
  | mk p => rfl

lemma componentsMap_id (p : ZerothHomotopy X) : componentsMap (.id X) p = p := by
  induction p with
  | mk p => rfl

lemma componentsMap_homotopic {f g : C(X, Y)} (H : f.Homotopic g)
    (p : ZerothHomotopy X) : componentsMap f p = componentsMap g p := by
  rcases H with ⟨H⟩
  induction p with
  | mk p =>
    exact ZerothHomotopy.sound
      { toFun := fun t => H (t, p)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := H.apply_zero p
        target' := H.apply_one p }

theorem equivalence_of_strong_retract (j : C(X, Y)) (p : C(Y, X))
    (hj : p.comp j = .id X)
    (H : (j.comp p).HomotopicRel (.id Y) (Set.range j)) : Equivalence j := by
  have hpj (x : X) : p (j x) = x := ContinuousMap.congr_fun hj x
  constructor
  · have hl : Function.LeftInverse (componentsMap p) (componentsMap j) := by
      intro x
      rw [componentsMap_comp, hj, componentsMap_id]
    have hr : Function.RightInverse (componentsMap p) (componentsMap j) := by
      intro y
      rw [componentsMap_comp, componentsMap_homotopic H.homotopic, componentsMap_id]
    exact ⟨hl.injective, hr.surjective⟩
  · intro n x
    let q := basedGroupMap (Fin (n+1)) p (j x) x (hpj x)
    have hmap : groupMap (Fin (n+1)) j x =
        basedGroupMap (Fin (n+1)) j x (j x) rfl := rfl
    rw [hmap]
    have hl : Function.LeftInverse q (basedGroupMap (Fin (n+1)) j x (j x) rfl) := by
      intro a
      dsimp [q]
      rw [basedGroupMap_comp]
      have ht (h : (p.comp j) x = x) :
          basedGroupMap (Fin (n+1)) (p.comp j) x x h a = a := by
        simpa only [hj] using basedGroupMap_id (Fin (n+1)) x a
      exact ht _
    have hr : Function.RightInverse q (basedGroupMap (Fin (n+1)) j x (j x) rfl) := by
      intro a
      dsimp [q]
      rw [basedGroupMap_comp]
      have hx : (j.comp p).HomotopicRel (.id Y) {j x} := by
        rcases H with ⟨H⟩
        exact ⟨{ toHomotopy := H.toHomotopy
                 prop' := fun t y hy => H.eq_fst t (by
                   rcases Set.mem_singleton_iff.mp hy with rfl
                   exact ⟨x, rfl⟩) }⟩
      rw [basedGroupMap_homotopic _ (j x) (j x) _ rfl hx, basedGroupMap_id]
    exact ⟨hl.injective, hr.surjective⟩

end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

lemma simplexRank_of_after_lt {N : ℕ} {a : Fin (N+1)} {l : List (Fin (N+1))}
    (h : (a :: l).Pairwise (· < ·)) (w : Word (Fin (N+1)))
    (hw : ∀ b ∈ w.val, a < b) : simplexRank w.val < simplexRank (a :: l) := by
  cases l with
  | nil =>
    change simplexRank w.val < (3 : ℤ) ^ (N-a.val) - 0
    cases ht : w.val with
    | nil => simp only [simplexRank, sub_zero]; exact pow_pos (by norm_num) _
    | cons b q =>
      have hb := (simplexRank_bounds (ht ▸ w.property)).2
      have he := simplexWeight_lt (hw b (ht ▸ List.mem_cons_self))
      have hp : 0 < (3 : ℤ) ^ (N-b.val) := pow_pos (by norm_num) _
      linarith
  | cons b l =>
    have hb := (simplexRank_bounds h.tail).2
    have he := simplexWeight_lt ((List.pairwise_cons.mp h).1 b (by simp))
    have hp : 0 < (3 : ℤ) ^ (N-a.val) := pow_pos (by norm_num) _
    change simplexRank w.val < (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l)
    cases ht : w.val with
    | nil => rw [simplexRank]; linarith
    | cons c q =>
      have hc := (simplexRank_bounds (ht ▸ w.property)).2
      have hf := simplexWeight_lt (hw c (ht ▸ List.mem_cons_self))
      linarith

lemma prepend_support {E : Type u} [PartialOrder E] (a : E) (c : Chains E) (w : Word E)
    (hw : prepend a c w ≠ 0) :
    ∃ q : Word E, w.val = a :: q.val ∧ c q ≠ 0 := by
  classical
  have he : ∃ q, w.val = a :: q := by
    by_contra h
    apply hw
    exact prepend_apply_zero a c w (fun q hq => h ⟨q, hq.symm⟩)
  obtain ⟨q, hq⟩ := he
  let t : Word E := ⟨q, (hq ▸ w.property).tail⟩
  refine ⟨t, hq, ?_⟩
  have ht : w = ⟨a :: t.val, hq ▸ w.property⟩ := Subtype.ext hq
  rw [ht, prepend_apply_cons] at hw
  exact hw

lemma simplexAtom_rank {N : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (h : (a :: l).Pairwise (· < ·)) (p : ℕ) (hp : p < l.length)
    (b : Bool) (w : Word (Fin (N+1)))
    (hw : (((simplexAtom a l (h.imp le_of_lt)).table.row p b).val) w ≠ 0) :
    if b then simplexRank w.val < simplexRank (a :: l)
    else simplexRank (a :: l) < simplexRank w.val := by
  classical
  induction l generalizing a p b w with
  | nil => simp at hp
  | cons c l ih =>
    let x := simplexAtom c l (h.tail.imp le_of_lt)
    have ha : ∀ d ∈ c :: l, a < d := (List.pairwise_cons.mp h).1
    have hx : ∀ p b, (x.table.row p b).val ∈ supportedOn (Set.Ici a) :=
      fun p b => supportedOn_mono (fun d hd => (ha d hd).le) (x.supported p b)
    have het : (simplexAtom a (c :: l) (h.imp le_of_lt)).table =
        coneTable a x.table hx := rfl
    rw [het] at hw
    cases p with
    | zero =>
      rw [coneTable_row_zero] at hw
      cases b
      · change bracket [a] w ≠ 0 at hw
        rw [bracket_apply] at hw
        have he : [a] = w.val := by split_ifs at hw with he; exact he; contradiction
        change simplexRank (a :: c :: l) < simplexRank w.val
        rw [← he]
        have hc := (simplexRank_bounds h.tail).1
        simp only [simplexRank]
        change (3 : ℤ) ^ (N-a.val) - simplexRank (c :: l) <
          (3 : ℤ) ^ (N-a.val) - 0
        omega
      · change (x.table.row 0 true).val w ≠ 0 at hw
        have hs := (mem_supportedOn_iff {d | d ∈ c :: l} _).mp (x.supported 0 true) w hw
        exact simplexRank_of_after_lt h w (fun d hd => ha d (hs d hd))
    | succ p =>
      rw [coneTable_row_succ] at hw
      have hp' : p < l.length := by simpa using hp
      cases b
      · change prepend a (x.table.row p true).val w ≠ 0 at hw
        obtain ⟨q, hq, hc⟩ := prepend_support a _ w hw
        have hr := ih c h.tail p hp' true q hc
        change simplexRank (a :: c :: l) < simplexRank w.val
        rw [hq]
        change (3 : ℤ) ^ (N-a.val) - simplexRank (c :: l) <
          (3 : ℤ) ^ (N-a.val) - simplexRank q.val
        exact sub_lt_sub_left hr _
      · change ((x.table.row (p+1) true).val + prepend a (x.table.row p false).val) w ≠ 0 at hw
        have he : (x.table.row (p+1) true).val w ≠ 0 ∨
            prepend a (x.table.row p false).val w ≠ 0 := by
          by_contra hn
          simp only [not_or, not_not] at hn
          exact hw (by simp only [Finsupp.add_apply, hn.1, hn.2, add_zero])
        rcases he with he | he
        · have hs := (mem_supportedOn_iff {d | d ∈ c :: l} _).mp
            (x.supported (p+1) true) w he
          exact simplexRank_of_after_lt h w (fun d hd => ha d (hs d hd))
        · obtain ⟨q, hq, hc⟩ := prepend_support a _ w he
          have hr := ih c h.tail p hp' false q hc
          change simplexRank w.val < simplexRank (a :: c :: l)
          rw [hq]
          change (3 : ℤ) ^ (N-a.val) - simplexRank q.val <
            (3 : ℤ) ^ (N-a.val) - simplexRank (c :: l)
          exact sub_lt_sub_left hr _

end Thomason.NormalizedChains

end

end OAI
