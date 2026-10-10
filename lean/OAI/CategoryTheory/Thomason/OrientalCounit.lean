import Mathlib
import OAI.CategoryTheory.Thomason.SimplexRanks

namespace OAI

/-! Oriental Counit. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

def removeContextRow (k : ℕ) (y : Table K) (c d : K.Chain (k+1)) :
    (p : ℕ) → Bool → K.Chain p :=
  Function.update (Function.update y.row k
    (fun b => if b then y.row k true - K.d k d else y.row k false + K.d k c))
    (k+1) (fun b => y.row (k+1) b - c - d)

@[simp] lemma removeContextRow_middle (k : ℕ) (y : Table K) (c d : K.Chain (k+1)) (b : Bool) :
    removeContextRow k y c d k b =
      if b then y.row k true - K.d k d else y.row k false + K.d k c := by
  simp [removeContextRow]

@[simp] lemma removeContextRow_top (k : ℕ) (y : Table K) (c d : K.Chain (k+1)) (b : Bool) :
    removeContextRow k y c d (k+1) b = y.row (k+1) b - c - d := by
  simp [removeContextRow]

lemma removeContextRow_other (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (p : ℕ) (b : Bool) (h₀ : p ≠ k) (h₁ : p ≠ k+1) :
    removeContextRow k y c d p b = y.row p b := by simp [removeContextRow, h₀, h₁]

def removeContext (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) : Table K where
  row := removeContextRow k y c d
  positive p b := by
    by_cases h₀ : p = k
    · subst p; rw [removeContextRow_middle]; cases b; exact hs; exact he
    · by_cases h₁ : p = k+1
      · subst p; simpa using ht b
      · rw [removeContextRow_other k y c d p b h₀ h₁]; exact y.positive p b
  boundary p b := by
    by_cases h₀ : p = k
    · subst p
      rw [removeContextRow_top, removeContextRow_middle, removeContextRow_middle]
      simp only [Bool.false_eq_true, ite_false, ite_true, map_sub, y.boundary]
      abel
    · by_cases h₁ : p = k+1
      · subst p
        rw [removeContextRow_top, removeContextRow_top,
          removeContextRow_other k y c d (k+1+1) b (by omega) (by omega), y.boundary]
        abel
      · by_cases h₂ : p+1 = k
        · subst k
          rw [removeContextRow_middle,
            removeContextRow_other (p+1) y c d p true (by omega) (by omega),
            removeContextRow_other (p+1) y c d p false (by omega) (by omega)]
          cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_add, map_sub,
            K.d_d, add_zero, sub_zero, y.boundary]
        · rw [removeContextRow_other k y c d (p+1) b h₂ (by omega),
            removeContextRow_other k y c d p true h₀ h₁,
            removeContextRow_other k y c d p false h₀ h₁]
          exact y.boundary p b
  augmentation b := by
    by_cases hk : k = 0
    · subst k
      rw [removeContextRow_middle]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_add, map_sub,
        K.augmentation_d, add_zero, sub_zero, y.augmentation]
    · rw [removeContextRow_other k y c d 0 b (Ne.symm hk) (by omega)]
      exact y.augmentation b
  bounded := by
    obtain ⟨n, hn⟩ := y.bounded
    refine ⟨max n (k+1), fun p hp b => ?_⟩
    rw [removeContextRow_other k y c d p b (by omega) (by omega)]
    exact hn p (lt_of_le_of_lt (le_max_left _ _) hp) b

@[simp] lemma removeContext_row (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) (p : ℕ) (b : Bool) :
    (removeContext k y c d ht hs he).row p b = removeContextRow k y c d p b := rfl

lemma removeContext_dimension {k n : ℕ} (hkn : k < n) (y : Table K)
    (hy : truncate n false y = y) (c d : K.Chain (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) :
    truncate n false (removeContext k y c d ht hs he) = removeContext k y c d ht hs he := by
  ext p b
  rw [truncate_row]
  by_cases hp : p < n
  · exact ite_eq_left hp
  · rw [ite_eq_right hp]
    by_cases hn : p = n
    · subst p
      rw [ite_eq_left rfl]
      by_cases hk : n = k+1
      · subst n; simp only [removeContext_row, removeContextRow_top]
        cases b
        · rfl
        · rw [row_top_fixed y hy]
      · simp only [removeContext_row,
          removeContextRow_other k y c d n false (by omega) hk,
          removeContextRow_other k y c d n b (by omega) hk]
        cases b
        · rfl
        · exact row_top_fixed y hy
    · rw [ite_eq_right hn, removeContext_row, removeContextRow_other k y c d p b
        (by omega) (by omega), row_above_fixed y hy (by omega) b]

lemma factor_context (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (hc : c ∈ K.positive (k+1)) (hd : d ∈ K.positive (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) :
    ∃ (l r : Table K) (hlm : truncate k true l = truncate k false (removeContext k y c d ht hs he))
      (hmr : truncate k true (comp k l (removeContext k y c d ht hs he) hlm) = truncate k false r),
      truncate (k+1) false l = l ∧ truncate (k+1) false r = r ∧
      comp k (comp k l (removeContext k y c d ht hs he) hlm) r hmr = y := by
  let m := removeContext k y c d ht hs he
  let s := truncate k false y
  have hsf : truncate k false s = s := by simp [s, truncate_truncate_same]
  have hs' : s.row k false + K.d k c ∈ K.positive k := by simpa [s] using hs
  let l := extendTop k s hsf c hc hs'
  have hlm : truncate k true l = truncate k false m := by
    ext p b
    rw [truncate_row, truncate_row]
    by_cases hp : p < k
    · simp only [ite_eq_left hp]
      change extensionRow k s c p b = removeContextRow k y c d p b
      rw [extensionRow_other k s c p b (by omega) (by omega),
        removeContextRow_other k y c d p b (by omega) (by omega)]
      simp [s, hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
      by_cases heq : p = k
      · subst p
        simp only [ite_true]
        change extensionRow k s c k true = removeContextRow k y c d k false
        simp [s]
      · simp only [ite_eq_right heq]
  let t := truncate k true m
  have htf : truncate k false t = t := by simp [t, truncate_truncate]
  have htrow : t.row k false = y.row k true - K.d k d := by simp [t, m]
  have ht' : t.row k false + K.d k d ∈ K.positive k := by
    rw [htrow, sub_add_cancel]; exact y.positive k true
  let r := extendTop k t htf d hd ht'
  have hmr : truncate k true (comp k l m hlm) = truncate k false r := by
    rw [target_comp_le k k le_rfl, extendTop_source]
  refine ⟨l, r, hlm, hmr, extendTop_dimension k s hsf c hc hs',
    extendTop_dimension k t htf d hd ht', ?_⟩
  ext p b
  simp only [comp_row]
  by_cases hp : p < k
  · simp only [ite_eq_left hp]
    change extensionRow k s c p b = y.row p b
    rw [extensionRow_other k s c p b (by omega) (by omega)]
    simp [s, hp]
  · simp only [ite_eq_right hp]
    by_cases heq : p = k
    · subst p
      simp only [ite_true]
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        change extensionRow k s c k false = y.row k false
        simp [s]
      · simp only [ite_true]
        change extensionRow k t d k true = y.row k true
        simp only [extensionRow_middle, ite_true, htrow, sub_add_cancel]
    · simp only [ite_eq_right heq]
      by_cases hk : p = k+1
      · subst p
        change extensionRow k s c (k+1) b + removeContextRow k y c d (k+1) b +
          extensionRow k t d (k+1) b = y.row (k+1) b
        rw [extensionRow_top, extensionRow_top, removeContextRow_top]
        abel
      · change extensionRow k s c p b + removeContextRow k y c d p b +
          extensionRow k t d p b = y.row p b
        rw [extensionRow_other k s c p b heq hk, extensionRow_other k t d p b heq hk,
          removeContextRow_other k y c d p b heq hk]
        have hz₁ : s.row p b = 0 := by simp [s, hp, heq]
        have hz₂ : t.row p b = 0 := by simp [t, hp, heq]
        rw [hz₁, hz₂, zero_add, add_zero]

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma positive_common_context {a b x y : Chains E}
    (hx : Positive x) (hy : Positive y)
    (hab : ∀ w, a w ≠ 0 → b w = 0) (he : y - x = b - a) :
    Positive (x - a) ∧ y - b = x - a := by
  constructor
  · intro w
    have hh := congrArg (fun z : Chains E => z w) he
    simp only [Finsupp.sub_apply] at hh ⊢
    by_cases ha : a w = 0
    · simpa only [ha, sub_zero] using hx w
    · have hb := hab w ha
      have hp := hy w
      rw [hb] at hh
      omega
  · ext w
    have hh := congrArg (fun z : Chains E => z w) he
    simp only [Finsupp.sub_apply] at hh ⊢
    omega

lemma filter_mem_grade (z : Chains E) {k : ℕ} (hz : z ∈ grade k)
    (P : Word E → Prop) [DecidablePred P] : z.filter P ∈ grade k := by
  apply (mem_grade_iff k _).mpr
  intro w hw
  apply (mem_grade_iff k z).mp hz w
  intro he
  exact hw (by simp [Finsupp.filter_apply, he])

lemma filter_positive (z : Chains E) (hz : Positive z)
    (P : Word E → Prop) [DecidablePred P] : Positive (z.filter P) := by
  intro w
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hz w
  · exact le_rfl

noncomputable def rankBefore {N : ℕ} (z : Chains (Fin (N+1))) (r : ℤ) :
    Chains (Fin (N+1)) := z.filter (fun w => r < simplexRank w.val)

noncomputable def rankAfter {N : ℕ} (z : Chains (Fin (N+1))) (r : ℤ) :
    Chains (Fin (N+1)) := z.filter (fun w => ¬ r < simplexRank w.val)

lemma rankBefore_add_rankAfter {N : ℕ} (z : Chains (Fin (N+1))) (r : ℤ) :
    rankBefore z r + rankAfter z r = z := Finsupp.filter_add_filter_not z _

lemma boundary_nonneg_of_before {N : ℕ} {z : Chains (Fin (N+1))} (hz : Positive z)
    (r : ℤ) (hs : ∀ w, z w ≠ 0 → r < simplexRank w.val)
    (t : Word (Fin (N+1))) (ht : simplexRank t.val ≤ r) : 0 ≤ boundary z t := by
  classical
  rw [boundary_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro w hw
  apply mul_nonneg (hz w)
  by_contra hn
  have hr := ((wordBoundary_rank w t).2 (lt_of_not_ge hn)).2
  have hh := hs w (Finsupp.mem_support_iff.mp hw)
  omega

lemma boundary_nonpos_of_after {N : ℕ} {z : Chains (Fin (N+1))} (hz : Positive z)
    (r : ℤ) (hs : ∀ w, z w ≠ 0 → simplexRank w.val ≤ r)
    (t : Word (Fin (N+1))) (ht : r ≤ simplexRank t.val) : boundary z t ≤ 0 := by
  classical
  rw [boundary_apply, Finsupp.sum]
  apply Finset.sum_nonpos
  intro w hw
  apply mul_nonpos_of_nonneg_of_nonpos (hz w)
  by_contra hn
  have hr := ((wordBoundary_rank w t).1 (lt_of_not_ge hn)).2
  have hh := hs w (Finsupp.mem_support_iff.mp hw)
  omega

lemma rankBefore_boundary_nonneg {N : ℕ} {z : Chains (Fin (N+1))}
    (hz : Positive z) (r : ℤ) (t : Word (Fin (N+1))) (ht : simplexRank t.val ≤ r) :
    0 ≤ boundary (rankBefore z r) t := by
  apply boundary_nonneg_of_before (filter_positive z hz _) r _ t ht
  intro w hw
  by_contra hn
  exact hw (by simp [hn])

lemma rankAfter_boundary_nonpos {N : ℕ} {z : Chains (Fin (N+1))}
    (hz : Positive z) (r : ℤ) (t : Word (Fin (N+1))) (ht : r ≤ simplexRank t.val) :
    boundary (rankAfter z r) t ≤ 0 := by
  apply boundary_nonpos_of_after (filter_positive z hz _) r _ t ht
  intro w hw
  by_contra hn
  exact hw (by simp [lt_of_not_ge hn])

lemma rank_cut_positive {N : ℕ} {a b x y z : Chains (Fin (N+1))} (r : ℤ)
    (ha : Positive a) (hb : Positive b) (hx : Positive x) (hy : Positive y) (hz : Positive z)
    (has : ∀ w, a w ≠ 0 → r < simplexRank w.val)
    (hbs : ∀ w, b w ≠ 0 → simplexRank w.val < r)
    (he : y - x = b - a + boundary z) :
    Positive (x + boundary (rankBefore z r)) ∧
      Positive (y - boundary (rankAfter z r)) := by
  have hh (t : Word (Fin (N+1))) :
      y t - x t = b t - a t + boundary (rankBefore z r) t + boundary (rankAfter z r) t := by
    have h := congrArg (fun z : Chains (Fin (N+1)) => z t) he
    rw [← rankBefore_add_rankAfter z r, map_add] at h
    simp only [Finsupp.sub_apply, Finsupp.add_apply] at h
    linarith
  constructor
  · intro t
    change 0 ≤ x t + boundary (rankBefore z r) t
    by_cases ht : simplexRank t.val ≤ r
    · exact add_nonneg (hx t) (rankBefore_boundary_nonneg hz r t ht)
    · have ht' : r < simplexRank t.val := lt_of_not_ge ht
      have hb₀ : b t = 0 := by
        by_contra hn
        have := hbs t hn
        omega
      have hlow := rankAfter_boundary_nonpos hz r t ht'.le
      have heq := hh t
      have hp := hy t
      have hn := ha t
      rw [hb₀] at heq
      omega
  · intro t
    change 0 ≤ y t - boundary (rankAfter z r) t
    by_cases ht : r ≤ simplexRank t.val
    · exact sub_nonneg.mpr (le_trans (rankAfter_boundary_nonpos hz r t ht) (hy t))
    · have ht' : simplexRank t.val < r := lt_of_not_ge ht
      have ha₀ : a t = 0 := by
        by_contra hn
        have := has t hn
        omega
      have hhigh := rankBefore_boundary_nonneg hz r t ht'.le
      have heq := hh t
      have hp := hx t
      have hn := hb t
      rw [ha₀] at heq
      omega

lemma positive_augmentation_zero {z : Chains E} (hg : z ∈ grade 1)
    (hz : Positive z) (ha : emptyCoefficient (boundary z) = 0) : z = 0 := by
  classical
  rw [augmentation_eq_sum hg, ← chainMass_eq_sum] at ha
  by_contra hn
  obtain ⟨w, hw⟩ := Finsupp.ne_iff.mp hn
  change z w ≠ 0 at hw
  have hp : 0 < z w := lt_of_le_of_ne (hz w) (Ne.symm hw)
  have hh := chainMass_pos hz hp
  omega

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

inductive AtomPasting (N : ℕ) : Table (complex (Fin (N+1))) → Prop
  | atom (a : Fin (N+1)) (l : List (Fin (N+1))) (h : (a :: l).Pairwise (· < ·)) :
      AtomPasting N (simplexAtom a l (h.imp le_of_lt)).table
  | compose (k : ℕ) (x y) (h : truncate k true x = truncate k false y) :
      AtomPasting N x → AtomPasting N y → AtomPasting N (comp k x y h)

lemma common_atom_context {N : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (ha : (a :: l).Pairwise (· < ·)) (s : ℕ) (hs : s < l.length)
    (y : Table (complex (Fin (N+1))))
    (hy : y.row (s+1) false = (simplexAtom a l (ha.imp le_of_lt)).table.row (s+1) false) :
    Positive (y.row s false - (simplexAtom a l (ha.imp le_of_lt)).table.row s false).val ∧
      y.row s true - (simplexAtom a l (ha.imp le_of_lt)).table.row s true =
        y.row s false - (simplexAtom a l (ha.imp le_of_lt)).table.row s false := by
  let A := (simplexAtom a l (ha.imp le_of_lt)).table
  have he : y.row s true - y.row s false = A.row s true - A.row s false := by
    rw [← y.boundary s false, hy, A.boundary]
  have hraw := congrArg Subtype.val he
  change (y.row s true).val - (y.row s false).val =
    (A.row s true).val - (A.row s false).val at hraw
  obtain ⟨hz, hcommon⟩ := positive_common_context (y.positive s false) (y.positive s true)
    (fun w hw => by
      by_contra hn
      have hr₁ := simplexAtom_rank a l ha s hs false w hw
      have hr₂ := simplexAtom_rank a l ha s hs true w hn
      simp only [Bool.false_eq_true, ite_false, ite_true] at hr₁ hr₂
      omega) hraw
  exact ⟨hz, Subtype.ext hcommon⟩

lemma atom_context_pasting {N n : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (ha : (a :: l).Pairwise (· < ·)) (hlen : l.length = n+1)
    (hsmall : ∀ x : Table (complex (Fin (N+1))), truncate n false x = x → AtomPasting N x)
    (k : ℕ) (hk : k ≤ n) (y : Table (complex (Fin (N+1))))
    (hy : ∀ p, k < p → ∀ b,
      y.row p b = (simplexAtom a l (ha.imp le_of_lt)).table.row p b) : AtomPasting N y := by
  let A := (simplexAtom a l (ha.imp le_of_lt)).table
  let r := simplexRank (a :: l)
  induction k generalizing y with
  | zero =>
    have hs : 0 < l.length := by omega
    obtain ⟨hz, hcommon⟩ := common_atom_context a l ha 0 hs y (hy 1 (by omega) false)
    let z := y.row 0 false - A.row 0 false
    have haug : (complex (Fin (N+1))).augmentation z = 0 := by
      dsimp [z]
      rw [map_sub, y.augmentation, A.augmentation, sub_self]
    have hz₀ : z = 0 := Subtype.ext
      (positive_augmentation_zero z.property hz haug)
    have heq : y = A := by
      ext p b
      cases p with
      | zero =>
        cases b
        · exact sub_eq_zero.mp hz₀
        · exact sub_eq_zero.mp (hcommon.trans hz₀)
      | succ p => exact hy (p+1) (by omega) b
    rw [heq]
    exact .atom a l ha
  | succ k ih =>
    have hs : k+1 < l.length := by omega
    obtain ⟨hz, hcommon⟩ := common_atom_context a l ha (k+1) hs y
      (hy (k+1+1) (by omega) false)
    let z := y.row (k+1) false - A.row (k+1) false
    let c : (complex (Fin (N+1))).Chain (k+1) :=
      ⟨rankBefore z.val r, filter_mem_grade z.val z.property _⟩
    let d : (complex (Fin (N+1))).Chain (k+1) :=
      ⟨rankAfter z.val r, filter_mem_grade z.val z.property _⟩
    have hc : c ∈ (complex (Fin (N+1))).positive (k+1) := filter_positive z.val hz _
    have hd : d ∈ (complex (Fin (N+1))).positive (k+1) := filter_positive z.val hz _
    have hcd : c + d = z := Subtype.ext (rankBefore_add_rankAfter z.val r)
    have hrows (b : Bool) : y.row (k+1) b - c - d = A.row (k+1) b := by
      have hz' : y.row (k+1) b - A.row (k+1) b = z := by
        cases b
        · rfl
        · exact hcommon
      rw [sub_sub, hcd]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hz').trans (add_comm _ _))
    have ht : ∀ b, y.row (k+1) b - c - d ∈ (complex (Fin (N+1))).positive (k+1) := by
      intro b
      rw [hrows b]
      exact A.positive (k+1) b
    have hdiff : y.row k true - y.row k false = A.row k true - A.row k false +
        (complex (Fin (N+1))).d k z := by
      dsimp [z]
      rw [map_sub, y.boundary, A.boundary]
      abel
    have hraw := congrArg Subtype.val hdiff
    change (y.row k true).val - (y.row k false).val =
      (A.row k true).val - (A.row k false).val + boundary z.val at hraw
    obtain ⟨hstart, hend⟩ := rank_cut_positive r (A.positive k false) (A.positive k true)
      (y.positive k false) (y.positive k true) hz
      (fun w hw => simplexAtom_rank a l ha k (by omega) false w hw)
      (fun w hw => simplexAtom_rank a l ha k (by omega) true w hw) hraw
    have hstart' : y.row k false + (complex (Fin (N+1))).d k c ∈
        (complex (Fin (N+1))).positive k := hstart
    have hend' : y.row k true - (complex (Fin (N+1))).d k d ∈
        (complex (Fin (N+1))).positive k := hend
    let m := removeContext k y c d ht hstart' hend'
    have hm : AtomPasting N m := by
      apply ih (by omega) m
      intro p hp b
      change removeContextRow k y c d p b = A.row p b
      by_cases hpk : p = k+1
      · subst p
        rw [removeContextRow_top, hrows]
      · rw [removeContextRow_other k y c d p b (by omega) hpk]
        exact hy p (by omega) b
    obtain ⟨left, right, hlm, hmr, hl, hr, he⟩ := factor_context k y c d hc hd ht hstart' hend'
    rw [← he]
    exact .compose k _ _ hmr
      (.compose k _ _ hlm
        (hsmall left ((complex (Fin (N+1))).nu.source_fixed_upwards hk hl)) hm)
      (hsmall right ((complex (Fin (N+1))).nu.source_fixed_upwards hk hr))

lemma rows_above_top_agree {K : DirectedComplex.{u}} {n : ℕ} (x y : Table K)
    (hx : truncate n false x = x) (hy : truncate n false y = y)
    (ht : x.row n false = y.row n false) (p : ℕ) (hp : n ≤ p) (b : Bool) :
    x.row p b = y.row p b := by
  by_cases he : p = n
  · subst p
    cases b
    · exact ht
    · rw [← row_top_fixed x hx, ← row_top_fixed y hy, ht]
  · rw [row_above_fixed x hx (by omega) b, row_above_fixed y hy (by omega) b]

lemma oriental_atomic_pasting {N : ℕ} (n : ℕ) (y : Table (complex (Fin (N+1))))
    (hy : truncate n false y = y) : AtomPasting N y := by
  induction n generalizing y with
  | zero =>
    let x : (complex (Fin (N+1))).nu.Objects := ⟨y, hy⟩
    let a := tableObjectsEquiv x
    have he : vertexTable a = y := congrArg Subtype.val (tableObjectsEquiv.left_inv x)
    rw [← he]
    exact .atom a [] (by simp)
  | succ n ih =>
    have ht := oriental_top_pasting y hy
    clear hy
    induction ht with
    | identity x hx => exact ih x hx
    | basis x w hx hxt =>
      have hw : w.val.length = n+1+1 := by
        apply (mem_grade_iff (n+1+1) (x.row (n+1) false).val).mp
          (x.row (n+1) false).property w
        rw [hxt, bracket_of_pairwise w.property, Finsupp.single_eq_same]
        norm_num
      rcases w with ⟨w, hwp⟩
      cases w with
      | nil => simp at hw
      | cons a l =>
        have hlen : l.length = n+1 := by simpa using hw
        let A := simplexAtom a l (hwp.imp le_of_lt)
        have hdim : truncate (n+1) false A.table = A.table := by
          convert A.dimension using 1; simp [hlen]
        have htop : x.row (n+1) false = A.table.row (n+1) false := by
          apply Subtype.ext
          rw [hxt]
          have hh := A.top false
          have hidx : (a :: l).length - 1 = n+1 := by simpa using hlen
          rw [hidx] at hh
          exact hh.symm
        apply atom_context_pasting a l hwp hlen ih n le_rfl x
        intro p hp b
        exact rows_above_top_agree x A.table hx hdim htop p (by omega) b
    | compose x y h hx hy ihx ihy => exact .compose n x y h ihx ihy

lemma oriental_all_atomic {N : ℕ} (y : Table (complex (Fin (N+1)))) : AtomPasting N y := by
  obtain ⟨n, hn⟩ := (complex (Fin (N+1))).nu.finite_dimension y
  exact oriental_atomic_pasting n y hn

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

lemma dimension_of_rows_above_zero {K : DirectedComplex.{u}} {n : ℕ} (x : Table K)
    (h : ∀ p, n < p → ∀ b, x.row p b = 0) : truncate n false x = x := by
  have ht : x.row n false = x.row n true := by
    have hz := x.boundary n false
    rw [h (n+1) (by omega) false, map_zero] at hz
    exact (sub_eq_zero.mp hz.symm).symm
  ext p b
  rw [truncate_row]
  by_cases hp : p < n
  · simp only [hp, ite_true]
  · by_cases he : p = n
    · subst p
      cases b <;> simp [ht]
    · simp only [hp, ite_false, he]
      exact (h p (by omega) b).symm

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

variable {E : Type u} [PartialOrder E]

lemma positive_add_zero {x y : Chains E} (hx : Positive x) (hy : Positive y)
    (h : x+y = 0) : x = 0 ∧ y = 0 := by
  have hf (w : Word E) : x w = 0 ∧ y w = 0 := by
    have he := congrArg (fun z : Chains E => z w) h
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at he
    have hx' := hx w
    have hy' := hy w
    omega
  exact ⟨Finsupp.ext fun w => (hf w).1, Finsupp.ext fun w => (hf w).2⟩

lemma comp_dimension_factors {k n : ℕ} (x y : Table (complex E))
    (h : truncate k true x = truncate k false y)
    (hz : truncate n false (comp k x y h) = comp k x y h) :
    truncate n false x = x ∧ truncate n false y = y := by
  have habove (p : ℕ) (hp : max n k < p) (b : Bool) :
      x.row p b = 0 ∧ y.row p b = 0 := by
    have he := row_above_fixed (comp k x y h) hz (by omega : n < p) b
    rw [comp_row] at he
    simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false] at he
    have heraw := congrArg Subtype.val he
    change (x.row p b).val + (y.row p b).val = 0 at heraw
    obtain ⟨hx, hy⟩ := positive_add_zero (x.positive p b) (y.positive p b) heraw
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hx := dimension_of_rows_above_zero x (fun p hp b => (habove p hp b).1)
  have hy := dimension_of_rows_above_zero y (fun p hp b => (habove p hp b).2)
  by_cases hkn : k ≤ n
  · simpa only [max_eq_left hkn] using And.intro hx hy
  · have hnk : n ≤ k := by omega
    rw [max_eq_right hnk] at hx hy
    have hz' : truncate k false (comp k x y h) = comp k x y h :=
      (complex E).nu.source_fixed_upwards hnk hz
    have hz'' : truncate k true (comp k x y h) = comp k x y h :=
      (complex E).nu.target_eq_self_of_source_eq_self hz'
    have hzx : comp k x y h = x := by rw [← hz', source_comp_le k k le_rfl, hx]
    have hzy : comp k x y h = y := by
      rw [← hz'', target_comp_le k k le_rfl]
      exact (complex E).nu.target_eq_self_of_source_eq_self hy
    exact ⟨hzx ▸ hz, hzy ▸ hz⟩

lemma oriental_functor_ext {N : ℕ} {C : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex (Fin (N+1))).nu C)
    (h : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a :: l).Pairwise (· < ·)),
      F.map (simplexAtom a l (ha.imp le_of_lt)).table =
        G.map (simplexAtom a l (ha.imp le_of_lt)).table) : F = G := by
  apply OmegaCategory.Functor.ext
  funext x
  induction oriental_all_atomic x with
  | atom a l ha => exact h a l ha
  | compose k x y hab hx hy ihx ihy =>
    erw [F.map_comp k x y hab (F.map_composable hab),
      G.map_comp k x y hab (G.map_composable hab)]
    congr 1

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table OmegaCategory

variable {E : Type u} [PartialOrder E]

noncomputable def basisLambda (p : ℕ) (w : Word E) : (complex E).nu.LambdaChain p := by
  classical
  by_cases h : w.val.length = p+1
  · rcases w with ⟨w, hw⟩
    cases w with
    | nil => simp at h
    | cons a l =>
      let A := simplexAtom a l (hw.imp le_of_lt)
      have he : (a :: l).length-1 = p := by simp only [List.length_cons] at h ⊢; omega
      exact (complex E).nu.lambdaGen ⟨A.table, he ▸ A.dimension⟩
  · exact 0

lemma basisLambda_cons (p : ℕ) (a : E) (l : List E) (ha : (a :: l).Pairwise (· < ·))
    (h : l.length = p)
    (hd : truncate p false (simplexAtom a l (ha.imp le_of_lt)).table =
      (simplexAtom a l (ha.imp le_of_lt)).table) :
    basisLambda p ⟨a :: l, ha⟩ = (complex E).nu.lambdaGen ⟨_, hd⟩ := by
  simp [basisLambda, h]

noncomputable def atomCounitInverse (p : ℕ) :
    (complex E).Chain p →ₗ[ℤ] (complex E).nu.LambdaChain p :=
  (Finsupp.linearCombination ℤ (basisLambda p)).comp (grade (p+1)).subtype

lemma atomCounitInverse_bracket (p : ℕ) (w : Word E)
    (h : w.val.length = p+1) :
    atomCounitInverse p ⟨bracket w.val, h ▸ bracket_mem_grade w.val⟩ = basisLambda p w := by
  change Finsupp.linearCombination ℤ (basisLambda p) (bracket w.val) = _
  rw [bracket_of_pairwise w.property, Finsupp.linearCombination_single, one_smul]

lemma simplexAtom_dimension_le {N p : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (ha : (a :: l).Pairwise (· < ·))
    (h : truncate p false (simplexAtom a l (ha.imp le_of_lt)).table =
      (simplexAtom a l (ha.imp le_of_lt)).table) : l.length ≤ p := by
  by_contra hn
  have hz := row_above_fixed (simplexAtom a l (ha.imp le_of_lt)).table h
    (lt_of_not_ge hn) false
  have ht := (simplexAtom a l (ha.imp le_of_lt)).top false
  change ((simplexAtom a l (ha.imp le_of_lt)).table.row l.length false).val =
    bracket (a :: l) at ht
  rw [hz] at ht
  change 0 = bracket (a :: l) at ht
  rw [bracket_of_pairwise ha] at ht
  have he := congrArg (fun z : Chains (Fin (N+1)) => z ⟨a :: l, ha⟩) ht
  simp at he

lemma atomCounitInverse_top {N p : ℕ} (y : Table (complex (Fin (N+1))))
    (hy : truncate p false y = y) :
    atomCounitInverse p (y.row p false) = (complex (Fin (N+1))).nu.lambdaGen ⟨y, hy⟩ := by
  revert hy
  induction oriental_all_atomic y with
  | atom a l ha =>
    intro hy
    let A := simplexAtom a l (ha.imp le_of_lt)
    have hp : l.length ≤ p := simplexAtom_dimension_le a l ha hy
    by_cases he : l.length = p
    · have hr : A.table.row p false =
          (⟨bracket (a :: l), (show (a :: l).length = p+1 by simp [he]) ▸
            bracket_mem_grade (a :: l)⟩ : (complex (Fin (N+1))).Chain p) := by
        apply Subtype.ext
        have ht := A.top false
        have hd : (a :: l).length-1 = p := by simp [he]
        rwa [hd] at ht
      change atomCounitInverse p (A.table.row p false) = _
      rw [hr, atomCounitInverse_bracket p ⟨a :: l, ha⟩ (by simp [he])]
      exact basisLambda_cons p a l ha he hy
    · have hlt : l.length < p := by omega
      have hd : truncate l.length false A.table = A.table := by
        simpa only [List.length_cons, Nat.add_sub_cancel] using A.dimension
      rw [row_above_fixed A.table hd hlt false, map_zero]
      exact ((complex (Fin (N+1))).nu.lambdaGen_degenerate hlt ⟨A.table, hy⟩ hd).symm
  | compose k x y h hx hy ihx ihy =>
    intro hz
    obtain ⟨hxd, hyd⟩ := comp_dimension_factors x y h hz
    by_cases hkp : k < p
    · have hgraded : (⟨comp k x y h, hz⟩ : (complex (Fin (N+1))).nu.Cells p) =
          (complex (Fin (N+1))).nu.gradedComp hkp ⟨x, hxd⟩ ⟨y, hyd⟩ h := rfl
      rw [hgraded]
      erw [(complex (Fin (N+1))).nu.lambdaGen_comp hkp]
      rw [comp_row]
      simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false]
      rw [map_add, ihx hxd, ihy hyd]
    · have hpk : p ≤ k := by omega
      have hz' : truncate k false (comp k x y h) = comp k x y h :=
        (complex (Fin (N+1))).nu.source_fixed_upwards hpk hz
      have hx' : truncate k false x = x :=
        (complex (Fin (N+1))).nu.source_fixed_upwards hpk hxd
      have he : comp k x y h = x := by rw [← hz', source_comp_le k k le_rfl, hx']
      have hecell : (⟨comp k x y h, hz⟩ : (complex (Fin (N+1))).nu.Cells p) =
          ⟨x, hxd⟩ := Subtype.ext he
      rw [hecell, he]
      exact ihx hxd

lemma oriental_lambdaCounit_leftInverse {N : ℕ} (p : ℕ) :
    (atomCounitInverse p).comp ((complex (Fin (N+1))).lambdaCounitMap p) =
      LinearMap.id := by
  apply (complex (Fin (N+1))).nu.lambda_linear_ext
  intro x
  change atomCounitInverse p ((complex (Fin (N+1))).lambdaCounitMap p
    ((complex (Fin (N+1))).nu.lambdaGen x)) = (complex (Fin (N+1))).nu.lambdaGen x
  rw [(complex (Fin (N+1))).lambdaCounitMap_gen]
  exact atomCounitInverse_top x.val x.property

lemma oriental_lambdaCounit_injective {N : ℕ} (p : ℕ) :
    Function.Injective ((complex (Fin (N+1))).lambdaCounitMap p) := by
  apply Function.HasLeftInverse.injective
  refine ⟨atomCounitInverse p, ?_⟩
  intro x
  exact LinearMap.congr_fun (oriental_lambdaCounit_leftInverse p) x

end Thomason.NormalizedChains

end

end OAI
