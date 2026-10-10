import OAI.Probability.FKMaps.Vervaat

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def walk {N : ℕ} (d : Fin N → Fin N) (j : ℕ) : ℤ :=
  ∑ i : Fin N, if i.val < j then ((d i).val : ℤ) - 1 else 0


def IsTreeCode {N : ℕ} (d : Fin N → Fin N) : Prop :=
  walk d N = -1 ∧ ∀ j < N, 0 ≤ walk d j


abbrev Code (N : ℕ) := {d : Fin N → Fin N // IsTreeCode d}


instance (N : ℕ) : Fintype (Code N) := Fintype.ofFinite _


def height {N : ℕ} (d : Fin N → Fin N) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin N => k.val < j ∧
    ∀ r : Fin (N+1), k.val ≤ r.val → r.val ≤ j → walk d k.val ≤ walk d r.val)).card


def jointCode {N : ℕ} (σ : ℝ) (d : Code N) : C(unitInterval, ℝ × ℝ) :=
  (interpolation N (fun i => (walk d.val i.val : ℝ) / (σ * Real.sqrt N))).prodMk
    (interpolation N (fun i => σ * height d.val i.val / (2 * Real.sqrt N)))


def codeWeight {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) : ℝ :=
  ∏ i : Fin N, p.mass (d.val i).val


def codePartition (p : CriticalEvenOffspring) (N : ℕ) : ℝ :=
  ∑ d : Code N, codeWeight p d


def codeExpectation (p : CriticalEvenOffspring) (N : ℕ)
    (F : C(unitInterval, ℝ × ℝ) → ℝ) : ℝ :=
  ∑ d : Code N, (codeWeight p d / codePartition p N) * F (jointCode p.sigma d)


@[simp] lemma walk_zero {N : ℕ} (d : Fin N → Fin N) : walk d 0 = 0 := by simp [walk]


lemma codeWeight_nonneg {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) :
    0 ≤ codeWeight p d := Finset.prod_nonneg (fun _i _ => p.nonneg _)


lemma codePartition_nonneg (p : CriticalEvenOffspring) (N : ℕ) :
    0 ≤ codePartition p N := Finset.sum_nonneg (fun d _ => codeWeight_nonneg p d)


@[simp] lemma height_terminal {N : ℕ} (d : Code N) : height d.val N = 0 := by
  unfold height
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  have h := hk.2 ⟨N, Nat.lt_succ_self N⟩ k.isLt.le le_rfl
  rw [d.property.1] at h
  have h' := d.property.2 k.val k.isLt
  omega


lemma walk_step {N : ℕ} (d : Fin N → Fin N) {j : ℕ} (hj : j < N) :
    walk d (j+1) = walk d j + ((d ⟨j, hj⟩).val : ℤ) - 1 := by
  have hsplit : ∀ i : Fin N,
      (if i.val < j+1 then ((d i).val : ℤ) - 1 else 0) =
        (if i.val < j then ((d i).val : ℤ) - 1 else 0) +
        (if i = ⟨j, hj⟩ then ((d i).val : ℤ) - 1 else 0) := by
    intro i
    by_cases h : i = ⟨j, hj⟩
    · subst i
      simp
    · have hv : i.val ≠ j := fun hv => h (Fin.ext hv)
      by_cases hi : i.val < j <;> simp [hi, h, show (i.val < j+1) ↔ i.val < j by omega]
  simp only [walk, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  omega


def binaryCombDegrees (n : ℕ) : Fin (2*n+1) → Fin (2*n+1) := fun i =>
  ⟨if i.val < n then 2 else 0, by split_ifs <;> omega⟩


lemma walk_binaryComb (n : ℕ) {j : ℕ} (hj : j ≤ 2*n+1) :
    walk (binaryCombDegrees n) j = if j ≤ n then (j : ℤ) else 2*(n : ℤ) - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [walk_step _ (by omega), ih (by omega)]
    simp only [binaryCombDegrees, Nat.cast_ite, Nat.cast_ofNat]
    split_ifs <;> omega


def binaryComb (n : ℕ) : Code (2*n+1) :=
  ⟨binaryCombDegrees n, by
    constructor
    · rw [walk_binaryComb _ (le_refl _), ite_eq_right (by omega)]
      push_cast
      omega
    · intro j hj
      rw [walk_binaryComb _ hj.le]
      split_ifs <;> omega⟩


lemma codeWeight_binaryComb_pos (p : CriticalEvenOffspring) (n : ℕ) :
    0 < codeWeight p (binaryComb n) := by
  apply Finset.prod_pos
  intro i _
  change 0 < p.mass (if i.val < n then 2 else 0)
  split_ifs
  · exact p.two_pos
  · exact p.zero_pos


lemma codePartition_odd_pos (p : CriticalEvenOffspring) (n : ℕ) :
    0 < codePartition p (2*n+1) := by
  apply lt_of_lt_of_le (codeWeight_binaryComb_pos p n)
  exact Finset.single_le_sum (fun d _ => codeWeight_nonneg p d) (Finset.mem_univ _)


lemma Code.sum_degrees {N : ℕ} (d : Code N) :
    (∑ i : Fin N, (d.val i).val) + 1 = N := by
  have h := d.property.1
  simp only [walk, Fin.is_lt, ite_true, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hcast : (∑ i : Fin N, ((d.val i).val : ℤ)) =
      ((∑ i : Fin N, (d.val i).val : ℕ) : ℤ) := by simp
  rw [hcast] at h
  omega


lemma codeWeight_eq_zero_of_not_odd (p : CriticalEvenOffspring) {N : ℕ}
    (hN : ¬ Odd N) (d : Code N) : codeWeight p d = 0 := by
  by_contra hw
  have heven : ∀ i : Fin N, Even (d.val i).val := by
    intro i
    rcases Nat.even_or_odd (d.val i).val with hi | hi
    · exact hi
    · have hz := p.even_support (d.val i).val hi
      have hprod : codeWeight p d = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      contradiction
  have hevenSum : Even (∑ i : Fin N, (d.val i).val) :=
    Finset.even_sum _ (fun i _ => heven i)
  apply hN
  rw [← d.sum_degrees]
  exact hevenSum.add_odd (by decide)


lemma codePartition_eq_zero_of_not_odd (p : CriticalEvenOffspring) {N : ℕ}
    (hN : ¬ Odd N) : codePartition p N = 0 := by
  exact Finset.sum_eq_zero (fun d _ => codeWeight_eq_zero_of_not_odd p hN d)


lemma codeExpectation_one (p : CriticalEvenOffspring) (n : ℕ) :
    codeExpectation p (2*n+1) (fun _ => 1) = 1 := by
  simp only [codeExpectation, mul_one, ← Finset.sum_div]
  exact div_self (codePartition_odd_pos p n).ne'


def prefixSum (l : List ℤ) (j : ℕ) : ℤ := (l.take j).sum


def IsExcursionList (l : List ℤ) : Prop :=
  l.sum = -1 ∧ ∀ j < l.length, 0 ≤ prefixSum l j


def FirstMinimum (l : List ℤ) (m : ℕ) : Prop :=
  m < l.length ∧ (∀ j < l.length, prefixSum l m ≤ prefixSum l j) ∧
    ∀ j < m, prefixSum l m < prefixSum l j


@[simp] lemma prefixSum_zero (l : List ℤ) : prefixSum l 0 = 0 := by simp [prefixSum]


@[simp] lemma prefixSum_length (l : List ℤ) : prefixSum l l.length = l.sum := by
  simp [prefixSum]


lemma prefixSum_drop (l : List ℤ) (m j : ℕ) :
    prefixSum (l.drop m) j = prefixSum l (m + j) - prefixSum l m := by
  simp only [prefixSum, List.take_add, List.sum_append]
  omega


lemma sum_drop (l : List ℤ) (m : ℕ) :
    (l.drop m).sum = l.sum - prefixSum l m := by
  have := congrArg List.sum (List.take_append_drop m l)
  simp only [List.sum_append] at this
  unfold prefixSum
  omega


lemma prefixSum_rotate_left (l : List ℤ) {m j : ℕ} (hm : m ≤ l.length)
    (hj : j ≤ l.length - m) :
    prefixSum (l.rotate m) j = prefixSum l (m + j) - prefixSum l m := by
  rw [List.rotate_eq_drop_append_take hm]
  rw [prefixSum, List.take_append_of_le_length (by simpa using hj)]
  exact prefixSum_drop l m j


lemma prefixSum_rotate_right (l : List ℤ) {m j : ℕ} (hm : m ≤ l.length)
    (hj : l.length - m ≤ j) (hj' : j ≤ l.length) :
    prefixSum (l.rotate m) j = l.sum - prefixSum l m +
      prefixSum l (j - (l.length - m)) := by
  rw [List.rotate_eq_drop_append_take hm]
  simp only [prefixSum, List.take_append, List.length_drop, List.sum_append]
  rw [List.take_of_length_le (by simpa using hj), List.take_take,
    Nat.min_eq_left (by omega)]
  rw [sum_drop]
  rfl


lemma exists_firstListMinimum {l : List ℤ} (hl : l ≠ []) : ∃ m, FirstMinimum l m := by
  have hex : ∃ m, m < l.length ∧ ∀ j < l.length, prefixSum l m ≤ prefixSum l j := by
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.range l.length)
      (prefixSum l) (by simpa using hl)
    exact ⟨m, Finset.mem_range.mp hm, fun j hj => hmin j (Finset.mem_range.mpr hj)⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  refine ⟨m, hm.1, hm.2, ?_⟩
  intro j hj
  have hjN : j < l.length := lt_trans hj hm.1
  by_contra h
  have hle : prefixSum l j ≤ prefixSum l m := le_of_not_gt h
  have hjmin : j < l.length ∧ ∀ k < l.length, prefixSum l j ≤ prefixSum l k :=
    ⟨hjN, fun k hk => hle.trans (hm.2 k hk)⟩
  have hfind := Nat.find_min' hex hjmin
  omega


lemma FirstMinimum.unique {l : List ℤ} {m r : ℕ}
    (hm : FirstMinimum l m) (hr : FirstMinimum l r) : m = r := by
  rcases lt_trichotomy m r with h | h | h
  · have h1 := hm.2.1 r hr.1
    have h2 := hr.2.2 m h
    omega
  · exact h
  · have h1 := hr.2.1 m hm.1
    have h2 := hm.2.2 r h
    omega


lemma isExcursionList_rotate_of_firstMinimum {l : List ℤ} (hs : l.sum = -1)
    {m : ℕ} (hm : FirstMinimum l m) : IsExcursionList (l.rotate m) := by
  refine ⟨(List.rotate_perm l m).sum_eq.trans hs, ?_⟩
  intro j hj
  rw [List.length_rotate] at hj
  by_cases hleft : j < l.length - m
  · rw [prefixSum_rotate_left l hm.1.le hleft.le]
    exact sub_nonneg.mpr (hm.2.1 _ (by omega))
  · rw [prefixSum_rotate_right l hm.1.le (by omega) hj.le, hs]
    have hmin := hm.2.2 (j - (l.length - m)) (by omega)
    omega


lemma firstMinimum_of_isExcursionList_rotate {l : List ℤ} (hs : l.sum = -1)
    {m : ℕ} (hm : m < l.length) (he : IsExcursionList (l.rotate m)) :
    FirstMinimum l m := by
  have hnonneg : ∀ j < l.length, 0 ≤ prefixSum (l.rotate m) j := by
    simpa only [List.length_rotate] using he.2
  have hstrict : ∀ j < m, prefixSum l m < prefixSum l j := by
    intro j hj
    have hsum := hnonneg (l.length - m + j) (by omega)
    rw [prefixSum_rotate_right l hm.le (by omega) (by omega), hs] at hsum
    have hcancel : l.length - m + j - (l.length - m) = j := by omega
    rw [hcancel] at hsum
    omega
  refine ⟨hm, ?_, hstrict⟩
  intro j hj
  by_cases hjm : j < m
  · exact (hstrict j hjm).le
  · have hsum := hnonneg (j - m) (by omega)
    rw [prefixSum_rotate_left l hm.le (by omega)] at hsum
    have hcancel : m + (j - m) = j := by omega
    rw [hcancel] at hsum
    omega


theorem existsUnique_excursion_rotation {l : List ℤ} (hs : l.sum = -1) :
    ∃! m : ℕ, m < l.length ∧ IsExcursionList (l.rotate m) := by
  have hl : l ≠ [] := by rintro rfl; simp at hs
  obtain ⟨m, hm⟩ := exists_firstListMinimum hl
  refine ⟨m, ⟨hm.1, isExcursionList_rotate_of_firstMinimum hs hm⟩, ?_⟩
  rintro r ⟨hr, he⟩
  exact (firstMinimum_of_isExcursionList_rotate hs hr he).unique hm


lemma weighted_unique_rotation {α J : Type*} [Fintype α] [Fintype J]
    (r : J → Equiv.Perm α) (w : α → ℝ) (good : α → Prop) [DecidablePred good]
    (hinv : ∀ j a, w (r j a) = w a)
    (hunique : ∀ a, ∃! j, good (r j a)) :
    ∑ a : α, w a = (Fintype.card J : ℝ) * ∑ a : α, if good a then w a else 0 := by
  classical
  have hrow : ∀ a, (∑ j : J, if good (r j a) then w (r j a) else 0) = w a := by
    intro a
    obtain ⟨j, hj, heq⟩ := hunique a
    rw [Finset.sum_eq_single j]
    · simp [hj, hinv]
    · intro k _ hkj
      have hk : ¬ good (r k a) := fun hk => hkj (heq k hk)
      simp [hk]
    · simp
  calc
    ∑ a : α, w a = ∑ a : α, ∑ j : J, if good (r j a) then w (r j a) else 0 :=
      Finset.sum_congr rfl (fun a _ => (hrow a).symm)
    _ = ∑ j : J, ∑ a : α, if good (r j a) then w (r j a) else 0 := Finset.sum_comm
    _ = ∑ _j : J, ∑ a : α, if good a then w a else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp (r j) (fun a => if good a then w a else 0)
    _ = _ := by simp [nsmul_eq_mul]


abbrev Bridge (N : ℕ) := {d : Fin N → Fin N // walk d N = -1}


instance (N : ℕ) : Fintype (Bridge N) := Fintype.ofFinite _


def degreeList {N : ℕ} (d : Fin N → Fin N) : List ℤ :=
  List.ofFn (fun i => ((d i).val : ℤ) - 1)


@[simp] lemma degreeList_length {N : ℕ} (d : Fin N → Fin N) :
    (degreeList d).length = N := List.length_ofFn


lemma degreeList_prefixSum {N : ℕ} (d : Fin N → Fin N) (j : ℕ) :
    prefixSum (degreeList d) j = walk d j := by
  simp only [prefixSum, degreeList, List.sum_take_ofFn, walk, Finset.sum_filter]


lemma degreeList_sum {N : ℕ} (d : Fin N → Fin N) :
    (degreeList d).sum = walk d N := by
  simp [degreeList, List.sum_ofFn, walk]


lemma isTreeCode_iff {N : ℕ} (d : Fin N → Fin N) :
    IsTreeCode d ↔ IsExcursionList (degreeList d) := by
  simp [IsTreeCode, IsExcursionList, degreeList_sum, degreeList_prefixSum]


def rotateDegrees {N : ℕ} [NeZero N] (m : Fin N) : Equiv.Perm (Fin N → Fin N) where
  toFun d i := d (i + m)
  invFun d i := d (i - m)
  left_inv d := by funext i; simp
  right_inv d := by funext i; simp


lemma degreeList_rotate {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N) :
    degreeList (rotateDegrees m d) = (degreeList d).rotate m.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [degreeList, List.getElem_ofFn, List.getElem_rotate, List.length_ofFn,
      rotateDegrees, Equiv.coe_fn_mk, Fin.add_def]


lemma walk_rotate_terminal {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N) :
    walk (rotateDegrees m d) N = walk d N := by
  rw [← degreeList_sum, degreeList_rotate, (List.rotate_perm _ _).sum_eq, degreeList_sum]


def rotateBridge {N : ℕ} [NeZero N] (m : Fin N) : Equiv.Perm (Bridge N) :=
  (rotateDegrees m).subtypeEquiv (fun d => by rw [walk_rotate_terminal])


lemma Bridge.unique_good_rotation {N : ℕ} [NeZero N] (d : Bridge N) :
    ∃! m : Fin N, IsTreeCode (rotateBridge m d).val := by
  have hs : (degreeList d.val).sum = -1 := (degreeList_sum _).trans d.property
  obtain ⟨m, hm, huniq⟩ := existsUnique_excursion_rotation hs
  refine ⟨⟨m, by simpa using hm.1⟩, ?_, ?_⟩
  · change IsTreeCode (rotateDegrees ⟨m, by simpa using hm.1⟩ d.val)
    rw [isTreeCode_iff]
    exact (degreeList_rotate ⟨m, by simpa using hm.1⟩ d.val).symm ▸ hm.2
  · intro k hk
    apply Fin.ext
    apply huniq _
    refine ⟨by simpa only [degreeList_length] using k.isLt, ?_⟩
    rw [isTreeCode_iff] at hk
    simpa only [rotateBridge, Equiv.subtypeEquiv_apply, degreeList_rotate] using hk


def bridgeWeight {N : ℕ} (p : CriticalEvenOffspring) (d : Bridge N) : ℝ :=
  ∏ i : Fin N, p.mass (d.val i).val


def bridgePartition (p : CriticalEvenOffspring) (N : ℕ) : ℝ :=
  ∑ d : Bridge N, bridgeWeight p d


lemma bridgeWeight_rotate {N : ℕ} [NeZero N] (p : CriticalEvenOffspring)
    (d : Bridge N) (m : Fin N) : bridgeWeight p (rotateBridge m d) = bridgeWeight p d := by
  exact Equiv.prod_comp (Equiv.addRight m) (fun i => p.mass (d.val i).val)


theorem codePartition_cyclic (p : CriticalEvenOffspring) {N : ℕ} (hN : 0 < N) :
    bridgePartition p N = (N : ℝ) * codePartition p N := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  have h := weighted_unique_rotation (rotateBridge (N := N)) (bridgeWeight p)
    (fun d => IsTreeCode d.val) (fun m d => bridgeWeight_rotate p d m)
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  change (∑ d : Bridge N, bridgeWeight p d) = _
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  unfold codePartition
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Equiv.sum_comp e (fun d => bridgeWeight p d.val)).symm


def bridgeEmbedding (N : ℕ) : Bridge N ↪ (Fin N → ℕ) where
  toFun d i := (d.val i).val
  inj' := by
    intro d e h
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun h i)


lemma totalStep_bridge {N : ℕ} (d : Bridge N) : totalStep (bridgeEmbedding N d) = -1 := by
  have heq : totalStep (bridgeEmbedding N d) = walk d.val N := by
    simp only [totalStep, walk, Fin.is_lt, ite_true]
    rfl
  exact heq.trans d.property


lemma totalStep_bridge_range (N : ℕ) :
    {d : Fin N → ℕ | totalStep d = -1} = Set.range (bridgeEmbedding N) := by
  ext d
  constructor
  · intro hd
    have hsum : (∑ i, d i) + 1 = N := by
      rw [Set.mem_ofPred_eq, totalStep_eq_sum_sub] at hd
      omega
    have hbound (i : Fin N) : d i < N := by
      have hle : d i ≤ ∑ k, d k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    let f : Fin N → Fin N := fun i => ⟨d i, hbound i⟩
    have hf : walk f N = -1 := by
      have : walk f N = totalStep d := by simp [walk, totalStep, f]
      exact this.trans hd
    exact ⟨⟨f, hf⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact totalStep_bridge b


lemma CriticalEvenOffspring.bridgePartition_eq_iid (p : CriticalEvenOffspring) (N : ℕ) :
    bridgePartition p N = (p.iidLaw N).real {d | totalStep d = -1} := by
  classical
  have hset : {d : Fin N → ℕ | totalStep d = -1} =
      ⋃ b : Bridge N, {bridgeEmbedding N b} := by
    rw [totalStep_bridge_range]
    ext d
    simp
  have hdis : Pairwise (fun b c : Bridge N => Disjoint ({bridgeEmbedding N b} : Set (Fin N → ℕ)) {bridgeEmbedding N c}) := by
    intro b c hbc
    exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
  rw [measureReal_def, hset, measure_iUnion hdis (fun _ => measurableSet_singleton _),
    tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [CriticalEvenOffspring.iidLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


@[simp] lemma rotateBridge_zero {N : ℕ} [NeZero N] (d : Bridge N) :
    rotateBridge (0 : Fin N) d = d := by
  apply Subtype.ext
  funext i
  simp [rotateBridge, rotateDegrees]


lemma rotateBridge_add {N : ℕ} [NeZero N] (a b : Fin N) (d : Bridge N) :
    rotateBridge a (rotateBridge b d) = rotateBridge (a+b) d := by
  apply Subtype.ext
  funext i
  simp [rotateBridge, rotateDegrees, add_assoc]


def goodRotation {N : ℕ} [NeZero N] (d : Bridge N) : Fin N :=
  d.unique_good_rotation.exists.choose


lemma goodRotation_spec {N : ℕ} [NeZero N] (d : Bridge N) :
    IsTreeCode (rotateBridge (goodRotation d) d).val :=
  d.unique_good_rotation.exists.choose_spec


def canonicalCode {N : ℕ} [NeZero N] (d : Bridge N) : Code N :=
  ⟨(rotateBridge (goodRotation d) d).val, goodRotation_spec d⟩


lemma goodRotation_of_code {N : ℕ} [NeZero N] (d : Bridge N)
    (hd : IsTreeCode d.val) : goodRotation d = 0 := by
  apply d.unique_good_rotation.unique (goodRotation_spec d)
  simpa using hd


@[simp] lemma canonicalCode_of_code {N : ℕ} [NeZero N] (d : Code N) :
    canonicalCode (⟨d.val, d.property.1⟩ : Bridge N) = d := by
  apply Subtype.ext
  change (rotateBridge (goodRotation ⟨d.val, d.property.1⟩) _).val = d.val
  rw [goodRotation_of_code _ d.property, rotateBridge_zero]


lemma goodRotation_add {N : ℕ} [NeZero N] (d : Bridge N) (m : Fin N) :
    goodRotation (rotateBridge m d) + m = goodRotation d := by
  apply d.unique_good_rotation.unique _ (goodRotation_spec d)
  rw [← rotateBridge_add]
  exact goodRotation_spec (rotateBridge m d)


@[simp] lemma canonicalCode_rotate {N : ℕ} [NeZero N] (d : Bridge N) (m : Fin N) :
    canonicalCode (rotateBridge m d) = canonicalCode d := by
  apply Subtype.ext
  change (rotateBridge _ (rotateBridge m d)).val = (rotateBridge _ d).val
  rw [rotateBridge_add, goodRotation_add]


theorem canonicalCode_weighted_sum (p : CriticalEvenOffspring)
    {N : ℕ} [NeZero N] (F : Code N → ℝ) :
    ∑ d : Bridge N, bridgeWeight p d * F (canonicalCode d) =
      (N : ℝ) * ∑ d : Code N, codeWeight p d * F d := by
  classical
  have h := weighted_unique_rotation (rotateBridge (N := N))
    (fun d => bridgeWeight p d * F (canonicalCode d))
    (fun d => IsTreeCode d.val)
    (fun m d => by rw [bridgeWeight_rotate, canonicalCode_rotate])
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro d _
  change bridgeWeight p ⟨d.val, d.property.1⟩ *
    F (canonicalCode ⟨d.val, d.property.1⟩) = codeWeight p d * F d
  rw [canonicalCode_of_code]
  rfl


theorem canonicalCode_expectation (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    ∑ d : Bridge (2*n+1), (bridgeWeight p d / bridgePartition p (2*n+1)) *
      F (canonicalCode d) =
    ∑ d : Code (2*n+1), (codeWeight p d / codePartition p (2*n+1)) * F d := by
  let : NeZero (2*n+1) := ⟨by omega⟩
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, canonicalCode_weighted_sum,
    codePartition_cyclic p (by omega)]
  rw [mul_div_mul_left _ _ (by positivity : ((2*n+1 : ℕ) : ℝ) ≠ 0)]


lemma CriticalEvenOffspring.iid_bridge_singleton (p : CriticalEvenOffspring)
    {N : ℕ} (b : Bridge N) :
    (p.iidLaw N).real {bridgeEmbedding N b} = bridgeWeight p b := by
  rw [measureReal_def, iidLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


lemma CriticalEvenOffspring.bridge_integral_eq (p : CriticalEvenOffspring) (N : ℕ)
    (F : (Fin N → ℕ) → ℝ) :
    ∫ d, F d ∂cond (p.iidLaw N) {d | totalStep d = -1} =
      ∑ b : Bridge N, (bridgeWeight p b / bridgePartition p N) * F (bridgeEmbedding N b) := by
  classical
  have hset : {d : Fin N → ℕ | totalStep d = -1} = ⋃ b : Bridge N, {bridgeEmbedding N b} := by
    rw [totalStep_bridge_range]
    ext d
    simp
  have hdis : Pairwise (fun b c : Bridge N => Disjoint ({bridgeEmbedding N b} : Set (Fin N → ℕ))
      {bridgeEmbedding N c}) := by
    intro b c hbc
    exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
  have hi (b : Bridge N) : IntegrableOn F {bridgeEmbedding N b} (p.iidLaw N) :=
    IntegrableOn.of_finite (Set.finite_singleton _)
  rw [ProbabilityTheory.cond,integral_smul_measure,hset,integral_iUnion_fintype (fun _ => measurableSet_singleton _) hdis hi]
  simp only [integral_singleton,smul_eq_mul,ENNReal.toReal_inv]
  rw [← hset,← measureReal_def,← p.bridgePartition_eq_iid,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [p.iid_bridge_singleton]
  ring


def bridgeFromArray {N : ℕ} (d : Fin N → ℕ) (hd : totalStep d = -1) : Bridge N :=
  ((totalStep_bridge_range N) ▸ hd : d ∈ Set.range (bridgeEmbedding N)).choose


lemma bridgeFromArray_spec {N : ℕ} (d : Fin N → ℕ) (hd : totalStep d = -1) :
    bridgeEmbedding N (bridgeFromArray d hd)=d :=
  ((totalStep_bridge_range N) ▸ hd : d ∈ Set.range (bridgeEmbedding N)).choose_spec


@[simp] lemma bridgeFromArray_embedding {N : ℕ} (b : Bridge N) (hd : totalStep (bridgeEmbedding N b) = -1) :
    bridgeFromArray (bridgeEmbedding N b) hd=b := by
  exact (bridgeEmbedding N).injective (bridgeFromArray_spec _ _)


def arrayTree (n : ℕ) (d : Fin (2*n+1) → ℕ) : Code (2*n+1) := by
  let : NeZero (2*n+1) := ⟨by omega⟩
  exact if h : totalStep d = -1 then canonicalCode (bridgeFromArray d h) else binaryComb n


lemma arrayTree_embedding (n : ℕ) (b : Bridge (2*n+1)) :
    arrayTree n (bridgeEmbedding (2*n+1) b)=canonicalCode b := by
  simp [arrayTree,totalStep_bridge]


theorem CriticalEvenOffspring.arrayTree_expectation (p : CriticalEvenOffspring)
    (n : ℕ) (F : Code (2*n+1) → ℝ) :
    ∫ d, F (arrayTree n d) ∂cond (p.iidLaw (2*n+1)) {d | totalStep d = -1} =
      ∑ b : Code (2*n+1), (codeWeight p b / codePartition p (2*n+1))*F b := by
  rw [p.bridge_integral_eq]
  simp only [arrayTree_embedding]
  exact canonicalCode_expectation p n F


lemma interpolation_interval_formula {N j : ℕ} (hj : j<N)
    (a : Fin (N+1) → ℝ) (t : unitInterval)
    (hl : (j:ℝ) ≤ (N:ℝ)*(t:ℝ)) (hu : (N:ℝ)*(t:ℝ) ≤ j+1) :
    interpolation N a t =
      (1-((N:ℝ)*(t:ℝ)-j))*a ⟨j,by omega⟩ +
        ((N:ℝ)*(t:ℝ)-j)*a ⟨j+1,by omega⟩ := by
  classical
  let i : Fin (N+1) := ⟨j,by omega⟩
  let k : Fin (N+1) := ⟨j+1,by omega⟩
  have hik : i ≠ k := by intro he; have := congrArg Fin.val he; dsimp [i,k] at this; omega
  have hz (r : Fin (N+1)) (hr : r∉({i,k} : Finset (Fin (N+1)))) :
      a r*hat N r.val t=0 := by
    have hir : r.val ≠ j := by
      intro he
      apply hr
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inl (Fin.ext he)
    have hkr : r.val ≠ j+1 := by
      intro he
      apply hr
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inr (Fin.ext he)
    suffices hat N r.val t=0 by rw [this,mul_zero]
    change max 0 (1-|(N:ℝ)*(t:ℝ)-(r.val:ℝ)|)=0
    apply max_eq_left
    rcases lt_or_gt_of_ne hir with h | h
    · have hh : (r.val:ℝ)+1 ≤ j := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h' : j+2 ≤ r.val := by omega
      have hh : (j:ℝ)+2 ≤ r.val := by exact_mod_cast h'
      rw [abs_of_nonpos (by linarith)]
      linarith
  rw [interpolation_apply,← Finset.sum_subset (Finset.subset_univ {i,k}) (fun r _ hr => hz r hr)]
  rw [Finset.sum_pair hik]
  change a i*max 0 (1-|(N:ℝ)*(t:ℝ)-j|)+
    a k*max 0 (1-|(N:ℝ)*(t:ℝ)-(j+1:ℕ)|)=_
  rw [Nat.cast_add,Nat.cast_one,abs_of_nonneg (by linarith),abs_of_nonpos (by linarith),
    max_eq_right (by linarith),max_eq_right (by linarith)]
  dsimp [i,k]
  ring


lemma interpolation_ge {N : ℕ} (a : Fin (N+1) → ℝ) {c : ℝ}
    (h : ∀ i, c ≤ a i) (t : unitInterval) : c ≤ interpolation N a t := by
  rw [interpolation_apply]
  calc
    c = ∑ i : Fin (N+1), c*hat N i.val t := by rw [← Finset.mul_sum,hat_sum,mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (hat_nonneg _ _ _)


lemma interpolation_strict_before {N : ℕ} (hN : 0<N) (a : Fin (N+1) → ℝ)
    (m : Fin (N+1)) (hmin : ∀ i, a m≤a i) (hfirst : ∀ i, i < m → a m < a i)
    (t : unitInterval) (ht : t<gridPoint N m) : a m < interpolation N a t := by
  have hNR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hNt : (N:ℝ)*(t:ℝ) < m.val := by
    have hh : (t:ℝ)<(m.val:ℝ)/(N:ℝ) := ht
    nlinarith [(lt_div_iff₀ hNR).mp hh]
  have hz : 0≤(N:ℝ)*(t:ℝ) := mul_nonneg hNR.le t.property.1
  let j := ⌊(N:ℝ)*(t:ℝ)⌋₊
  have hjx : (j:ℝ)≤(N:ℝ)*(t:ℝ) := Nat.floor_le hz
  have hxj : (N:ℝ)*(t:ℝ)<(j:ℝ)+1 := Nat.lt_floor_add_one _
  have hjm : j < m.val := by exact_mod_cast (hjx.trans_lt hNt)
  have hjN : j<N := hjm.trans_le (Nat.le_of_lt_succ m.isLt)
  rw [interpolation_interval_formula hjN a t hjx hxj.le]
  have ha := hfirst ⟨j,by omega⟩ hjm
  have hb := hmin ⟨j+1,by omega⟩
  have hc : 0<1-((N:ℝ)*(t:ℝ)-j) := by linarith
  have hd : 0≤(N:ℝ)*(t:ℝ)-j := by linarith
  nlinarith [mul_pos hc (sub_pos.mpr ha),mul_nonneg hd (sub_nonneg.mpr hb)]


lemma exists_grid_interval {N : ℕ} (hN : 0<N) (t : unitInterval) :
    ∃ j : ℕ, j<N ∧ (j:ℝ) ≤ (N:ℝ)*(t:ℝ) ∧ (N:ℝ)*(t:ℝ) ≤ j+1 := by
  by_cases ht : t=1
  · have hcast : ((N-1:ℕ):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    refine ⟨N-1,by omega,?_,?_⟩
    · subst t
      change ((N-1:ℕ):ℝ)≤(N:ℝ)*1
      rw [hcast,mul_one]
      linarith
    · subst t
      change (N:ℝ)*1≤((N-1:ℕ):ℝ)+1
      rw [hcast,mul_one]
      linarith
  · have hlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun he => ht (Subtype.ext he))
    let j := ⌊(N:ℝ)*(t:ℝ)⌋₊
    have hj : (j:ℝ)≤(N:ℝ)*(t:ℝ) := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) t.property.1)
    have h' : (N:ℝ)*(t:ℝ)<N := by nlinarith [show (0:ℝ)<N from Nat.cast_pos.mpr hN]
    refine ⟨j,?_,hj,(Nat.lt_floor_add_one _).le⟩
    exact_mod_cast (hj.trans_lt h')


lemma cyclePath_interpolation {N m : ℕ} (hN : 0<N) (hm : m≤N)
    (a b : Fin (N+1) → ℝ)
    (hl : ∀ j (hj : j≤N-m), b ⟨j,by omega⟩ = a ⟨m+j,by omega⟩-a ⟨m,by omega⟩)
    (hr : ∀ j (hj : N-m≤j) (hjN : j≤N), b ⟨j,by omega⟩ =
      a ⟨N,by omega⟩+a ⟨j-(N-m),by omega⟩-a ⟨0,by omega⟩-a ⟨m,by omega⟩) :
    cyclePath (gridPoint N ⟨m,by omega⟩) (interpolation N a)=interpolation N b := by
  have hNR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hNne : (N:ℝ)≠0 := hNR.ne'
  have hgrid : (gridPoint N ⟨m,by omega⟩:ℝ)=(m:ℝ)/N := rfl
  have hmul : (N:ℝ)*((m:ℝ)/N)=m := mul_div_cancel₀ _ hNne
  have hz : (0:unitInterval)=gridPoint N ⟨0,by omega⟩ := by apply Subtype.ext; simp [gridPoint]
  have ho : (1:unitInterval)=gridPoint N ⟨N,by omega⟩ := by apply Subtype.ext; simp [gridPoint,hNne]
  apply ContinuousMap.ext
  intro t
  obtain ⟨j,hj,hjt,htj⟩ := exists_grid_interval hN t
  rw [interpolation_interval_formula hj b t hjt htj]
  by_cases hsum : m+j<N
  · have hjle : j≤N-m := by omega
    have hjle' : j+1≤N-m := by omega
    have hsumR : (m:ℝ)+(j:ℝ)+1≤N := by exact_mod_cast hsum
    have hct : (gridPoint N ⟨m,by omega⟩:ℝ)+(t:ℝ)≤1 := by
      rw [hgrid]
      nlinarith
    rw [cyclePath_apply_left _ _ _ hct,interpolation_gridPoint hN,
      interpolation_interval_formula hsum a _ (by dsimp; rw [hgrid,Nat.cast_add]; nlinarith)
        (by dsimp; rw [hgrid,Nat.cast_add]; nlinarith)]
    rw [hl j hjle,hl (j+1) hjle']
    simp only [Nat.cast_add]
    rw [hgrid]
    have hidx : (⟨m+j+1,by omega⟩ : Fin (N+1))=⟨m+(j+1),by omega⟩ := by congr 1
    simp only [hidx,mul_sub,mul_add,hmul]
    ring
  · have hjge : N-m≤j := by omega
    have hk : j-(N-m)<N := by omega
    have hdiff : (N-m:ℕ) + (j-(N-m))=j := Nat.add_sub_of_le hjge
    have hNm : ((N-m:ℕ):ℝ)=(N:ℝ)-m := Nat.cast_sub hm
    have hkR : ((j-(N-m):ℕ):ℝ)=(j:ℝ)-((N:ℝ)-m) := by rw [Nat.cast_sub hjge,hNm]
    have hct : 1≤(gridPoint N ⟨m,by omega⟩:ℝ)+(t:ℝ) := by
      rw [hgrid]
      have hsumR : (N:ℝ) ≤ m+j := by exact_mod_cast (le_of_not_gt hsum)
      nlinarith
    rw [cyclePath_apply_right _ _ _ hct,hz,ho,
      interpolation_gridPoint hN,interpolation_gridPoint hN,interpolation_gridPoint hN,
      interpolation_interval_formula hk a _ (by dsimp; rw [hgrid,hkR]; nlinarith)
        (by dsimp; rw [hgrid,hkR]; nlinarith)]
    rw [hr j hjge (by omega),hr (j+1) (by omega) (by omega)]
    simp only []
    rw [hgrid,hkR]
    have hidx : (⟨j-(N-m)+1,by omega⟩ : Fin (N+1))=⟨j+1-(N-m),by omega⟩ := by congr 1; omega
    simp only [hidx,mul_sub,mul_add,hmul,mul_one]
    ring


lemma minTime_interpolation {N : ℕ} (hN : 0 < N) (a : Fin (N+1) → ℝ)
    (m : Fin (N+1)) (hmin : ∀ i, a m ≤ a i) (hfirst : ∀ i, i < m → a m < a i) :
    minTime (interpolation N a)=gridPoint N m := by
  apply le_antisymm
  · apply minTime_first
    intro t
    rw [interpolation_gridPoint hN]
    exact interpolation_ge a hmin t
  · by_contra h
    have ht : minTime (interpolation N a)<gridPoint N m := lt_of_not_ge h
    have hs := interpolation_strict_before hN a m hmin hfirst _ ht
    have hu := minTime_spec (interpolation N a) (gridPoint N m)
    rw [interpolation_gridPoint hN] at hu
    exact (not_lt_of_ge hu) hs


@[simp] lemma cyclePath_one_time (f : C(unitInterval,ℝ)) : cyclePath 1 f=f-f 0 • 1 := by
  ext t
  rw [cyclePath_apply_right _ _ _ (by simp only [show ((1:unitInterval):ℝ)=1 from rfl]; linarith [t.property.1])]
  have he : (⟨(1:ℝ)+(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩ : unitInterval)=t := by
    ext; dsimp; ring
  simp only [show ((1:unitInterval):ℝ)=1 from rfl,he,ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,smul_eq_mul,mul_one]
  ring


lemma goodRotation_firstMinimum {N : ℕ} [NeZero N] (d : Bridge N) :
    FirstMinimum (degreeList d.val) (goodRotation d).val := by
  apply firstMinimum_of_isExcursionList_rotate ((degreeList_sum _).trans d.property)
    (by simp)
  rw [← degreeList_rotate,← isTreeCode_iff]
  exact goodRotation_spec d


def walkPolygon {N : ℕ} (σ : ℝ) (d : Fin N → Fin N) : C(unitInterval,ℝ) :=
  interpolation N (fun i => (walk d i.val:ℝ)/(σ*Real.sqrt N))


lemma walkPolygon_cycle {N : ℕ} [NeZero N] (σ : ℝ) (d : Bridge N) (m : Fin N) :
    cyclePath (gridPoint N ⟨m.val,by omega⟩) (walkPolygon σ d.val)=
      walkPolygon σ (rotateBridge m d).val := by
  have hN : 0 < N := NeZero.pos N
  apply cyclePath_interpolation hN m.isLt.le
  · intro j hj
    have he : walk (rotateBridge m d).val j = walk d.val (m.val+j)-walk d.val m.val := by
      change walk (rotateDegrees m d.val) j=_
      rw [← degreeList_prefixSum,degreeList_rotate,
        prefixSum_rotate_left _ (by simp) (by simpa using hj)]
      simp only [degreeList_prefixSum]
    dsimp
    rw [he,Int.cast_sub,sub_div]
  · intro j hj hjN
    have he : walk (rotateBridge m d).val j = walk d.val N-walk d.val m.val+
        walk d.val (j-(N-m.val)) := by
      change walk (rotateDegrees m d.val) j=_
      rw [← degreeList_prefixSum,degreeList_rotate,
        prefixSum_rotate_right _ (by simp) (by simpa using hj) (by simpa using hjN)]
      simp only [degreeList_prefixSum,degreeList_sum,degreeList_length]
    dsimp
    rw [he,Int.cast_add,Int.cast_sub,walk_zero,Int.cast_zero]
    ring


theorem vervaat_walkPolygon {N : ℕ} [NeZero N] {σ : ℝ} (hσ : 0 < σ) (d : Bridge N) :
    vervaat (walkPolygon σ d.val)=walkPolygon σ (canonicalCode d).val := by
  have hN : 0 < N := NeZero.pos N
  have hs : 0 < σ*Real.sqrt N := mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hm := goodRotation_firstMinimum d
  have hmin : ∀ j < N, walk d.val (goodRotation d).val ≤ walk d.val j := by
    simpa only [degreeList_prefixSum,degreeList_length] using hm.2.1
  have hfirst : ∀ j < (goodRotation d).val, walk d.val (goodRotation d).val < walk d.val j := by
    simpa only [degreeList_prefixSum] using hm.2.2
  have hnonpos : walk d.val (goodRotation d).val ≤ 0 := by simpa using hmin 0 hN
  by_cases hz : walk d.val (goodRotation d).val=0
  · have hg : IsTreeCode d.val := ⟨d.property,fun j hj => hz ▸ hmin j hj⟩
    have hc : (canonicalCode d).val=d.val := by
      change (rotateBridge (goodRotation d) d).val=d.val
      rw [goodRotation_of_code d hg,rotateBridge_zero]
    have ht : minTime (walkPolygon σ d.val)=1 := by
      rw [walkPolygon,minTime_interpolation hN _ (⟨N,by omega⟩ : Fin (N+1))]
      · apply Subtype.ext
        simp [gridPoint,(Nat.cast_pos.mpr hN : (0:ℝ)<N).ne']
      · intro i
        apply (div_le_div_iff_of_pos_right hs).mpr
        apply Int.cast_le.mpr
        by_cases hi : i.val=N
        · simp [hi]
        · rw [d.property]
          have hh := hg.2 i.val (by omega)
          omega
      · intro i hi
        apply (div_lt_div_iff_of_pos_right hs).mpr
        apply Int.cast_lt.mpr
        rw [d.property]
        have hh := hg.2 i.val hi
        omega
    rw [vervaat,ht,cyclePath_one_time,hc]
    have hzero : walkPolygon σ d.val 0=0 := by
      have he : (0:unitInterval)=gridPoint N ⟨0,by omega⟩ := by ext; simp [gridPoint]
      rw [walkPolygon,he,interpolation_gridPoint hN]
      simp
    rw [hzero,zero_smul,sub_zero]
  · have hneg : walk d.val (goodRotation d).val ≤ -1 := by omega
    have ht : minTime (walkPolygon σ d.val)=gridPoint N ⟨(goodRotation d).val,by omega⟩ := by
      apply minTime_interpolation hN
      · intro i
        apply (div_le_div_iff_of_pos_right hs).mpr
        apply Int.cast_le.mpr
        by_cases hi : i.val=N
        · simpa only [hi,d.property] using hneg
        · exact hmin i.val (by omega)
      · intro i hi
        apply (div_lt_div_iff_of_pos_right hs).mpr
        exact Int.cast_lt.mpr (hfirst i.val hi)
    rw [vervaat,ht,walkPolygon_cycle]
    rfl


lemma CriticalEvenOffspring.iidWalk_bridgeEmbedding (p : CriticalEvenOffspring)
    {N : ℕ} (d : Bridge N) : p.iidWalk N (bridgeEmbedding N d)=walkPolygon p.sigma d.val := by
  unfold iidWalk walkPolygon
  congr 1
  funext i
  have he : (∑ j : Fin N, if j.val < i.val then p.standardStep (bridgeEmbedding N d j) else 0)=
      (walk d.val i.val:ℝ)/p.sigma := by
    simp only [walk,Int.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · simp only [standardStep,Int.cast_sub,Int.cast_natCast,Int.cast_one]
      rfl
    · simp
  rw [he,div_div]


lemma CriticalEvenOffspring.vervaat_arrayTree (p : CriticalEvenOffspring) (n : ℕ) :
    (fun d => vervaat (p.iidWalk (2*n+1) d)) =ᵐ[p.iidBridgeLaw n]
      (fun d => walkPolygon p.sigma (arrayTree n d).val) := by
  have he : ∀ᵐ d ∂p.iidBridgeLaw n, totalStep d = -1 := by
    exact ae_cond_mem (by measurability)
  filter_upwards [he] with d hd
  let b := bridgeFromArray d hd
  have hb : bridgeEmbedding (2*n+1) b=d := bridgeFromArray_spec _ _
  rw [← hb,p.iidWalk_bridgeEmbedding,arrayTree_embedding,vervaat_walkPolygon p.sigma_pos]


theorem CriticalEvenOffspring.codeWalk_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (F : BoundedContinuousFunction C(unitInterval,ℝ) ℝ) :
    Tendsto (fun n : ℕ => ∑ d : Code (2*n+1),
      (codeWeight p d/codePartition p (2*n+1))*F (walkPolygon p.sigma d.val)) atTop
      (𝓝 (∫ ω,F (vervaat (bridgePath B ω)) ∂P)) := by
  have hc := p.iidVervaat_CLT hB
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc.tendsto F
  simp only [ProbabilityMeasure.coe_mk] at hh
  have hn (n : ℕ) :
      (∫ f,F f ∂(p.iidBridgeLaw n).map (fun d => vervaat (p.iidWalk (2*n+1) d)))=
        ∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1))*F (walkPolygon p.sigma d.val) := by
    rw [integral_map (hc.forall_aemeasurable n) F.continuous.aestronglyMeasurable]
    calc
      _ = ∫ d,F (walkPolygon p.sigma (arrayTree n d).val) ∂p.iidBridgeLaw n := by
        apply integral_congr_ae
        exact (p.vervaat_arrayTree n).fun_comp F
      _ = _ := p.arrayTree_expectation n (fun d => F (walkPolygon p.sigma d.val))
  have hz : (∫ f,F f ∂P.map (fun ω => vervaat (bridgePath B ω)))=
      ∫ ω,F (vervaat (bridgePath B ω)) ∂P :=
    integral_map hc.aemeasurable_limit F.continuous.aestronglyMeasurable
  simpa only [hn,hz] using hh


def firstZero {Ω : Type*} (S : ℕ → Ω → ℤ) (ω : Ω) : WithTop ℕ := by
  classical
  exact if h : ∃ n, S n ω=0 then WithTop.some (Nat.find h) else ⊤


lemma firstZero_le_iff {Ω : Type*} (S : ℕ → Ω → ℤ) (ω : Ω) (n : ℕ) :
    firstZero S ω ≤ WithTop.some n ↔ ∃ k  ≤  n, S k ω=0 := by
  classical
  unfold firstZero
  split_ifs with h
  · norm_cast
    exact Nat.find_le_iff h n
  · simp only [WithTop.top_le_iff,WithTop.coe_ne_top,false_iff,not_exists,not_and]
    intro k _ hk
    exact h ⟨k,hk⟩


lemma firstZero_isStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {S : ℕ → Ω → ℤ}
    (hS : StronglyAdapted ℱ S) : IsStoppingTime ℱ (firstZero S) := by
  intro n
  have he : {ω | firstZero S ω ≤ WithTop.some n}=⋃ k ≤ n,{ω | S k ω=0} := by
    ext ω
    change (firstZero S ω ≤ WithTop.some n) ↔ _
    rw [firstZero_le_iff]
    simp
  change MeasurableSet[ℱ n] {ω | firstZero S ω ≤ WithTop.some n}
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) fun k hk =>
    measurableSet_eq_fun ((hS k).measurable.mono (ℱ.mono hk) le_rfl) measurable_const


lemma integer_path_nonneg_before_zero (S : ℕ → ℤ) (h₀ : 0 ≤ S 0)
    (hstep : ∀ n, S n-1 ≤ S (n+1)) (n : ℕ) (hn : ∀ k < n, S k≠0) : 0 ≤ S n := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    have hpos : 0 < S n := lt_of_le_of_ne (ih (fun k hk => hn k (by omega))) (Ne.symm (hn n (by omega)))
    have := hstep n
    omega


lemma stopped_firstZero_nonneg {Ω : Type*} (S : ℕ → Ω → ℤ) (ω : Ω)
    (h₀ : 0 ≤ S 0 ω) (hstep : ∀ n, S n ω-1 ≤ S (n+1) ω) (n : ℕ) :
    0 ≤ stoppedProcess (fun k ω => (S k ω:ℝ)) (firstZero S) n ω := by
  classical
  by_cases h : ∃ k, S k ω=0
  · by_cases hn : Nat.find h  ≤  n
    · rw [stoppedProcess,firstZero,dite_eq_left h,min_eq_right (WithTop.coe_le_coe.mpr hn)]
      simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,Nat.find_spec h,Int.cast_zero,le_refl]
    · rw [stoppedProcess,firstZero,dite_eq_left h,min_eq_left (WithTop.coe_le_coe.mpr (by omega : n ≤ Nat.find h))]
      simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      exact_mod_cast integer_path_nonneg_before_zero (fun k => S k ω) h₀ hstep n
        (fun k hk => Nat.find_min h (by omega))
  · rw [stoppedProcess,firstZero,dite_eq_right h,min_top_right,WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    exact_mod_cast integer_path_nonneg_before_zero (fun k => S k ω) h₀ hstep n
      (fun k _ hk => h ⟨k,hk⟩)


lemma martingale_stoppedProcess_real {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hf : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ) :
    Martingale (stoppedProcess f τ) ℱ μ := by
  apply martingale_iff.mpr
  constructor
  · have hh := (hf.neg.submartingale.stoppedProcess hτ).neg
    simpa using hh
  · exact hf.submartingale.stoppedProcess hτ


theorem integer_martingale_hits_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℤ} (hS : StronglyAdapted ℱ S)
    (hM : Martingale (fun n ω => (S n ω:ℝ)) ℱ μ)
    (h₀ : ∀ ω, 0 ≤ S 0 ω) (hstep : ∀ n ω, S n ω-1 ≤ S (n+1) ω)
    (hjump : ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, S (n+1) ω ≠ S n ω) :
    ∀ᵐ ω ∂μ, ∃ n, S n ω=0 := by
  let f := stoppedProcess (fun n ω => (S n ω:ℝ)) (firstZero S)
  have hm : Martingale f ℱ μ := martingale_stoppedProcess_real hM (firstZero_isStoppingTime hS)
  have hpos (n : ℕ) (ω : Ω) : 0 ≤ f n ω := stopped_firstZero_nonneg S ω (h₀ ω) (fun k => hstep k ω) n
  have he (n : ℕ) : ∫ ω,f n ω ∂μ=∫ ω,f 0 ω ∂μ := by
    simpa using (hm.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ).symm
  have hb (n : ℕ) : eLpNorm (f n) 1 μ ≤ ENNReal.ofReal (∫ ω,f 0 ω ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hm.integrable n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hm.integrable n)]
    have hn : (fun ω => ‖f n ω‖)=f n := funext fun ω => Real.norm_of_nonneg (hpos n ω)
    rw [hn,he]
  have hc := hm.submartingale.exists_ae_tendsto_of_bdd hb
  filter_upwards [hc,hjump] with ω hω hj
  obtain ⟨c,hc⟩ := hω
  by_contra hn
  have hz : firstZero S ω=⊤ := by simp [firstZero,hn]
  have hf : (fun n => f n ω)=fun n => (S n ω:ℝ) := by
    funext n
    dsimp [f,stoppedProcess]
    rw [hz,min_top_right,← WithTop.coe_natCast, Nat.cast_id,
      WithTop.untopA_eq_untop WithTop.coe_ne_top]
    rfl
  rw [hf] at hc
  have hd : Tendsto (fun n => (S (n+1) ω:ℝ)-(S n ω:ℝ)) atTop (𝓝 0) := by
    simpa using (hc.comp (tendsto_add_atTop_nat 1)).sub hc
  have hs := hd.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ)<1))
  obtain ⟨n,hn,hneq⟩ := ((hj.and_eventually hs)).exists
  apply hn
  apply Int.cast_injective (α := ℝ)
  have habs : |(S (n+1) ω:ℝ)-(S n ω:ℝ)|<1 := by simpa [Metric.mem_ball,Real.dist_eq] using hneq
  have hi : |S (n+1) ω-S n ω|<1 := by exact_mod_cast habs
  have hi' := abs_lt.mp hi
  omega


def integerSum (x : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, ((x k : ℤ)-1)


@[simp] lemma integerSum_zero (x : ℕ → ℕ) : integerSum x 0=0 := by simp [integerSum]


@[simp] lemma integerSum_succ (x : ℕ → ℕ) (n : ℕ) :
    integerSum x (n+1)=integerSum x n+(x n:ℤ)-1 := by
  simp only [integerSum,Finset.sum_range_succ]
  ring


theorem CriticalEvenOffspring.stream_hits_negative (p : CriticalEvenOffspring)
    (j : ℕ) (hj : 0 < j) :
    ∀ᵐ ω ∂p.streamLaw, ∃ n, integerSum ω n=-(j:ℤ) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun n ω => (ω n:ℝ)-1
  have hm (n : ℕ) : StronglyMeasurable (X n) := by fun_prop
  let ℱ := Filtration.natural X hm
  let S : ℕ → (ℕ → ℕ) → ℤ := fun n ω => (j:ℤ)+integerSum ω (n+1)
  have hM : Martingale (fun n ω => (S n ω:ℝ)) ℱ p.streamLaw := by
    have h := independent_sum_martingale X hm
      (fun n => (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).integrable_comp_of_integrable p.integrable_step)
      (iIndepFun_infinitePi (X := fun _ (k : ℕ) => (k:ℝ)-1) (fun _ => by fun_prop)) (fun n => by
        change (∫ ω, ((fun k : ℕ => (k:ℝ)-1) (ω n)) ∂p.streamLaw)=0
        exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).hasLaw.integral_comp
          (f := fun k : ℕ => (k:ℝ)-1) (by fun_prop)).trans p.integral_step)
    convert (martingale_const ℱ p.streamLaw (j:ℝ)).add h using 1
    ext n ω
    simp [S,integerSum,X]
  have hS : StronglyAdapted ℱ S := by
    intro n
    have h : Measurable[ℱ n] (fun ω => Int.floor (S n ω:ℝ)) :=
      Int.measurable_floor.comp (hM.stronglyMeasurable n).measurable
    simpa only [Int.floor_intCast] using h.stronglyMeasurable
  have h₀ (ω : ℕ → ℕ) : 0 ≤ S 0 ω := by
    dsimp [S]
    simp only [integerSum_succ,integerSum_zero,zero_add]
    omega
  have hstep (n : ℕ) (ω : ℕ → ℕ) : S n ω-1 ≤ S (n+1) ω := by
    dsimp [S]
    rw [integerSum_succ ω (n+1)]
    omega
  have hone : ∀ᵐ k ∂p.law.toMeasure, k≠1 := by
    rw [ae_iff]
    simpa using (show p.law.toMeasure {1}=0 by
      simp [p.even_support 1 (by decide)])
  have hall : ∀ᵐ ω ∂p.streamLaw, ∀ n, ω n≠1 := by
    rw [ae_all_iff]
    intro n
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).quasiMeasurePreserving.tendsto_ae hone
  have hjump : ∀ᵐ ω ∂p.streamLaw, ∃ᶠ n in atTop, S (n+1) ω≠S n ω := by
    filter_upwards [hall] with ω hω
    apply Filter.Frequently.of_forall
    intro n hn
    have h := hω (n+1)
    dsimp [S] at hn
    rw [integerSum_succ ω (n+1)] at hn
    omega
  filter_upwards [integer_martingale_hits_zero hS hM h₀ hstep hjump] with ω hω
  obtain ⟨n,hn⟩ := hω
  exact ⟨n+1,by dsimp [S] at hn; omega⟩


def reverseIndex (n k : ℕ) : ℕ := if k < n then n-1-k else k


def reverseFirst (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => x (reverseIndex n k)


lemma reverseIndex_involutive (n : ℕ) : Function.Involutive (reverseIndex n) := by
  intro k
  by_cases hk : k < n
  · have hnk : n-1-k < n := by omega
    simp only [reverseIndex,ite_eq_left hk,ite_eq_left hnk]
    omega
  · simp only [reverseIndex,ite_eq_right hk]


lemma reverseFirst_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseFirst n) p.streamLaw p.streamLaw := by
  refine ⟨by unfold reverseFirst; fun_prop,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (reverseIndex_involutive n).injective


lemma integerSum_reverseFirst (x : ℕ → ℕ) (n k : ℕ) (hk : k ≤ n) :
    integerSum (reverseFirst n x) k=integerSum x n-integerSum x (n-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := by omega
    have he : n-k=(n-(k+1))+1 := by omega
    have he' : n-1-k=n-(k+1) := by omega
    rw [integerSum_succ,ih (by omega)]
    simp only [reverseFirst,reverseIndex,ite_eq_left hk',he']
    rw [he,integerSum_succ]
    ring


def negativeSurvival (x : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, 0 < k → k ≤ n → integerSum x k < 0


def firstHitBelow (x : ℕ → ℕ) (j n : ℕ) : Prop :=
  integerSum x n=-(j:ℤ) ∧ ∀ k, k < n → -(j:ℤ) < integerSum x k


lemma firstHitBelow_iff_reverse_survival (x : ℕ → ℕ) (j n : ℕ) :
    firstHitBelow x j n ↔ integerSum (reverseFirst n x) n=-(j:ℤ) ∧
      negativeSurvival (reverseFirst n x) n := by
  have he : integerSum (reverseFirst n x) n=integerSum x n := by
    simp [integerSum_reverseFirst x n n le_rfl]
  rw [he]
  constructor
  · rintro ⟨hx,hfirst⟩
    refine ⟨hx,?_⟩
    intro k hk hkn
    rw [integerSum_reverseFirst x n k hkn,hx]
    have h := hfirst (n-k) (by omega)
    omega
  · rintro ⟨hx,hs⟩
    refine ⟨hx,?_⟩
    intro k hkn
    have h := hs (n-k) (by omega) (by omega)
    rw [integerSum_reverseFirst x n (n-k) (by omega)] at h
    have he' : n-(n-k)=k := by omega
    rw [he',hx] at h
    omega


lemma measurable_integerSum (n : ℕ) : Measurable (fun x : ℕ → ℕ => integerSum x n) := by
  unfold integerSum
  fun_prop


lemma measurableSet_firstHitBelow (j n : ℕ) : MeasurableSet {x | firstHitBelow x j n} := by
  unfold firstHitBelow
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integerSum n) measurable_const).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_integerSum k))


lemma measurableSet_survival_endpoint (j n : ℕ) :
    MeasurableSet {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} := by
  unfold negativeSurvival
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integerSum n) measurable_const).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_integerSum k) measurable_const)


lemma CriticalEvenOffspring.survival_endpoint_eq_firstHit (p : CriticalEvenOffspring)
    (j n : ℕ) :
    p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n}=
      p.streamLaw {x | firstHitBelow x j n} := by
  rw [← (reverseFirst_preserving p n).measure_preimage (measurableSet_survival_endpoint j n).nullMeasurableSet]
  congr 1
  ext x
  exact (firstHitBelow_iff_reverse_survival x j n).symm


lemma exists_firstHitBelow (x : ℕ → ℕ) (j : ℕ) (_hj : 0 < j)
    (hex : ∃ n, integerSum x n=-(j:ℤ)) : ∃ n, firstHitBelow x j n := by
  classical
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  intro k hk
  have h0 : 0 ≤ (j:ℤ)+integerSum x 0 := by simp
  have hs (r : ℕ) : (j:ℤ)+integerSum x r-1 ≤ (j:ℤ)+integerSum x (r+1) := by
    rw [integerSum_succ]
    omega
  have hn (r : ℕ) (hr : r ≤ k) : (j:ℤ)+integerSum x r≠0 := by
    have h := Nat.find_min hex (by omega : r < Nat.find hex)
    omega
  have hpos := integer_path_nonneg_before_zero (fun r => (j:ℤ)+integerSum x r)
    h0 hs k (fun r hr => hn r hr.le)
  have hne := hn k le_rfl
  omega


lemma firstHitBelow_disjoint (j : ℕ) :
    Pairwise (fun n m => Disjoint {x | firstHitBelow x j n} {x | firstHitBelow x j m}) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hh := hm.2 n h
    rw [hn.1] at hh
    exact (lt_irrefl _ hh)
  · have hh := hn.2 m h
    rw [hm.1] at hh
    exact (lt_irrefl _ hh)


theorem CriticalEvenOffspring.negative_potential_one (p : CriticalEvenOffspring)
    (j : ℕ) (hj : 0 < j) :
    (∑' n, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n})=1 := by
  simp_rw [p.survival_endpoint_eq_firstHit]
  rw [← measure_iUnion (firstHitBelow_disjoint j) (measurableSet_firstHitBelow j)]
  apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (measurableSet_firstHitBelow j))).mp
  filter_upwards [p.stream_hits_negative j hj] with x hx
  obtain ⟨n,hn⟩ := exists_firstHitBelow x j hj hx
  exact Set.mem_iUnion.mpr ⟨n,hn⟩


def truncateStream (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => if k<n then x k else 0


lemma measurable_truncateStream (n : ℕ) : Measurable (truncateStream n) := by
  apply Measurable.of_eval
  intro k
  unfold truncateStream
  split_ifs <;> fun_prop


lemma integerSum_truncateStream (x : ℕ → ℕ) {k n : ℕ} (hkn : k ≤ n) :
    integerSum (truncateStream n x) k=integerSum x k := by
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  simp [truncateStream,show i<n from lt_of_lt_of_le (Finset.mem_range.mp hi) hkn]


lemma CriticalEvenOffspring.truncate_indep_next (p : CriticalEvenOffspring) (n : ℕ) :
    IndepFun (truncateStream n) (fun x : ℕ → ℕ => x n) p.streamLaw := by
  classical
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) {n} := by simp
  have h := hi.indepFun_finset (Finset.range n) {n} hd (fun k => measurable_pi_apply k)
  let f : ((Finset.range n) → ℕ) → (ℕ → ℕ) :=
    fun x k => if hk : k<n then x ⟨k,Finset.mem_range.mpr hk⟩ else 0
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    dsimp [f]
    split_ifs <;> fun_prop
  have hh := h.comp hf (measurable_pi_apply ⟨n,by simp⟩)
  exact hh


lemma CriticalEvenOffspring.prefix_inter_next (p : CriticalEvenOffspring)
    (n r : ℕ) (E : Set (ℕ → ℕ)) (hE : MeasurableSet E)
    (htr : (truncateStream n) ⁻¹' E=E) :
    p.streamLaw (E ∩ {x | x n=r})=p.streamLaw E*p.law r := by
  have h := (p.truncate_indep_next n).measure_inter_preimage_eq_mul E {r} hE
    (measurableSet_singleton _)
  rw [htr] at h
  have he := (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).measure_preimage
    (measurableSet_singleton r).nullMeasurableSet
  change p.streamLaw ((fun x => x n) ⁻¹' {r})=p.law.toMeasure {r} at he
  rw [he] at h
  simpa only [Set.preimage,Set.mem_singleton_iff,p.law_singleton,p.law_apply] using h


lemma survival_endpoint_truncate (j n : ℕ) :
    (truncateStream n) ⁻¹' {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n}=
    {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} := by
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [negativeSurvival,integerSum_truncateStream x le_rfl]
  constructor <;> rintro ⟨he,hs⟩ <;> refine ⟨he,?_⟩
  · intro k hk hkn
    simpa only [integerSum_truncateStream x hkn] using hs k hk hkn
  · intro k hk hkn
    simpa only [integerSum_truncateStream x hkn] using hs k hk hkn


lemma CriticalEvenOffspring.negative_potential_zero (p : CriticalEvenOffspring) :
    (∑' n, p.streamLaw {x | integerSum x n=0 ∧ negativeSurvival x n})=1 := by
  rw [tsum_eq_single 0]
  · have he : {x | integerSum x 0=0 ∧ negativeSurvival x 0}=(Set.univ : Set (ℕ → ℕ)) := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true,integerSum_zero,true_and]
      intro k hk hkn
      omega
    rw [he,measure_univ]
  · intro n hn
    have he : {x | integerSum x n=0 ∧ negativeSurvival x n}=(∅ : Set (ℕ → ℕ)) := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro hx hs
      have h := hs n (Nat.pos_of_ne_zero hn) le_rfl
      omega
    rw [he,measure_empty]


lemma CriticalEvenOffspring.negative_potential (p : CriticalEvenOffspring) (j : ℕ) :
    (∑' n, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n})=1 := by
  cases j with
  | zero => simpa using p.negative_potential_zero
  | succ j => exact p.negative_potential_one _ (by omega)

end FKCRT.TreeCoding
end

end OAI
