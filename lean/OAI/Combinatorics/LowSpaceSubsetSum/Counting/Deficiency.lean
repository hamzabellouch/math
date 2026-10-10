import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Model
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-!
# Finite distinct-subset-sum estimates

These are the cardinality statements underlying the deficiency lemma in §2
of *A Low-Space Algorithm for Worst-Case Subset Sum*. The indexed formulation
retains repeated input values. Arbitrary signed integer weights are allowed.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct integer values of subset sums on the index domain `V`. -/
def distinctSums (a : ι → ℤ) (V : Finset ι) : Finset ℤ :=
  V.powerset.image (weight a)

/-- The count `N(V)` used in the paper's deficiency. -/
def distinctSumCount (a : ι → ℤ) (V : Finset ι) : ℕ :=
  (distinctSums a V).card

theorem mem_distinctSums (a : ι → ℤ) (V : Finset ι) (x : ℤ) :
    x ∈ distinctSums a V ↔ ∃ S ⊆ V, weight a S = x := by
  simp only [distinctSums, Finset.mem_image, Finset.mem_powerset]

@[simp] theorem zero_mem_distinctSums (a : ι → ℤ) (V : Finset ι) :
    0 ∈ distinctSums a V := by
  exact (mem_distinctSums a V 0).mpr ⟨∅, Finset.empty_subset _, weight_empty a⟩

theorem one_le_distinctSumCount (a : ι → ℤ) (V : Finset ι) :
    1 ≤ distinctSumCount a V := by
  exact Finset.card_pos.mpr ⟨0, zero_mem_distinctSums a V⟩

theorem distinctSumCount_le_pow (a : ι → ℤ) (V : Finset ι) :
    distinctSumCount a V ≤ 2 ^ V.card := by
  exact (Finset.card_image_le).trans (Finset.card_powerset V).le

@[simp] theorem distinctSums_empty (a : ι → ℤ) : distinctSums a ∅ = {0} := by
  simp [distinctSums]

@[simp] theorem distinctSumCount_empty (a : ι → ℤ) : distinctSumCount a ∅ = 1 := by
  simp [distinctSumCount]

theorem distinctSums_mono (a : ι → ℤ) {V W : Finset ι} (h : V ⊆ W) :
    distinctSums a V ⊆ distinctSums a W := by
  exact Finset.image_subset_image (Finset.powerset_mono.mpr h)

theorem distinctSumCount_mono (a : ι → ℤ) {V W : Finset ι} (h : V ⊆ W) :
    distinctSumCount a V ≤ distinctSumCount a W :=
  Finset.card_le_card (distinctSums_mono a h)

@[simp] theorem weight_singleton (a : ι → ℤ) (i : ι) : weight a {i} = a i := by
  simp [weight]

theorem weight_insert_of_not_mem (a : ι → ℤ) {i : ι} {S : Finset ι} (hi : i ∉ S) :
    weight a (insert i S) = a i + weight a S := by
  have hd : Disjoint ({i} : Finset ι) S := by simpa
  simpa using weight_union a hd

/-- Every sum after adding one index is either an old sum or its translate. -/
theorem distinctSums_insert_subset (a : ι → ℤ) (V : Finset ι) (i : ι) :
    distinctSums a (insert i V) ⊆
      distinctSums a V ∪ (distinctSums a V).image (fun x => a i + x) := by
  intro x hx
  obtain ⟨S, hS, rfl⟩ := (mem_distinctSums a (insert i V) x).mp hx
  by_cases hi : i ∈ S
  · apply Finset.mem_union.mpr
    right
    refine Finset.mem_image.mpr ⟨weight a (S.erase i), ?_, ?_⟩
    · apply (mem_distinctSums a V _).mpr
      refine ⟨S.erase i, ?_, rfl⟩
      intro j hj
      have hjS := Finset.mem_erase.mp hj
      have hjV := hS hjS.2
      simp only [Finset.mem_insert] at hjV
      exact hjV.resolve_left hjS.1
    · have hw := weight_insert_of_not_mem a (Finset.notMem_erase i S)
      simpa [Finset.insert_erase hi] using hw.symm
  · apply Finset.mem_union.mpr
    left
    apply (mem_distinctSums a V _).mpr
    refine ⟨S, ?_, rfl⟩
    intro j hj
    have hjV := hS hj
    simp only [Finset.mem_insert] at hjV
    rcases hjV with rfl | hjV
    · exact (hi hj).elim
    · exact hjV

theorem distinctSumCount_insert_le (a : ι → ℤ) (V : Finset ι) (i : ι) :
    distinctSumCount a (insert i V) ≤ 2 * distinctSumCount a V := by
  calc
    _ ≤ (distinctSums a V ∪ (distinctSums a V).image (fun x => a i + x)).card :=
      Finset.card_le_card (distinctSums_insert_subset a V i)
    _ ≤ (distinctSums a V).card + ((distinctSums a V).image (fun x => a i + x)).card :=
      Finset.card_union_le _ _
    _ ≤ (distinctSums a V).card + (distinctSums a V).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * distinctSumCount a V := by simp [distinctSumCount, two_mul]

theorem distinctSumCount_le_insert (a : ι → ℤ) (V : Finset ι) (i : ι) :
    distinctSumCount a V ≤ distinctSumCount a (insert i V) :=
  distinctSumCount_mono a (Finset.subset_insert i V)

/-- Every sum on a union is a sum of a value from each domain. The domains
need not be disjoint: split a witness using intersection and set difference. -/
theorem distinctSums_union_subset (a : ι → ℤ) (V W : Finset ι) :
    distinctSums a (V ∪ W) ⊆
      ((distinctSums a V) ×ˢ (distinctSums a W)).image (fun p => p.1 + p.2) := by
  intro x hx
  obtain ⟨S, hS, rfl⟩ := (mem_distinctSums a (V ∪ W) x).mp hx
  refine Finset.mem_image.mpr ⟨(weight a (S ∩ V), weight a (S \ V)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · exact (mem_distinctSums a V _).mpr ⟨S ∩ V, Finset.inter_subset_right, rfl⟩
    · apply (mem_distinctSums a W _).mpr
      refine ⟨S \ V, ?_, rfl⟩
      intro i hi
      have hiS := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hS hiS.1)).resolve_left hiS.2
  · have hd : Disjoint (S ∩ V) (S \ V) := by
      apply Finset.disjoint_left.mpr
      intro i hi₁ hi₂
      exact (Finset.mem_sdiff.mp hi₂).2 (Finset.mem_inter.mp hi₁).2
    have hunion : (S ∩ V) ∪ (S \ V) = S := by
      ext i
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    simpa only [hunion] using (weight_union a hd).symm

/-- The multiplicative count bound behind superadditivity of deficiency. -/
theorem distinctSumCount_union_le (a : ι → ℤ) (V W : Finset ι) :
    distinctSumCount a (V ∪ W) ≤ distinctSumCount a V * distinctSumCount a W := by
  calc
    _ ≤ (((distinctSums a V) ×ˢ (distinctSums a W)).image
        (fun p => p.1 + p.2)).card :=
      Finset.card_le_card (distinctSums_union_subset a V W)
    _ ≤ ((distinctSums a V) ×ˢ (distinctSums a W)).card := Finset.card_image_le
    _ = _ := Finset.card_product _ _

omit [Fintype ι] in
theorem symmDiff_subset_domain {S F V : Finset ι} (hS : S ⊆ V) (hF : F ⊆ V) :
    S ∆ F ⊆ V :=
  (Finset.symmDiff_subset_union).trans (Finset.union_subset hS hF)

/-- Negating selected indices translates the set of distinct sum values. -/
theorem distinctSums_flip_of_subset (a : ι → ℤ) {F V : Finset ι} (hF : F ⊆ V) :
    distinctSums (flip a F) V = (distinctSums a V).image (fun x => x - weight a F) := by
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, rfl⟩ := (mem_distinctSums (flip a F) V x).mp hx
    refine Finset.mem_image.mpr ⟨weight a (S ∆ F), ?_, ?_⟩
    · exact (mem_distinctSums a V _).mpr
        ⟨S ∆ F, symmDiff_subset_domain hS hF, rfl⟩
    · exact (weight_flip a F S).symm
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨S, hS, rfl⟩ := (mem_distinctSums a V y).mp hy
    apply (mem_distinctSums (flip a F) V _).mpr
    refine ⟨S ∆ F, symmDiff_subset_domain hS hF, ?_⟩
    simp only [weight_flip, symmDiff_assoc, symmDiff_self, symmDiff_bot]

theorem distinctSumCount_flip_of_subset (a : ι → ℤ) {F V : Finset ι} (hF : F ⊆ V) :
    distinctSumCount (flip a F) V = distinctSumCount a V := by
  rw [distinctSumCount, distinctSums_flip_of_subset a hF]
  apply Finset.card_image_of_injective
  intro x y hxy
  simpa only [sub_left_inj] using hxy

/-- Signs outside the current domain do not affect its subset sums. -/
theorem weight_flip_inter (a : ι → ℤ) (F V : Finset ι) {S : Finset ι} (hS : S ⊆ V) :
    weight (flip a F) S = weight (flip a (F ∩ V)) S := by
  simp only [weight]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi, flip, hS hi]
  · simp [hi]

/-- Distinct-sum counts are invariant under arbitrary individual sign changes. -/
theorem distinctSumCount_flip (a : ι → ℤ) (F V : Finset ι) :
    distinctSumCount (flip a F) V = distinctSumCount a V := by
  have hsums : distinctSums (flip a F) V = distinctSums (flip a (F ∩ V)) V := by
    ext x
    simp only [mem_distinctSums]
    constructor
    · rintro ⟨S, hS, hx⟩
      exact ⟨S, hS, (weight_flip_inter a F V hS).symm.trans hx⟩
    · rintro ⟨S, hS, hx⟩
      exact ⟨S, hS, (weight_flip_inter a F V hS).trans hx⟩
  change (distinctSums (flip a F) V).card = distinctSumCount a V
  rw [hsums]
  exact distinctSumCount_flip_of_subset a Finset.inter_subset_right

/-- The paper's deficiency, with logarithms in base two. -/
noncomputable def deficiency (a : ι → ℤ) (V : Finset ι) : ℝ :=
  V.card - Real.logb 2 (distinctSumCount a V)

theorem distinctSumCount_pos_real (a : ι → ℤ) (V : Finset ι) :
    0 < (distinctSumCount a V : ℝ) := by
  exact_mod_cast (one_le_distinctSumCount a V)

theorem deficiency_nonneg (a : ι → ℤ) (V : Finset ι) : 0 ≤ deficiency a V := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (distinctSumCount_pos_real a V)
    (show (distinctSumCount a V : ℝ) ≤ (2 : ℝ) ^ V.card by
      exact_mod_cast distinctSumCount_le_pow a V)
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hlog
  exact sub_nonneg.mpr hlog

theorem deficiency_le_card (a : ι → ℤ) (V : Finset ι) : deficiency a V ≤ V.card := by
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    (show (1 : ℝ) ≤ distinctSumCount a V by exact_mod_cast one_le_distinctSumCount a V)
  exact sub_le_self _ hlog

@[simp] theorem deficiency_empty (a : ι → ℤ) : deficiency a ∅ = 0 := by
  simp [deficiency]

/-- Sign changes preserve deficiency even when the domain is a proper subset
of all indices whose signs are changed. -/
theorem deficiency_flip (a : ι → ℤ) (F V : Finset ι) :
    deficiency (flip a F) V = deficiency a V := by
  simp only [deficiency, distinctSumCount_flip]

/-- Deficiency is superadditive on disjoint domains. -/
theorem deficiency_superadditive (a : ι → ℤ) {V W : Finset ι} (hd : Disjoint V W) :
    deficiency a V + deficiency a W ≤ deficiency a (V ∪ W) := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (distinctSumCount_pos_real a (V ∪ W))
    (show (distinctSumCount a (V ∪ W) : ℝ) ≤
        (distinctSumCount a V : ℝ) * (distinctSumCount a W : ℝ) by
      exact_mod_cast distinctSumCount_union_le a V W)
  rw [Real.logb_mul (distinctSumCount_pos_real a V).ne'
    (distinctSumCount_pos_real a W).ne'] at hlog
  simp only [deficiency, Finset.card_union_of_disjoint hd, Nat.cast_add]
  linarith

/-- Inclusion monotonicity follows by splitting off the new indices. -/
theorem deficiency_mono (a : ι → ℤ) {V W : Finset ι} (hVW : V ⊆ W) :
    deficiency a V ≤ deficiency a W := by
  have hd : Disjoint V (W \ V) := by
    apply Finset.disjoint_left.mpr
    intro i hiV hiD
    exact (Finset.mem_sdiff.mp hiD).2 hiV
  have hsuper := deficiency_superadditive a hd
  rw [Finset.union_sdiff_of_subset hVW] at hsuper
  linarith [deficiency_nonneg a (W \ V)]

/-- Adding a fresh index increases deficiency by at most one. -/
theorem deficiency_insert_le (a : ι → ℤ) {V : Finset ι} {i : ι} (hi : i ∉ V) :
    deficiency a (insert i V) ≤ deficiency a V + 1 := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (distinctSumCount_pos_real a V)
    (show (distinctSumCount a V : ℝ) ≤ distinctSumCount a (insert i V) by
      exact_mod_cast distinctSumCount_le_insert a V i)
  simp only [deficiency, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
  linarith

theorem deficiency_insert_bounds (a : ι → ℤ) {V : Finset ι} {i : ι} (hi : i ∉ V) :
    deficiency a V ≤ deficiency a (insert i V) ∧
      deficiency a (insert i V) ≤ deficiency a V + 1 :=
  ⟨deficiency_mono a (Finset.subset_insert i V), deficiency_insert_le a hi⟩

/-- Replacing one index of a domain by another changes deficiency by at
most one, the bounded-difference fact used in the variance estimate. -/
theorem deficiency_replacement_lipschitz (a : ι → ℤ) {V : Finset ι} {i j : ι}
    (hi : i ∉ V) (hj : j ∉ V) :
    |deficiency a (insert i V) - deficiency a (insert j V)| ≤ 1 := by
  obtain ⟨hi₀, hi₁⟩ := deficiency_insert_bounds a hi
  obtain ⟨hj₀, hj₁⟩ := deficiency_insert_bounds a hj
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end LowSpaceSubsetSum

end OAI
