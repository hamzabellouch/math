import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionConcentration
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FixedBuckets
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteKernels
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResidues

namespace OAI

/-!
# The compressed-block trial's actual solution bucket

The seven compacted blocks and three raw domains are consecutive intervals
of one uniform permutation. The only subsequent random draw is a prime.
The residue of the fixed solution is enumerated by the program, not sampled.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def compressionHalfSize (n : ℕ) : ℕ := mixerSize n / 2
def compressionRightRawSize (n : ℕ) : ℕ := n / 20
def compressionLeftRawSize (n : ℕ) : ℕ := n - 7 * compressionHalfSize n - compressionRightRawSize n
def compressionPrimeExponent (n : ℕ) : ℕ := 249 * n / 1000
def compressionDictionaryCapacity (n : ℕ) : ℕ := 2 ^ (199 * n / 1000)

def indexInterval (n start len : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => start ≤ i.val ∧ i.val < start + len)

theorem indexInterval_card {n start len : ℕ} (h : start + len ≤ n) :
    (indexInterval n start len).card = len := by
  let e : ↥(indexInterval n start len) ≃ Fin len :=
    { toFun := fun x => ⟨x.val.val - start, by
        have hx := (Finset.mem_filter.mp x.property).2
        omega⟩
      invFun := fun x => ⟨⟨start + x.val, by omega⟩, by
        simp only [indexInterval, Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Fin.ext
        have hx := (Finset.mem_filter.mp x.property).2
        dsimp
        omega
      right_inv := by intro x; apply Fin.ext; dsimp; omega }
  exact (Fintype.card_coe _).symm.trans ((Fintype.card_congr e).trans (Fintype.card_fin _))

def compressionBlock (n : ℕ) (i : Fin 7) : Finset (Fin n) :=
  indexInterval n (i.val * compressionHalfSize n) (compressionHalfSize n)

def compressionLeftRaw (n : ℕ) : Finset (Fin n) :=
  indexInterval n (7 * compressionHalfSize n) (compressionLeftRawSize n)

def compressionRightRaw (n : ℕ) (i : Fin 2) : Finset (Fin n) :=
  if i = 0 then
    indexInterval n (n - compressionRightRawSize n) (compressionRightRawSize n / 2)
  else indexInterval n (n - compressionRightRawSize n + compressionRightRawSize n / 2)
    (compressionRightRawSize n - compressionRightRawSize n / 2)

theorem compressionHalfSize_eq (n : ℕ) : compressionHalfSize n = 4 * (3 * n / 100) := by
  simp only [compressionHalfSize, mixerSize]
  omega

theorem compression_layout_feasible (n : ℕ) :
    7 * compressionHalfSize n + compressionRightRawSize n ≤ n := by
  rw [compressionHalfSize_eq]
  dsimp only [compressionRightRawSize]
  omega

theorem compressionBlock_card (n : ℕ) (i : Fin 7) :
    (compressionBlock n i).card = compressionHalfSize n := by
  apply indexInterval_card
  have hi := i.isLt
  have hf := compression_layout_feasible n
  nlinarith

theorem compressionLeftRaw_card (n : ℕ) :
    (compressionLeftRaw n).card = compressionLeftRawSize n := by
  apply indexInterval_card
  unfold compressionLeftRawSize
  have h := compression_layout_feasible n
  omega

theorem compressionBlock_disjoint (n : ℕ) {i j : Fin 7} (hij : i ≠ j) :
    Disjoint (compressionBlock n i) (compressionBlock n j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxi := (Finset.mem_filter.mp hx).2
  have hxj := (Finset.mem_filter.mp hy).2
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_right (compressionHalfSize n)
      (show i.val + 1 ≤ j.val by omega)
    simp only [Nat.add_mul, one_mul] at hm
    omega
  · have hm := Nat.mul_le_mul_right (compressionHalfSize n)
      (show j.val + 1 ≤ i.val by omega)
    simp only [Nat.add_mul, one_mul] at hm
    omega

theorem compressionBlock_leftRaw_disjoint (n : ℕ) (i : Fin 7) :
    Disjoint (compressionBlock n i) (compressionLeftRaw n) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxi := (Finset.mem_filter.mp hx).2
  have hxy := (Finset.mem_filter.mp hy).2
  have hi := i.isLt
  have hm := Nat.mul_le_mul_right (compressionHalfSize n)
    (show i.val + 1 ≤ 7 by omega)
  simp only [Nat.add_mul, one_mul] at hm
  omega

def compressionBaseLeft (n : ℕ) : Finset (Fin n) :=
  ((compressionBlock n 4 ∪ compressionBlock n 5) ∪ compressionBlock n 6) ∪ compressionLeftRaw n

def compressionBaseRight (n : ℕ) : Finset (Fin n) :=
  ((compressionBlock n 0 ∪ compressionBlock n 1) ∪ compressionRightRaw n 0) ∪
    ((compressionBlock n 2 ∪ compressionBlock n 3) ∪ compressionRightRaw n 1)

theorem compressionBaseLeft_interval (n : ℕ) :
    compressionBaseLeft n = indexInterval n (4 * compressionHalfSize n)
      (n - compressionRightRawSize n - 4 * compressionHalfSize n) := by
  ext x
  have hf := compression_layout_feasible n
  simp only [compressionBaseLeft, compressionBlock, compressionLeftRaw, indexInterval,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold compressionLeftRawSize
  omega

theorem compressionBaseRight_intervals (n : ℕ) :
    compressionBaseRight n = indexInterval n 0 (4 * compressionHalfSize n) ∪
      indexInterval n (n - compressionRightRawSize n) (compressionRightRawSize n) := by
  ext x
  have hx := x.isLt
  have hf := compression_layout_feasible n
  simp only [compressionBaseRight, compressionBlock, compressionRightRaw, indexInterval,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, ↓reduceIte]
  norm_num only [Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem compressionBaseRight_complement (n : ℕ) :
    compressionBaseRight n = Finset.univ \ compressionBaseLeft n := by
  ext x
  have hx := x.isLt
  have hf := compression_layout_feasible n
  have hbound : 4 * compressionHalfSize n +
      (n - compressionRightRawSize n - 4 * compressionHalfSize n) =
        n - compressionRightRawSize n := by omega
  rw [compressionBaseRight_intervals, compressionBaseLeft_interval]
  simp only [indexInterval,
    Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    zero_le, zero_add, hbound]
  omega

theorem compression_left_exponent {n : ℕ} (hn : 40 ≤ n) :
    ((3 * compressionCapExponent n + compressionLeftRawSize n : ℕ) : ℝ) <
      (179 / 400 : ℝ) * n + 17 := by
  have hsize := mixerSize_bounds n
  have hh : mixerSize n = 2 * compressionHalfSize n := by
    rw [compressionHalfSize_eq]
    simp only [mixerSize]
    omega
  rw [hh, Nat.cast_mul, Nat.cast_ofNat] at hsize
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hslo : (3 / 25 : ℝ) * n - 4 < compressionHalfSize n := by linarith [hsize.1]
  have hshi : (compressionHalfSize n : ℝ) ≤ (3 / 25 : ℝ) * n := by linarith [hsize.2]
  have hapos : 0 ≤ (compressionHalfSize n : ℝ) - (3 / 400 : ℝ) * n := by linarith
  have ha : (compressionCapExponent n : ℝ) ≤
      compressionHalfSize n - (3 / 400 : ℝ) * n := Nat.floor_le hapos
  have hRlo : (1 / 20 : ℝ) * n - 1 < compressionRightRawSize n := by
    have hnat : n < 20 * (n / 20 + 1) := by omega
    have hr : (n : ℝ) < 20 * ((n / 20 : ℕ) + 1 : ℝ) := by exact_mod_cast hnat
    dsimp only [compressionRightRawSize]
    linarith
  have hf := compression_layout_feasible n
  have hsum : compressionLeftRawSize n + 7 * compressionHalfSize n +
      compressionRightRawSize n = n := by unfold compressionLeftRawSize; omega
  have hsumR : (compressionLeftRawSize n : ℝ) + 7 * compressionHalfSize n +
      compressionRightRawSize n = n := by exact_mod_cast hsum
  push_cast
  linarith

theorem compression_prime_floor (n : ℕ) :
    (249 / 1000 : ℝ) * n - 1 < compressionPrimeExponent n := by
  have hnat : 249 * n < 1000 * (249 * n / 1000 + 1) := by omega
  have hr : (249 : ℝ) * n < 1000 * ((249 * n / 1000 : ℕ) + 1 : ℝ) := by
    exact_mod_cast hnat
  dsimp only [compressionPrimeExponent]
  linarith

theorem compression_capacity_lower (n : ℕ) :
    (2 : ℝ) ^ ((199 / 1000 : ℝ) * n - 1) ≤ compressionDictionaryCapacity n := by
  have hnat : 199 * n < 1000 * (199 * n / 1000 + 1) := by omega
  have hr : (199 : ℝ) * n < 1000 * ((199 * n / 1000 : ℕ) + 1 : ℝ) := by
    exact_mod_cast hnat
  have he : (199 / 1000 : ℝ) * n - 1 ≤ (199 * n / 1000 : ℕ) := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  simpa only [compressionDictionaryCapacity, Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    using hp

theorem compression_bucket_loss_le_half {n : ℕ} (hn : 100000 ≤ n) {u : ℝ}
    (hu : 0 < u) (hlog : Real.logb 2 u ≤ (n : ℝ) / 1000000000) :
    16 * u ^ 2 * (2 : ℝ) ^ (3 * compressionCapExponent n + compressionLeftRawSize n) /
      ((compressionDictionaryCapacity n : ℝ) * (2 : ℝ) ^ compressionPrimeExponent n) ≤ 1 / 2 := by
  have hu2 : u ^ 2 = (2 : ℝ) ^ (2 * Real.logb 2 u) := by
    have h := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (Real.logb 2 u) 2
    rw [Real.rpow_logb (by norm_num) (by norm_num) hu] at h
    simpa only [Nat.cast_ofNat, mul_comm] using h.symm
  have hnR : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have he := compression_left_exponent (by omega : 40 ≤ n)
  have hnum : 16 * u ^ 2 * (2 : ℝ) ^ (3 * compressionCapExponent n + compressionLeftRawSize n) ≤
      (2 : ℝ) ^ ((56 / 125 : ℝ) * n - 3) := by
    have hid : 16 * u ^ 2 * (2 : ℝ) ^ (3 * compressionCapExponent n + compressionLeftRawSize n) =
        (2 : ℝ) ^ (4 + 2 * Real.logb 2 u +
          ((3 * compressionCapExponent n + compressionLeftRawSize n : ℕ) : ℝ)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), ← hu2,
        Real.rpow_natCast]
      norm_num
    rw [hid]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hp : (2 : ℝ) ^ ((249 / 1000 : ℝ) * n - 1) ≤
      (2 : ℝ) ^ compressionPrimeExponent n := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (compression_prime_floor n).le
    simpa only [Real.rpow_natCast] using h
  have hden : (2 : ℝ) ^ ((56 / 125 : ℝ) * n - 2) ≤
      (compressionDictionaryCapacity n : ℝ) * (2 : ℝ) ^ compressionPrimeExponent n := by
    calc
      _ = (2 : ℝ) ^ ((199 / 1000 : ℝ) * n - 1) *
          (2 : ℝ) ^ ((249 / 1000 : ℝ) * n - 1) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul (compression_capacity_lower n) hp (by positivity) (by positivity)
  have hrel : 2 * (2 : ℝ) ^ ((56 / 125 : ℝ) * n - 3) =
      (2 : ℝ) ^ ((56 / 125 : ℝ) * n - 2) := by
    rw [show (56 / 125 : ℝ) * n - 2 = 1 + ((56 / 125 : ℝ) * n - 3) by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
  have hcap : (0 : ℝ) < compressionDictionaryCapacity n := by
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) (199 * n / 1000))
  apply (div_le_iff₀ (mul_pos hcap (by positivity))).mpr
  nlinarith

structure CompressionSetup (n : ℕ) where
  input : Instance n
  solution : Finset (Fin n)
  solution_weight : weight (fun i => (input.values i : ℤ)) solution = input.target

namespace CompressionSetup

variable {n : ℕ} (R : CompressionSetup n)

def weights : Fin n → ℤ := fun i => R.input.values i
def block (_R : CompressionSetup n) (e : Equiv.Perm (Fin n)) (i : Fin 7) : Finset (Fin n) :=
  permuteSubset e (compressionBlock n i)
def leftRaw (_R : CompressionSetup n) (e : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  permuteSubset e (compressionLeftRaw n)
def leftDomain (e : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  ((R.block e 4 ∪ R.block e 5) ∪ R.block e 6) ∪ R.leftRaw e
def rightDomain (e : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ \ R.leftDomain e

def rightRaw (e : Equiv.Perm (Fin n)) (i : Fin 2) : Finset (Fin n) :=
  permuteSubset e (compressionRightRaw n i)

/-- The four rows in the compression table, with their actual index domains. -/
def groupDomain (e : Equiv.Perm (Fin n)) : Fin 4 → Finset (Fin n) :=
  ![R.block e 4 ∪ R.block e 5, R.block e 6 ∪ R.leftRaw e,
    (R.block e 0 ∪ R.block e 1) ∪ rightRaw e 0,
    (R.block e 2 ∪ R.block e 3) ∪ rightRaw e 1]

def groupWeights (e : Equiv.Perm (Fin n)) (i : Fin 4) : Finset ℤ :=
  distinctSums R.weights (R.groupDomain e i)

theorem leftDomain_eq_groups (e : Equiv.Perm (Fin n)) :
    R.leftDomain e = R.groupDomain e 0 ∪ R.groupDomain e 1 := by
  change ((_ ∪ _) ∪ _) ∪ _ = (_ ∪ _) ∪ (_ ∪ _)
  rw [Finset.union_assoc]

theorem rightDomain_eq_groups (e : Equiv.Perm (Fin n)) :
    R.rightDomain e = R.groupDomain e 2 ∪ R.groupDomain e 3 := by
  have hl : R.leftDomain e = permuteSubset e (compressionBaseLeft n) := by
    simp only [leftDomain, block, leftRaw, compressionBaseLeft, permuteSubset, Finset.map_union]
  have hr : R.groupDomain e 2 ∪ R.groupDomain e 3 =
      permuteSubset e (compressionBaseRight n) := by
    change ((R.block e 0 ∪ R.block e 1) ∪ rightRaw e 0) ∪
      ((R.block e 2 ∪ R.block e 3) ∪ rightRaw e 1) = _
    simp only [block, rightRaw, compressionBaseRight, permuteSubset, Finset.map_union]
  rw [rightDomain, hl, hr, compressionBaseRight_complement, permuteSubset_sdiff]
  congr 1
  exact (Finset.map_univ_equiv e).symm

def blockWeights (e : Equiv.Perm (Fin n)) (i : Fin 7) : Finset ℤ :=
  distinctSums R.weights (R.block e i)
def leftWeights (e : Equiv.Perm (Fin n)) : Finset ℤ :=
  distinctSums R.weights (R.leftDomain e)
def rightWeights (e : Equiv.Perm (Fin n)) : Finset ℤ :=
  distinctSums R.weights (R.rightDomain e)
def solutionLeft (e : Equiv.Perm (Fin n)) : Finset (Fin n) := R.solution ∩ R.leftDomain e
def solutionRight (e : Equiv.Perm (Fin n)) : Finset (Fin n) := R.solution \ R.leftDomain e
def leftWeight (e : Equiv.Perm (Fin n)) : ℤ := weight R.weights (R.solutionLeft e)
def rightWeight (e : Equiv.Perm (Fin n)) : ℤ := weight R.weights (R.solutionRight e)

def Passing (e : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, (R.blockWeights e i).card ≤ 2 ^ compressionCapExponent n

theorem leftWeight_mem (e : Equiv.Perm (Fin n)) : R.leftWeight e ∈ R.leftWeights e :=
  (mem_distinctSums _ _ _).mpr ⟨_, Finset.inter_subset_right, rfl⟩

theorem rightWeight_mem (e : Equiv.Perm (Fin n)) : R.rightWeight e ∈ R.rightWeights e :=
  (mem_distinctSums _ _ _).mpr ⟨_, fun _ hx => Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩, rfl⟩

theorem solution_split (e : Equiv.Perm (Fin n)) :
    R.leftWeight e + R.rightWeight e = R.input.target := by
  have hd : Disjoint (R.solutionLeft e) (R.solutionRight e) :=
    Finset.disjoint_sdiff_inter _ _ |>.symm
  have hcover : R.solutionLeft e ∪ R.solutionRight e = R.solution := by
    ext x
    simp only [solutionLeft, solutionRight, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [leftWeight, rightWeight, ← weight_union _ hd, hcover]
  exact R.solution_weight

theorem four_group_solution (e : Equiv.Perm (Fin n)) :
    ∃ x : Fin 4 → ℤ, (∀ i, x i ∈ R.groupWeights e i) ∧
      x 0 + x 1 = R.leftWeight e ∧ x 2 + x 3 = R.rightWeight e := by
  have hl := R.leftWeight_mem e
  have hr := R.rightWeight_mem e
  rw [leftWeights, R.leftDomain_eq_groups e] at hl
  rw [rightWeights, R.rightDomain_eq_groups e] at hr
  obtain ⟨l, hl, hwl⟩ := Finset.mem_image.mp
    (distinctSums_union_subset R.weights (R.groupDomain e 0) (R.groupDomain e 1) hl)
  obtain ⟨r, hr, hwr⟩ := Finset.mem_image.mp
    (distinctSums_union_subset R.weights (R.groupDomain e 2) (R.groupDomain e 3) hr)
  obtain ⟨hl0, hl1⟩ := Finset.mem_product.mp hl
  obtain ⟨hr0, hr1⟩ := Finset.mem_product.mp hr
  refine ⟨![l.1, l.2, r.1, r.2], ?_, hwl, hwr⟩
  intro i
  fin_cases i
  · exact hl0
  · exact hl1
  · exact hr0
  · exact hr1

theorem passing_probability (hn : 168000000 ≤ n)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency R.weights Finset.univ (compressionHalfSize n)) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability R.Passing :=
  compression_size_tests_probability hn R.weights (compressionBlock n)
    (compressionBlock_card n) hmean

theorem leftWeights_card (e : Equiv.Perm (Fin n)) (he : R.Passing e) :
    (R.leftWeights e).card ≤ 2 ^ (3 * compressionCapExponent n + compressionLeftRawSize n) := by
  have h4 := he 4
  have h5 := he 5
  have h6 := he 6
  have hr : distinctSumCount R.weights (R.leftRaw e) ≤ 2 ^ compressionLeftRawSize n := by
    simpa only [leftRaw, permuteSubset_card, compressionLeftRaw_card] using
      distinctSumCount_le_pow R.weights (R.leftRaw e)
  apply (distinctSumCount_union_le _ _ _).trans
  apply (Nat.mul_le_mul (distinctSumCount_union_le _ _ _) (le_refl _)).trans
  apply (Nat.mul_le_mul (Nat.mul_le_mul (distinctSumCount_union_le _ _ _)
    (le_refl _)) (le_refl _)).trans
  have hp := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h4 h5) h6) hr
  have heq : compressionCapExponent n + compressionCapExponent n + compressionCapExponent n +
      compressionLeftRawSize n = 3 * compressionCapExponent n + compressionLeftRawSize n := by omega
  simpa only [← pow_add, heq, blockWeights, distinctSumCount] using hp

abbrev PrimeSpace (n : ℕ) := ↥(primeRange (compressionPrimeExponent n))

def BucketFits (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) : Prop :=
  (hashBucket (R.leftWeights e) id (fun w => w % (q.val : ℤ)) (R.leftWeight e)).card ≤
    compressionDictionaryCapacity n

theorem leftWeights_magnitude (e : Equiv.Perm (Fin n)) {x : ℤ}
    (hx : x ∈ R.leftWeights e) : x.natAbs ≤ n * 2 ^ inputBits R.input := by
  obtain ⟨S, _, rfl⟩ := (mem_distinctSums R.weights (R.leftDomain e) x).mp hx
  simpa only [Fintype.card_fin] using weight_natAbs_le R.weights S
    (M := 2 ^ inputBits R.input) (fun i => by
      simpa only [weights, Int.natAbs_natCast] using (value_lt_two_pow_bits R.input i).le)

theorem bucketFits_probability (hn : 168000000 ≤ n)
    (hlog : Real.logb 2 (inputScale R.input) ≤ (n : ℝ) / 1000000000)
    (e : Equiv.Perm (Fin n)) (he : R.Passing e) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability (R.BucketFits e) := by
  have hell : 4 ≤ compressionPrimeExponent n := by unfold compressionPrimeExponent; omega
  have hellu : compressionPrimeExponent n ≤ inputScale R.input := by
    unfold compressionPrimeExponent inputScale
    omega
  have hcap : 2 ≤ compressionDictionaryCapacity n := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show 1 ≤ 199 * n / 1000 by omega)
    simpa only [pow_one, compressionDictionaryCapacity] using hpow
  have hx := R.leftWeight_mem e
  have hequal : sameWeightKeys (R.leftWeights e) id (R.leftWeight e) = {R.leftWeight e} := by
    ext y
    simp only [sameWeightKeys, Finset.mem_filter, id_eq, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hx, h⟩⟩
  have hp := prime_fixed_bucket_fits_probability (R.leftWeights e) id hx hell hellu
    (by omega : 0 < compressionDictionaryCapacity n)
    (by
      rw [hequal, Finset.card_singleton]
      have hcR : (2 : ℝ) ≤ compressionDictionaryCapacity n := by exact_mod_cast hcap
      push_cast
      linarith)
    (fun x hx y hy => relevant_difference_bits R.input
      ((R.leftWeights_magnitude e hx).trans (by gcongr; omega))
      ((R.leftWeights_magnitude e hy).trans (by gcongr; omega)))
  have hcount : ((R.leftWeights e).card : ℝ) ≤
      (2 : ℝ) ^ (3 * compressionCapExponent n + compressionLeftRawSize n) := by
    exact_mod_cast R.leftWeights_card e he
  have hu : (0 : ℝ) < inputScale R.input := by unfold inputScale; positivity
  have hden : (0 : ℝ) < (compressionDictionaryCapacity n : ℝ) *
      (2 : ℝ) ^ compressionPrimeExponent n := by positivity
  have hloss : 16 * (inputScale R.input : ℝ) ^ 2 * (R.leftWeights e).card /
      ((compressionDictionaryCapacity n : ℝ) * (2 : ℝ) ^ compressionPrimeExponent n) ≤ 1 / 2 := by
    apply le_trans _ (compression_bucket_loss_le_half (by omega) hu hlog)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcount (by positivity)) hden.le
  have hprob : finiteUniformProbability (R.BucketFits e) =
      ∑ p ∈ (primeRange (compressionPrimeExponent n)).filter (fun (p : ℕ) =>
        (hashBucket (R.leftWeights e) id (fun w => w % (p : ℤ)) (R.leftWeight e)).card ≤
          compressionDictionaryCapacity n), primeProbability (compressionPrimeExponent n) p := by
    unfold BucketFits
    rw [finiteUniformProbability_finset (primeRange (compressionPrimeExponent n))
      (fun p : ℕ => (hashBucket (R.leftWeights e) id (fun w => w % (p : ℤ))
        (R.leftWeight e)).card ≤ compressionDictionaryCapacity n)]
    simp [primeProbability, div_eq_mul_inv, mul_comm]
  rw [hprob]
  linarith

abbrev TrialHistory (n : ℕ) := Σ _e : Equiv.Perm (Fin n), PrimeSpace n

def primeLaw (hn : 168000000 ≤ n) : FiniteLaw (PrimeSpace n) := by
  have hell : 4 ≤ compressionPrimeExponent n := by unfold compressionPrimeExponent; omega
  let : Nonempty (PrimeSpace n) :=
    ⟨⟨(primeRange_nonempty hell).choose, (primeRange_nonempty hell).choose_spec⟩⟩
  exact FiniteLaw.uniform

def trialLaw (_R : CompressionSetup n) (hn : 168000000 ≤ n) : FiniteLaw (TrialHistory n) :=
  (FiniteLaw.uniform : FiniteLaw (Equiv.Perm (Fin n))).bind (fun _ => PrimeSpace n)
    (fun _ => primeLaw hn)

def Successful (h : TrialHistory n) : Prop := R.Passing h.1 ∧ R.BucketFits h.1 h.2

/-- A passing partition has probability at least one half, and conditional
on every such actual partition its fixed solution bucket fits with probability
at least one half. No uniform residue guess appears in this experiment. -/
theorem successful_probability (hn : 168000000 ≤ n)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency R.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale R.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 4 : ℝ) ≤ (R.trialLaw hn).probability R.Successful := by
  have hp : (1 / 2 : ℝ) ≤ (FiniteLaw.uniform : FiniteLaw (Equiv.Perm (Fin n))).probability
      R.Passing := by rw [FiniteLaw.uniform_probability]; exact R.passing_probability hn hmean
  have h := FiniteLaw.bind_good_lower (FiniteLaw.uniform : FiniteLaw (Equiv.Perm (Fin n)))
    (fun _ => PrimeSpace n) (fun _ => primeLaw hn) R.Passing R.BucketFits
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hp (fun e he => by
      have hell : 4 ≤ compressionPrimeExponent n := by unfold compressionPrimeExponent; omega
      let : Nonempty (PrimeSpace n) :=
        ⟨⟨(primeRange_nonempty hell).choose, (primeRange_nonempty hell).choose_spec⟩⟩
      rw [primeLaw, FiniteLaw.uniform_probability]
      exact R.bucketFits_probability hn hlog e he)
  norm_num at h ⊢
  exact h

/-- The loop scans this residue among all `0,…,q−1`. Its dictionary is
small enough and contains the fixed solution's left weight. -/
theorem designated_bucket_witness (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (hq : R.BucketFits e q) :
    ∃ z : Fin q.val, ∃ x : Fin 4 → ℤ,
      (∀ i, x i ∈ R.groupWeights e i) ∧
      x 0 + x 1 + (x 2 + x 3) = R.input.target ∧
      x 0 + x 1 ≡ (z.val : ℤ) [ZMOD (q.val : ℤ)] ∧
      x 2 + x 3 ≡ (R.input.target : ℤ) - z.val [ZMOD (q.val : ℤ)] ∧
      (R.leftWeights e |>.filter (fun w => w % (q.val : ℤ) = z.val)).card ≤
        compressionDictionaryCapacity n := by
  have hpos := (primeRange_prime q.property).pos
  let z := normalizedResidue hpos (R.leftWeight e)
  obtain ⟨x, hx, hl, hr⟩ := R.four_group_solution e
  have hmod : R.leftWeight e ≡ (z.val : ℤ) [ZMOD (q.val : ℤ)] :=
    normalizedResidue_eq_modEq hpos _ z rfl
  have hright : R.rightWeight e = (R.input.target : ℤ) - R.leftWeight e := by
    have hs := R.solution_split e
    omega
  refine ⟨z, x, hx, ?_, ?_, ?_, ?_⟩
  · rw [hl, hr]
    exact R.solution_split e
  · rwa [hl]
  · rw [hr, hright]
    exact (Int.ModEq.refl (R.input.target : ℤ)).sub hmod
  · have hz : (z.val : ℤ) = R.leftWeight e % (q.val : ℤ) := normalizedResidue_cast hpos _
    simpa only [BucketFits, hashBucket, id_eq, hz] using hq

end CompressionSetup

end LowSpaceSubsetSum

end

end OAI
