import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteKernels
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilies
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.NestedOccupancy
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes
import Mathlib.Data.Fin.Tuple.Sort

namespace OAI

/-!
# The representation experiment preceding the extra prime

The sample space retains each draw in order. The subblock partitions and
the residue spaces use conditional uniform laws on their actual domains.
Representative selection is a deterministic analysis function of this
history; it does not inspect the extra prime or the separating families.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable

/-- A fixed YES instance and the three pre-order mixer locations. -/
structure RepresentationSetup (n : ℕ) where
  input : Instance n
  solution : Finset (Fin n)
  solution_weight : weight (fun i => (input.values i : ℤ)) solution = input.target
  mixers : Fin 3 → Finset (Fin n)
  disjoint : ∀ i j, i ≠ j → Disjoint (mixers i) (mixers j)
  card : ∀ i, (mixers i).card = mixerSize n

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

abbrev Layout (n : ℕ) := Equiv.Perm (Fin n) × Finset (Fin n)

def originalWeights : Fin n → ℤ := fun i => R.input.values i

def signMask (z : Layout n) : Finset (Fin n) := R.solution ∆ z.2

def signedWeights (z : Layout n) : Fin n → ℤ := flip R.originalWeights (R.signMask z)

def signedTarget (z : Layout n) : ℤ :=
  R.input.target - weight R.originalWeights (R.signMask z)

def signCoordinates : Layout n ≃ Layout n where
  toFun z := (z.1, R.signMask z)
  invFun z := (z.1, R.signMask z)
  left_inv z := by simp [signMask, symmDiff_symmDiff_cancel_left]
  right_inv z := by simp [signMask, symmDiff_symmDiff_cancel_left]

theorem signCoordinates_uniform (P : Layout n → Prop) :
    finiteUniformProbability (fun z : Layout n => P (z.1, R.signMask z)) =
      finiteUniformProbability P :=
  finiteUniformProbability_equiv R.signCoordinates P

theorem signed_solution (z : Layout n) :
    weight (R.signedWeights z) z.2 = R.signedTarget z := by
  rw [signedWeights, weight_flip, signMask]
  have h : z.2 ∆ (R.solution ∆ z.2) = R.solution := by
    rw [symmDiff_comm R.solution, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
  rw [h]
  exact congrArg (fun x : ℤ => x - weight R.originalWeights (R.signMask z))
    R.solution_weight

def rawMixers (z : Layout n) (i : Fin 3) : Finset (Fin n) :=
  permuteSubset z.1 (R.mixers i)

def mixerOrder (z : Layout n) : Equiv.Perm (Fin 3) :=
  Tuple.sort (fun i => deficiency R.originalWeights (R.rawMixers z i))

def orderedMixers (z : Layout n) (i : Fin 3) : Finset (Fin n) :=
  R.rawMixers z (R.mixerOrder z i)

def selectedHalves (z : Layout n) (i : Fin 3) : Finset (Fin n) :=
  z.2 ∩ R.orderedMixers z i

def halfSize (_R : RepresentationSetup n) : ℕ := mixerSize n / 2

def lowExponent (z : Layout n) (i : Fin 3) : ℝ :=
  R.halfSize - min ((39 / 5000 : ℝ) * n)
    (deficiency R.originalWeights (R.orderedMixers z i) / 2)

def GoodLayout (z : Layout n) : Prop :=
  MixerBalanced (R.rawMixers z) R.halfSize z.2 ∧
    actualLayoutSuccess R.originalWeights R.mixers z

theorem halfSize_eq : R.halfSize = 4 * (3 * n / 100) := by
  simp only [halfSize, mixerSize]
  omega

theorem orderedMixers_card (z : Layout n) (i : Fin 3) :
    (R.orderedMixers z i).card = 2 * R.halfSize := by
  rw [orderedMixers, rawMixers, permuteSubset_card, R.card, R.halfSize_eq]
  simp only [mixerSize]
  omega

theorem selectedHalves_subset (z : Layout n) (i : Fin 3) :
    R.selectedHalves z i ⊆ R.orderedMixers z i := Finset.inter_subset_right

theorem selectedHalves_card {z : Layout n} (hz : R.GoodLayout z) (i : Fin 3) :
    (R.selectedHalves z i).card = R.halfSize := by
  have h := hz.1 (R.mixerOrder z i)
  simpa only [selectedHalves, orderedMixers, Finset.inter_comm] using h

theorem selectedHalves_deficiency {z : Layout n} (hz : R.GoodLayout z) (i : Fin 3) :
    deficiency (R.signedWeights z) (R.selectedHalves z i) ≤
      min ((39 / 5000 : ℝ) * n)
        (deficiency R.originalWeights (R.orderedMixers z i) / 2) := by
  rw [signedWeights, deficiency_flip]
  exact hz.2.1 (R.mixerOrder z i)

theorem lowExponent_nonneg (z : Layout n) (i : Fin 3) :
    0 ≤ R.lowExponent z i := by
  have hd := deficiency_le_card R.originalWeights (R.orderedMixers z i)
  rw [R.orderedMixers_card, Nat.cast_mul, Nat.cast_ofNat] at hd
  have hm := min_le_right ((39 / 5000 : ℝ) * n)
    (deficiency R.originalWeights (R.orderedMixers z i) / 2)
  dsimp only [lowExponent]
  linarith

theorem lowExponent_le_halfSize (z : Layout n) (i : Fin 3) :
    R.lowExponent z i ≤ R.halfSize := by
  have hm : 0 ≤ min ((39 / 5000 : ℝ) * n)
      (deficiency R.originalWeights (R.orderedMixers z i) / 2) :=
    le_min (by positivity) (div_nonneg (deficiency_nonneg _ _) (by norm_num))
  exact sub_le_self _ hm

theorem lowExponent_antitone (z : Layout n) : Antitone (R.lowExponent z) := by
  intro i j hij
  have hsort := Tuple.monotone_sort
    (fun i => deficiency R.originalWeights (R.rawMixers z i)) hij
  have hmin : min ((39 / 5000 : ℝ) * n)
      (deficiency R.originalWeights (R.orderedMixers z i) / 2) ≤
      min ((39 / 5000 : ℝ) * n)
        (deficiency R.originalWeights (R.orderedMixers z j) / 2) :=
    min_le_min_left _ (div_le_div_of_nonneg_right hsort (by norm_num))
  exact sub_le_sub_left hmin _

def factorExponents (z : Layout n) : Fin 3 → ℕ :=
  ![⌊R.lowExponent z 2⌋₊,
    ⌊R.lowExponent z 1⌋₊ - ⌊R.lowExponent z 2⌋₊,
    ⌊R.lowExponent z 0⌋₊ - ⌊R.lowExponent z 1⌋₊]

theorem prefixExponent_eq_floor (z : Layout n) (i : Fin 3) :
    prefixExponent (R.factorExponents z 0) (R.factorExponents z 1)
      (R.factorExponents z 2) i = ⌊R.lowExponent z i⌋₊ := by
  have h21 := Nat.floor_mono (R.lowExponent_antitone z (by decide : (1 : Fin 3) ≤ 2))
  have h10 := Nat.floor_mono (R.lowExponent_antitone z (by decide : (0 : Fin 3) ≤ 1))
  fin_cases i
  · change ⌊R.lowExponent z 2⌋₊ + (⌊R.lowExponent z 1⌋₊ - ⌊R.lowExponent z 2⌋₊) +
      (⌊R.lowExponent z 0⌋₊ - ⌊R.lowExponent z 1⌋₊) = ⌊R.lowExponent z 0⌋₊
    omega
  · change ⌊R.lowExponent z 2⌋₊ + (⌊R.lowExponent z 1⌋₊ - ⌊R.lowExponent z 2⌋₊) =
      ⌊R.lowExponent z 1⌋₊
    omega
  · rfl

theorem factorExponents_le_scale (z : Layout n) (i : Fin 3) :
    R.factorExponents z i ≤ inputScale R.input := by
  have hs : R.halfSize ≤ n := by
    have hm := R.orderedMixers_card z 0
    have hc := Finset.card_le_univ (R.orderedMixers z 0)
    simp only [Fintype.card_fin] at hc
    omega
  have hf (j : Fin 3) : ⌊R.lowExponent z j⌋₊ ≤ n :=
    Nat.floor_le_of_le ((R.lowExponent_le_halfSize z j).trans (by exact_mod_cast hs))
  have hn : n ≤ inputScale R.input := by unfold inputScale; omega
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  fin_cases i
  · change ⌊R.lowExponent z 2⌋₊ ≤ inputScale R.input
    omega
  · change ⌊R.lowExponent z 1⌋₊ - ⌊R.lowExponent z 2⌋₊ ≤ inputScale R.input
    omega
  · change ⌊R.lowExponent z 0⌋₊ - ⌊R.lowExponent z 1⌋₊ ≤ inputScale R.input
    omega

def SizeGood (z : Layout n) (i : Fin 3) (k : ℕ) : Prop :=
  (R.selectedHalves z i).card < 3 * k ∧ k ≤ (R.selectedHalves z i).card / 2 ∧
    (2 : ℝ) ^ R.lowExponent z i / ((R.selectedHalves z i).card + 1) ≤
      (sumsAtSize (R.signedWeights z) (R.selectedHalves z i) k).card

def chosenSize (z : Layout n) (i : Fin 3) : ℕ :=
  if h : ∃ k, R.SizeGood z i k then h.choose else 0

theorem chosenSize_spec {z : Layout n} (hz : R.GoodLayout z)
    (hn : 2200 ≤ n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize)) (i : Fin 3) :
    R.SizeGood z i (R.chosenSize z i) := by
  have hc := R.selectedHalves_card hz i
  have hd := R.selectedHalves_deficiency hz i
  have ht := half_mixer_deficiency_threshold hn
  have hds : deficiency (R.signedWeights z) (R.selectedHalves z i) ≤
      (33 / 500 : ℝ) * R.halfSize := (hd.trans (min_le_left _ _)).trans ht
  have hs : 0 < R.halfSize := by
    rw [R.halfSize_eq]
    omega
  have hgap : binaryEntropy (1 / 3) + (1 / 1500 : ℝ) < 467 / 500 := by
    linarith [binaryEntropy_third_lt]
  have hexp : (R.halfSize : ℝ) * binaryEntropy (1 / 3) +
      (1 / 1500 : ℝ) * R.halfSize <
      (R.halfSize : ℝ) - deficiency (R.signedWeights z) (R.selectedHalves z i) := by
    have hsR : (0 : ℝ) < R.halfSize := by exact_mod_cast hs
    nlinarith
  have hcount : (2 : ℝ) ^ ((R.selectedHalves z i).card * binaryEntropy (1 / 3)) <
      (distinctSumCount (R.signedWeights z) (R.selectedHalves z i) : ℝ) /
        ((R.selectedHalves z i).card + 1) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (R.selectedHalves z i).card + 1)).mpr
    rw [← two_pow_card_sub_deficiency, hc]
    calc
      _ < (2 : ℝ) ^ ((R.halfSize : ℝ) * binaryEntropy (1 / 3)) *
          (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize) :=
        mul_lt_mul_of_pos_left hden (Real.rpow_pos_of_pos (by norm_num) _)
      _ = _ := (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  obtain ⟨k, hk, hupper, hmany⟩ := exists_representative_size_range
    (R.signedWeights z) (R.selectedHalves z i) (by omega) hcount
  have hL : R.lowExponent z i ≤ (R.selectedHalves z i).card -
      deficiency (R.signedWeights z) (R.selectedHalves z i) := by
    dsimp only [lowExponent]
    rw [hc]
    linarith
  have hexists : ∃ k, R.SizeGood z i k := by
    refine ⟨k, hk, hupper, ?_⟩
    apply le_trans _ hmany
    rw [← two_pow_card_sub_deficiency]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hL) (by positivity)
  simpa only [chosenSize, hexists, ↓reduceDIte] using hexists.choose_spec

/-- The precise interval sampled by the implementation. -/
def guessRange (n : ℕ) : Finset ℕ :=
  Finset.Icc ((mixerSize n + 5) / 6) (mixerSize n / 4)

abbrev Guesses (n : ℕ) := Fin 3 → ↥(guessRange n)

theorem guessRange_nonempty (n : ℕ) : (guessRange n).Nonempty := by
  refine ⟨mixerSize n / 4, Finset.mem_Icc.mpr ⟨?_, le_rfl⟩⟩
  simp only [mixerSize]
  omega

instance guessesNonempty : Nonempty (Guesses n) :=
  ⟨fun _ => ⟨(guessRange_nonempty n).choose, (guessRange_nonempty n).choose_spec⟩⟩

def GoodGuesses (z : Layout n) (g : Guesses n) : Prop :=
  ∀ i, (g i).val = R.chosenSize z i

def blockCount : Fin 3 → ℕ := ![4, 2, 2]

def blockHalf (n : ℕ) : Fin 3 → ℕ :=
  ![3 * n / 100, 2 * (3 * n / 100), 2 * (3 * n / 100)]

theorem blockCount_half (i : Fin 3) :
    blockCount i * blockHalf n i = R.halfSize := by
  rw [R.halfSize_eq]
  fin_cases i
  · rfl
  · change 2 * (2 * (3 * n / 100)) = 4 * (3 * n / 100)
    omega
  · change 2 * (2 * (3 * n / 100)) = 4 * (3 * n / 100)
    omega

abbrev Partition (z : Layout n) (i : Fin 3) :=
  MatchingSmoothing.Colorings ↥(R.orderedMixers z i) (Fin (blockCount i))
    (fun _ => 2 * blockHalf n i)

abbrev Partitions (z : Layout n) := ∀ i, R.Partition z i

instance partitionNonempty (z : Layout n) (i : Fin 3) : Nonempty (R.Partition z i) := by
  obtain ⟨f, hf⟩ := exists_coloring_of_sum ↥(R.orderedMixers z i)
    (fun _ : Fin (blockCount i) => 2 * blockHalf n i) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Fintype.card_coe, R.orderedMixers_card]
      rw [← R.blockCount_half i]
      ring)
  exact ⟨⟨f, hf⟩⟩

instance partitionsNonempty (z : Layout n) : Nonempty (R.Partitions z) := by
  exact ⟨fun i => Classical.choice (R.partitionNonempty z i)⟩

def Prescribed (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (i : Fin 3) (r : ↥(sumsAtSize (R.signedWeights z) (R.selectedHalves z i) (g i).val)) :
    Prop :=
  representativePrescriptions
    (representativeMask_spec (R.signedWeights z) (R.selectedHalves z i) (g i).val r).1
    (R.selectedHalves_subset z i)
    (representativeBlockProfile (blockCount i) (blockHalf n i) (g i).val) (f i)

def retainedWeights (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (i : Fin 3) : Finset ℤ :=
  survivingWeights (R.signedWeights z)
    (representativeMask (R.signedWeights z) (R.selectedHalves z i) (g i).val)
    (R.Prescribed z g f i)

def GoodPartitions (z : Layout n) (g : Guesses n) (f : R.Partitions z) : Prop :=
  ∀ i, (2 : ℝ) ^ R.lowExponent z i / (inputScale R.input : ℝ) ^ 14 ≤
    (R.retainedWeights z g f i).card

abbrev PrimeSpace (z : Layout n) :=
  ↥(tripleRange (R.factorExponents z 0) (R.factorExponents z 1) (R.factorExponents z 2))

instance primeSpaceNonempty (z : Layout n) : Nonempty (R.PrimeSpace z) :=
  ⟨⟨(tripleRange_nonempty _ _ _).choose, (tripleRange_nonempty _ _ _).choose_spec⟩⟩

abbrev Residues {_z : Layout n} (p : R.PrimeSpace _z) :=
  Fin (prefixModulus p.val 0) × Fin (prefixModulus p.val 1) × Fin (prefixModulus p.val 2)

instance residuesNonempty {_z : Layout n} (p : R.PrimeSpace _z) : Nonempty (R.Residues p) :=
  ⟨⟨⟨0, prefixModulus_pos p 0⟩, ⟨0, prefixModulus_pos p 1⟩,
    ⟨0, prefixModulus_pos p 2⟩⟩⟩

def GoodPrime (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (p : R.PrimeSpace z) : Prop :=
  ∀ i, (prefixModulus p.val i : ℝ) / (inputScale R.input : ℝ) ^ 16 ≤
    ((R.retainedWeights z g f i).image (fun x => x % (prefixModulus p.val i : ℤ))).card

abbrev GuessHistory (_R : RepresentationSetup n) := Σ _z : Layout n, Guesses n
abbrev PartitionHistory := Σ h : R.GuessHistory, R.Partitions h.1
abbrev PrimeHistory := Σ h : R.PartitionHistory, R.PrimeSpace h.1.1
abbrev TrialHistory := Σ h : R.PrimeHistory, R.Residues h.2

def layoutLaw (_R : RepresentationSetup n) : FiniteLaw (Layout n) := FiniteLaw.uniform

def guessLaw : FiniteLaw R.GuessHistory :=
  R.layoutLaw.bind (fun _ => Guesses n) (fun _ => FiniteLaw.uniform)

def partitionLaw : FiniteLaw R.PartitionHistory :=
  R.guessLaw.bind (fun h => R.Partitions h.1) (fun _ => FiniteLaw.uniform)

def primeLaw : FiniteLaw R.PrimeHistory :=
  R.partitionLaw.bind (fun h => R.PrimeSpace h.1.1) (fun _ => FiniteLaw.uniform)

def trialLaw : FiniteLaw R.TrialHistory :=
  R.primeLaw.bind (fun h => R.Residues h.2) (fun _ => FiniteLaw.uniform)

theorem mixerSize_add_one_le_scale :
    (mixerSize n : ℝ) + 1 ≤ inputScale R.input := by
  have hm := Finset.card_le_univ (R.mixers 0)
  rw [R.card, Fintype.card_fin] at hm
  have hnat : mixerSize n + 1 ≤ inputScale R.input := by
    unfold inputScale
    omega
  exact_mod_cast hnat

theorem goodLayout_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n) :
    1 / (16 * (inputScale R.input : ℝ) ^ 3) ≤ R.layoutLaw.probability R.GoodLayout := by
  have hs : (R.halfSize : ℝ) ≤ (3 / 25 : ℝ) * n := by
    have hm := (mixerSize_bounds n).2
    have he : mixerSize n = 2 * R.halfSize := by
      rw [R.halfSize_eq]
      simp only [mixerSize]
      omega
    rw [he, Nat.cast_mul, Nat.cast_ofNat] at hm
    linarith
  have hcard : ∀ i, (R.mixers i).card = 2 * R.halfSize := by
    intro i
    rw [R.card, R.halfSize_eq]
    simp only [mixerSize]
    omega
  have hm : ((2 * R.halfSize : ℕ) : ℝ) ≤ (6 / 25 : ℝ) * n := by
    push_cast
    linarith
  have h := signed_layout_survival_probability hn hs hm
    R.originalWeights R.mixers R.disjoint hcard hmean
  rw [layoutLaw, FiniteLaw.uniform_probability]
  apply le_trans _ h
  apply one_div_le_one_div_of_le (by positivity)
  have hbase : ((2 * R.halfSize + 1 : ℕ) : ℝ) ≤ inputScale R.input := by
    have hh := R.mixerSize_add_one_le_scale
    have he := R.orderedMixers_card (1, ∅) 0
    rw [orderedMixers, rawMixers, permuteSubset_card, R.card] at he
    simpa only [he, Nat.cast_add, Nat.cast_one] using hh
  gcongr

theorem goodGuesses_probability {z : Layout n} (hz : R.GoodLayout z)
    (hn : 2200 ≤ n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize)) :
    1 / (inputScale R.input : ℝ) ^ 3 ≤
      finiteUniformProbability (R.GoodGuesses z) := by
  have hk (i : Fin 3) : R.chosenSize z i ∈ guessRange n := by
    have h := R.chosenSize_spec hz hn hden i
    simp only [SizeGood] at h
    rw [R.selectedHalves_card hz i] at h
    rw [R.halfSize_eq] at h
    apply Finset.mem_Icc.mpr
    dsimp only [mixerSize]
    constructor <;> omega
  let g : Guesses n := fun i => ⟨R.chosenSize z i, hk i⟩
  have hevent : R.GoodGuesses z = (fun x : Guesses n => x = g) := by
    funext x
    apply propext
    constructor
    · intro h
      funext i
      exact Subtype.ext (h i)
    · rintro rfl i
      rfl
  rw [hevent]
  have hp : finiteUniformProbability (fun x : Guesses n => x = g) =
      1 / (guessRange n).card ^ 3 := by
    rw [finiteUniformProbability_eq_indicator_mean]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
    simp
  rw [hp]
  have hc : ((guessRange n).card : ℝ) ≤ inputScale R.input := by
    have hsub : guessRange n ⊆ Finset.range (mixerSize n + 1) := by
      intro x hx
      have hh := (Finset.mem_Icc.mp hx).2
      exact Finset.mem_range.mpr (by omega)
    have hh : (guessRange n).card ≤ mixerSize n + 1 :=
      (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    have hhR : ((guessRange n).card : ℝ) ≤ (mixerSize n : ℝ) + 1 := by exact_mod_cast hh
    exact hhR.trans R.mixerSize_add_one_le_scale
  have hp0 : 0 < (guessRange n).card := Finset.card_pos.mpr (guessRange_nonempty n)
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem goodPartitions_probability {z : Layout n} (hz : R.GoodLayout z)
    (g : Guesses n) (hg : R.GoodGuesses z g) (hn : 2200 ≤ n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hu : 8 ≤ inputScale R.input) :
    1 / (inputScale R.input : ℝ) ^ 25 ≤ finiteUniformProbability (R.GoodPartitions z g) := by
  have hi (i : Fin 3) : 1 / (2 * (inputScale R.input : ℝ) ^ (3 * blockCount i)) ≤
      finiteUniformProbability (fun f : R.Partition z i =>
        (2 : ℝ) ^ R.lowExponent z i / (inputScale R.input : ℝ) ^ 14 ≤
          (survivingWeights (R.signedWeights z)
            (representativeMask (R.signedWeights z) (R.selectedHalves z i) (g i).val)
            (fun r => representativePrescriptions
              (representativeMask_spec (R.signedWeights z) (R.selectedHalves z i) (g i).val r).1
              (R.selectedHalves_subset z i)
              (representativeBlockProfile (blockCount i) (blockHalf n i) (g i).val) f)).card) := by
    have hs := R.chosenSize_spec hz hn hden i
    change _ ∧ _ ∧ _ at hs
    rw [← hg i] at hs
    have hk : (g i).val ≤ blockCount i * blockHalf n i := by
      rw [R.blockCount_half, ← R.selectedHalves_card hz i]
      omega
    have hhalf : ((blockCount i * blockHalf n i : ℕ) : ℝ) + 1 ≤ inputScale R.input := by
      rw [R.blockCount_half]
      apply le_trans _ R.mixerSize_add_one_le_scale
      have h := R.orderedMixers_card z i
      rw [orderedMixers, rawMixers, permuteSubset_card, R.card] at h
      exact_mod_cast (by omega : R.halfSize + 1 ≤ mixerSize n + 1)
    apply distinct_sum_representatives_survival (R.signedWeights z) (R.selectedHalves z i)
      (R.orderedMixers z i) (R.selectedHalves_subset z i) (blockCount i) (blockHalf n i)
      (g i).val (by fin_cases i <;> simp [blockCount]) hk
      ((R.selectedHalves_card hz i).trans (R.blockCount_half i).symm)
      (by rw [R.orderedMixers_card, R.blockCount_half])
      (R.lowExponent z i) (inputScale R.input) (by exact_mod_cast (by omega : 2 ≤ inputScale R.input))
      hhalf (by simpa only [orderedMixers, rawMixers, permuteSubset_card, R.card] using
        R.mixerSize_add_one_le_scale)
    simpa only [R.selectedHalves_card hz i, R.blockCount_half] using hs.2.2
  exact three_representative_families_probability (fun i => R.Partition z i)
    (fun i f => (2 : ℝ) ^ R.lowExponent z i / (inputScale R.input : ℝ) ^ 14 ≤
      (survivingWeights (R.signedWeights z)
        (representativeMask (R.signedWeights z) (R.selectedHalves z i) (g i).val)
        (fun r => representativePrescriptions
          (representativeMask_spec (R.signedWeights z) (R.selectedHalves z i) (g i).val r).1
          (R.selectedHalves_subset z i)
          (representativeBlockProfile (blockCount i) (blockHalf n i) (g i).val) f)).card)
    (inputScale R.input) (by exact_mod_cast hu) (hi 0) (hi 1) (hi 2)

theorem retainedWeight_bound (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (i : Fin 3) {x : ℤ} (hx : x ∈ R.retainedWeights z g f i) :
    x.natAbs ≤ n * 2 ^ inputBits R.input := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
  exact signed_weight_natAbs_le R.input (R.signMask z) _

theorem goodPrime_probability (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hf : R.GoodPartitions z g f) (hu : 256 ≤ inputScale R.input) :
    1 / 2 ≤ finiteUniformProbability (R.GoodPrime z g f) := by
  have h := nested_simultaneous_fraction_probability hu
    (R.factorExponents_le_scale z 0) (R.factorExponents_le_scale z 1)
    (R.factorExponents_le_scale z 2) (R.retainedWeights z g f) (R.lowExponent z)
    (fun i => by rw [R.prefixExponent_eq_floor]; exact Nat.floor_le (R.lowExponent_nonneg z i))
    (fun i => by rw [R.prefixExponent_eq_floor]; exact Nat.lt_floor_add_one _)
    hf (fun i x hx y hy => relevant_difference_bits R.input
      ((R.retainedWeight_bound z g f i hx).trans (by gcongr; omega))
      ((R.retainedWeight_bound z g f i hy).trans (by gcongr; omega)))
  apply le_trans _ h
  have huR : (256 : ℝ) ≤ inputScale R.input := by exact_mod_cast hu
  have hd : 3 / (inputScale R.input : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < inputScale R.input)).mpr
    linarith
  linarith

def GoodGuessHistory (h : R.GuessHistory) : Prop :=
  R.GoodLayout h.1 ∧ R.GoodGuesses h.1 h.2

def GoodPartitionHistory (h : R.PartitionHistory) : Prop :=
  R.GoodGuessHistory h.1 ∧ R.GoodPartitions h.1.1 h.1.2 h.2

def GoodPrimeHistory (h : R.PrimeHistory) : Prop :=
  R.GoodPartitionHistory h.1 ∧ R.GoodPrime h.1.1.1 h.1.1.2 h.1.2 h.2

/-- The offsets may depend on the layout, guesses, and subblock partition;
they are fixed before the common prime tuple and its target residues. -/
structure ResidueOffsets where
  parent : R.PartitionHistory → ℤ
  left : R.PartitionHistory → ℤ → ℤ
  right : R.PartitionHistory → ℤ → ℤ

def ResidueSuccess (O : R.ResidueOffsets) (h : R.PrimeHistory) (r : R.Residues h.2) : Prop :=
  adaptiveResidueHits (prefixModulus_pos h.2 0) (prefixModulus_pos h.2 1)
    (prefixModulus_pos h.2 2)
    (R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 0)
    (R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 1)
    (R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 2)
    (O.parent h.1) (O.left h.1) (O.right h.1) r

def Successful (O : R.ResidueOffsets) (h : R.TrialHistory) : Prop :=
  R.GoodPrimeHistory h.1 ∧ R.ResidueSuccess O h.1 h.2

theorem residueSuccess_probability (O : R.ResidueOffsets) (h : R.PrimeHistory)
    (hh : R.GoodPrimeHistory h) :
    1 / (inputScale R.input : ℝ) ^ 48 ≤ finiteUniformProbability (R.ResidueSuccess O h) :=
  adaptiveResidueHits_probability (prefixModulus_pos h.2 0) (prefixModulus_pos h.2 1)
    (prefixModulus_pos h.2 2)
    (R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 0)
    (R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 1)
    (R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 2)
    (O.parent h.1) (O.left h.1) (O.right h.1) (inputScale R.input)
    (by exact_mod_cast (show 0 < inputScale R.input by
      have := inputBits_pos R.input
      unfold inputScale
      omega))
    (hh.2 0) (hh.2 1) (hh.2 2)

/-- All probability factors are proved for the concrete successive draws.
No success probability is assumed as an interface. -/
theorem successful_probability (O : R.ResidueOffsets)
    (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize)) :
    1 / (inputScale R.input : ℝ) ^ 100 ≤ R.trialLaw.probability (R.Successful O) := by
  have hu : 256 ≤ inputScale R.input := by unfold inputScale; omega
  have huR : (256 : ℝ) ≤ inputScale R.input := by exact_mod_cast hu
  have h1 : (1 / (16 * (inputScale R.input : ℝ) ^ 3)) *
      (1 / (inputScale R.input : ℝ) ^ 3) ≤ R.guessLaw.probability R.GoodGuessHistory := by
    apply FiniteLaw.bind_good_lower R.layoutLaw (fun _ => Guesses n)
      (fun _ => FiniteLaw.uniform) R.GoodLayout R.GoodGuesses (by positivity)
      (R.goodLayout_probability hn hmean)
    intro z hz
    rw [FiniteLaw.uniform_probability]
    exact R.goodGuesses_probability hz (by omega) hden
  have h2 : ((1 / (16 * (inputScale R.input : ℝ) ^ 3)) *
      (1 / (inputScale R.input : ℝ) ^ 3)) * (1 / (inputScale R.input : ℝ) ^ 25) ≤
      R.partitionLaw.probability R.GoodPartitionHistory := by
    apply FiniteLaw.bind_good_lower R.guessLaw (fun h => R.Partitions h.1)
      (fun _ => FiniteLaw.uniform) R.GoodGuessHistory
      (fun h f => R.GoodPartitions h.1 h.2 f) (by positivity) h1
    intro h hh
    rw [FiniteLaw.uniform_probability]
    exact R.goodPartitions_probability hh.1 h.2 hh.2 (by omega) hden (by omega)
  have h3 : (((1 / (16 * (inputScale R.input : ℝ) ^ 3)) *
      (1 / (inputScale R.input : ℝ) ^ 3)) * (1 / (inputScale R.input : ℝ) ^ 25)) * (1 / 2) ≤
      R.primeLaw.probability R.GoodPrimeHistory := by
    apply FiniteLaw.bind_good_lower R.partitionLaw (fun h => R.PrimeSpace h.1.1)
      (fun _ => FiniteLaw.uniform) R.GoodPartitionHistory
      (fun h p => R.GoodPrime h.1.1 h.1.2 h.2 p) (by norm_num) h2
    intro h hh
    rw [FiniteLaw.uniform_probability]
    exact R.goodPrime_probability h.1.1 h.1.2 h.2 hh.2 hu
  have h4 : ((((1 / (16 * (inputScale R.input : ℝ) ^ 3)) *
      (1 / (inputScale R.input : ℝ) ^ 3)) * (1 / (inputScale R.input : ℝ) ^ 25)) * (1 / 2)) *
      (1 / (inputScale R.input : ℝ) ^ 48) ≤ R.trialLaw.probability (R.Successful O) := by
    apply FiniteLaw.bind_good_lower R.primeLaw (fun h => R.Residues h.2)
      (fun _ => FiniteLaw.uniform) R.GoodPrimeHistory (R.ResidueSuccess O) (by positivity) h3
    intro h hh
    rw [FiniteLaw.uniform_probability]
    exact R.residueSuccess_probability O h hh
  apply le_trans _ h4
  have hpow : 32 ≤ (inputScale R.input : ℝ) ^ 21 := by
    have hbig : (2 : ℝ) ^ 21 ≤ (inputScale R.input : ℝ) ^ 21 := by gcongr; linarith
    norm_num at hbig ⊢
    linarith
  have hdenom : 32 * (inputScale R.input : ℝ) ^ 79 ≤
      (inputScale R.input : ℝ) ^ 100 := by
    calc
      _ ≤ (inputScale R.input : ℝ) ^ 21 * (inputScale R.input : ℝ) ^ 79 :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by rw [← pow_add]
  calc
    _ ≤ 1 / (32 * (inputScale R.input : ℝ) ^ 79) :=
      one_div_le_one_div_of_le (by positivity) hdenom
    _ = _ := by field_simp; ring

theorem mem_retainedWeights (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (i : Fin 3) (x : ℤ) : x ∈ R.retainedWeights z g f i ↔
      ∃ r : ↥(sumsAtSize (R.signedWeights z) (R.selectedHalves z i) (g i).val),
        R.Prescribed z g f i r ∧
        weight (R.signedWeights z)
          (representativeMask (R.signedWeights z) (R.selectedHalves z i) (g i).val r) = x := by
  simp only [retainedWeights, survivingWeights, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The lookup is a deterministic analysis choice on distinct retained weights. -/
def retainedMask (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (i : Fin 3) (x : ℤ) : Finset (Fin n) :=
  if h : x ∈ R.retainedWeights z g f i then
    representativeMask (R.signedWeights z) (R.selectedHalves z i) (g i).val
      ((R.mem_retainedWeights z g f i x).mp h).choose
  else ∅

theorem retainedMask_spec (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (i : Fin 3) {x : ℤ} (hx : x ∈ R.retainedWeights z g f i) :
    R.retainedMask z g f i x ⊆ R.selectedHalves z i ∧
    (R.retainedMask z g f i x).card = (g i).val ∧
    weight (R.signedWeights z) (R.retainedMask z g f i x) = x ∧
    (∃ hsub : R.retainedMask z g f i x ⊆ R.selectedHalves z i,
      representativePrescriptions hsub (R.selectedHalves_subset z i)
        (representativeBlockProfile (blockCount i) (blockHalf n i) (g i).val) (f i)) := by
  let he := (R.mem_retainedWeights z g f i x).mp hx
  have hr := representativeMask_spec (R.signedWeights z) (R.selectedHalves z i)
    (g i).val he.choose
  have hm : R.retainedMask z g f i x =
      representativeMask (R.signedWeights z) (R.selectedHalves z i) (g i).val he.choose := by
    simp only [retainedMask, hx, ↓reduceDIte]
  rw [hm]
  exact ⟨hr.1, hr.2.1, he.choose_spec.2, hr.1, he.choose_spec.1⟩

def chosenWeights (O : R.ResidueOffsets) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Fin 3 → ℤ :=
  let X := R.retainedWeights h.1.1.1 h.1.1.2 h.1.2
  let x0 := chosenTopRepresentative (prefixModulus_pos h.2 0) (X 0) (O.parent h.1) r.1
  ![x0,
    chosenTopRepresentative (prefixModulus_pos h.2 1) (X 1) (O.left h.1 x0) r.2.1,
    chosenTopRepresentative (prefixModulus_pos h.2 2) (X 2) (O.right h.1 x0) r.2.2]

def chosenMasks (O : R.ResidueOffsets) (h : R.PrimeHistory)
    (r : R.Residues h.2) (i : Fin 3) : Finset (Fin n) :=
  R.retainedMask h.1.1.1 h.1.1.2 h.1.2 i (R.chosenWeights O h r i)

/-- In particular, the top choice is fixed before either child residue. -/
theorem chosenTop_independent_children (O : R.ResidueOffsets) (h : R.PrimeHistory)
    (r s : R.Residues h.2) (hrs : r.1 = s.1) :
    R.chosenMasks O h r 0 = R.chosenMasks O h s 0 := by
  simp only [chosenMasks, chosenWeights, Matrix.cons_val_zero, hrs]

theorem chosenWeights_mem (O : R.ResidueOffsets) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess O h r) (i : Fin 3) :
    R.chosenWeights O h r i ∈ R.retainedWeights h.1.1.1 h.1.1.2 h.1.2 i := by
  have h0 := (chosenTopRepresentative_spec (prefixModulus_pos h.2 0) _ _ _ hr.1).1
  have h1 := (chosenTopRepresentative_spec (prefixModulus_pos h.2 1) _ _ _ hr.2.1).1
  have h2 := (chosenTopRepresentative_spec (prefixModulus_pos h.2 2) _ _ _ hr.2.2).1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem chosenMasks_spec (O : R.ResidueOffsets) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess O h r) (i : Fin 3) :
    R.chosenMasks O h r i ⊆ R.selectedHalves h.1.1.1 i ∧
    (R.chosenMasks O h r i).card = (h.1.1.2 i).val ∧
    weight (R.signedWeights h.1.1.1) (R.chosenMasks O h r i) = R.chosenWeights O h r i ∧
    (∃ hsub : R.chosenMasks O h r i ⊆ R.selectedHalves h.1.1.1 i,
      representativePrescriptions hsub (R.selectedHalves_subset h.1.1.1 i)
        (representativeBlockProfile (blockCount i) (blockHalf n i) (h.1.1.2 i).val)
        (h.1.2 i)) :=
  R.retainedMask_spec _ _ _ i (R.chosenWeights_mem O hr i)

theorem successful_spread (O : R.ResidueOffsets) {h : R.TrialHistory}
    (hh : R.Successful O h) :
    mixerSpreadTest (R.signedWeights h.1.1.1.1)
      (R.orderedMixers h.1.1.1.1) n := by
  intro i j
  have hz : R.GoodLayout h.1.1.1.1 := hh.1.1.1.1
  have hs := hz.2.2 (R.mixerOrder h.1.1.1.1 i) (R.mixerOrder h.1.1.1.1 j)
  simpa only [signedWeights, distinctSumCount_flip, orderedMixers, rawMixers] using hs

theorem chosenWeights_compatible (O : R.ResidueOffsets) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess O h r) :
    let x := R.chosenWeights O h r
    let t := R.signedTarget h.1.1.1
    x 0 + O.parent h.1 ≡ (r.1.val : ℤ) [ZMOD (prefixModulus h.2.val 0 : ℤ)] ∧
    t - (x 0 + O.parent h.1) ≡ t - (r.1.val : ℤ) [ZMOD (prefixModulus h.2.val 0 : ℤ)] ∧
    x 1 + O.left h.1 (x 0) ≡ (r.2.1.val : ℤ) [ZMOD (prefixModulus h.2.val 1 : ℤ)] ∧
    (x 0 + O.parent h.1) - (x 1 + O.left h.1 (x 0)) ≡
      (r.1.val : ℤ) - r.2.1.val [ZMOD (prefixModulus h.2.val 1 : ℤ)] ∧
    x 2 + O.right h.1 (x 0) ≡ (r.2.2.val : ℤ) [ZMOD (prefixModulus h.2.val 2 : ℤ)] ∧
    (t - (x 0 + O.parent h.1)) - (x 2 + O.right h.1 (x 0)) ≡
      (t - (r.1.val : ℤ)) - r.2.2.val [ZMOD (prefixModulus h.2.val 2 : ℤ)] := by
  have h0 := (chosenTopRepresentative_spec (prefixModulus_pos h.2 0) _ _ _ hr.1).2
  have h1 := (chosenTopRepresentative_spec (prefixModulus_pos h.2 1) _ _ _ hr.2.1).2
  have h2 := (chosenTopRepresentative_spec (prefixModulus_pos h.2 2) _ _ _ hr.2.2).2
  have hp0 := normalizedResidue_eq_modEq (prefixModulus_pos h.2 0) _ _ h0
  have hp1 := normalizedResidue_eq_modEq (prefixModulus_pos h.2 1) _ _ h1
  have hp2 := normalizedResidue_eq_modEq (prefixModulus_pos h.2 2) _ _ h2
  have ht : R.signedTarget h.1.1.1 -
      (R.chosenWeights O h r 0 + O.parent h.1) ≡ R.signedTarget h.1.1.1 - r.1.val
      [ZMOD (prefixModulus h.2.val 0 : ℤ)] := by
    simpa only [chosenWeights, Matrix.cons_val_zero, sub_eq_add_neg] using
      hp0.neg.add_left (R.signedTarget h.1.1.1)
  refine ⟨hp0, ht, hp1, ?_, hp2, ?_⟩
  · exact (hp0.of_dvd (by exact_mod_cast (prefixModulus_nested h.2.val).1)).sub hp1
  · exact (ht.of_dvd (by exact_mod_cast (prefixModulus_nested h.2.val).2)).sub hp2

/-- Later randomness may depend on the retained layout, but not on an
analysis witness. Its conditional joint law remains the prescribed product. -/
theorem future_conditional_product
    (Q F : R.TrialHistory → Type*) [∀ h, Fintype (Q h)] [∀ h, Fintype (F h)]
    [∀ h, Nonempty (Q h)] [∀ h, Nonempty (F h)]
    (A : ∀ h, Q h → Prop) (B : ∀ h, F h → Prop)
    (h : R.TrialHistory) (hh : R.trialLaw.mass h ≠ 0) :
    (R.trialLaw.bind (fun x => Q x × F x) (fun _ => FiniteLaw.uniform)).probability
        (fun z => z.1 = h ∧ A z.1 z.2.1 ∧ B z.1 z.2.2) /
      R.trialLaw.probability (fun x => x = h) =
      finiteUniformProbability (A h) * finiteUniformProbability (B h) := by
  have he := FiniteLaw.bind_conditional_probability R.trialLaw
    (fun x => Q x × F x) (fun _ => FiniteLaw.uniform)
    (fun x q => A x q.1 ∧ B x q.2) h hh
  rw [FiniteLaw.uniform_probability, finiteUniformProbability_product_and] at he
  exact he

end RepresentationSetup

theorem eventually_representation_half_gap :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
        (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (polynomial_absorption 2 (by norm_num : (0 : ℝ) < 1 / 1500))
  filter_upwards [Filter.eventually_ge_atTop (100 * (max N 3))] with n hn
  have hdiv : max N 3 ≤ 3 * n / 100 := by omega
  have hh : mixerSize n / 2 = 4 * (3 * n / 100) := by
    simp only [mixerSize]
    omega
  have hsN : N ≤ mixerSize n / 2 := by omega
  have hs3 : 3 ≤ mixerSize n / 2 := by omega
  have hs3R : (3 : ℝ) ≤ (mixerSize n / 2 : ℕ) := by exact_mod_cast hs3
  apply lt_of_lt_of_le _ (hN _ hsN)
  nlinarith

/-- A uniform threshold works for every input and every fixed solution;
the logarithmic representative loss is discharged rather than assumed. -/
theorem eventually_representation_survival :
    ∃ N : ℕ, ∀ n ≥ N, ∀ R : RepresentationSetup n,
      meanDeficiency R.originalWeights Finset.univ R.halfSize <
        (153 / 20000 : ℝ) * n →
      ∀ O : R.ResidueOffsets,
        1 / (inputScale R.input : ℝ) ^ 100 ≤ R.trialLaw.probability (R.Successful O) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp eventually_representation_half_gap
  refine ⟨max N 180000000, ?_⟩
  intro n hn R hmean O
  exact R.successful_probability O (by omega) hmean (hN n (by omega))

end LowSpaceSubsetSum

end

end OAI
