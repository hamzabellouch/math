import OAI.Combinatorics.EditApproximation.Numerics.Numerics
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset

/-- Little-endian encoding of a finite Boolean word. -/
def binaryWord : (B : ℕ) → (Fin B → Bool) → Fin (2 ^ B)
  | 0, _ => ⟨0, by norm_num⟩
  | B + 1, bits =>
    ⟨(if bits 0 then 1 else 0) + 2 * (binaryWord B (fun i => bits i.succ)).val, by
      have hword := (binaryWord B (fun i => bits i.succ)).isLt
      rw [pow_succ]
      split_ifs <;> omega⟩

theorem binaryWord_injective (B : ℕ) : Function.Injective (binaryWord B) := by
  induction B with
  | zero => intro bits other _; funext i; exact Fin.elim0 i
  | succ B ih =>
    intro bits other heq
    have hvalue := congrArg Fin.val heq
    dsimp only [binaryWord] at hvalue
    have hhead : bits 0 = other 0 := by
      cases hb : bits 0 <;> cases ho : other 0 <;> simp only [hb, ho, Bool.false_eq_true,
        ↓reduceIte] at hvalue ⊢ <;> omega
    have htail : binaryWord B (fun i => bits i.succ) = binaryWord B (fun i => other i.succ) := by
      apply Fin.ext
      rw [hhead] at hvalue
      omega
    have htailEq := ih htail
    funext i
    exact Fin.cases hhead (fun j => congr_fun htailEq j) i

theorem binaryWord_bijective (B : ℕ) : Function.Bijective (binaryWord B) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨binaryWord_injective B, by simp⟩

/-- A bijection carries the uniform finite law to the uniform finite law. -/
theorem uniform_map_of_bijective {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  classical
  ext b
  obtain ⟨a, rfl⟩ := hf.2 b
  rw [PMF.map_apply, tsum_eq_single a]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_of_bijective hf]
  · intro other hother
    rw [ite_eq_right]
    exact fun heq => hother (hf.1 heq.symm)

/-- Independent fair Boolean words encode a uniform power-of-two range. -/
theorem binaryWord_uniform (B : ℕ) :
    (PMF.uniformOfFintype (Fin B → Bool)).map (binaryWord B) =
      PMF.uniformOfFintype (Fin (2 ^ B)) := by
  exact uniform_map_of_bijective _ (binaryWord_bijective B)

/-- Number of fair bits per rejection trial. -/


theorem rejectionWord_range (N : ℕ) (hN : 0 < N) :
    N ≤ 2 ^ rejectionBitCount N ∧ 2 ^ rejectionBitCount N < 2 * N := by
  constructor
  · exact Nat.le_pow_clog (by norm_num) N
  · by_cases hNone : N = 1
    · subst N
      norm_num [rejectionBitCount]
    · have hN1 : 1 < N := by omega
      have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hN1
      have hB := Nat.clog_pos (by norm_num : 1 < 2) hN1
      have hpow : 2 ^ rejectionBitCount N = 2 ^ (Nat.clog 2 N).pred * 2 := by
        rw [rejectionBitCount, ← pow_succ]
        congr 1
        exact (Nat.succ_pred_eq_of_pos hB).symm
      rw [hpow]
      omega

/-- A trial accepts exactly the words lying in the requested range. -/
def rejectionTrial (N R : ℕ) (word : Fin R) : Option (Fin N) :=
  if h : word.val < N then some ⟨word.val, h⟩ else none

/-- Executable finite prefix of the rejection loop. Each failed trial
is discarded before the next trial is examined. -/
def rejectionPrefix (N R : ℕ) : List (Fin R) → Option (Fin N)
  | [] => none
  | word :: words => match rejectionTrial N R word with
    | some accepted => some accepted
    | none => rejectionPrefix N R words

theorem rejectionTrial_none_iff (N R : ℕ) (word : Fin R) :
    rejectionTrial N R word = none ↔ N ≤ word.val := by
  simp [rejectionTrial]

theorem rejectionTrial_some_iff (N R : ℕ) (word : Fin R) (accepted : Fin N) :
    rejectionTrial N R word = some accepted ↔ word.val = accepted.val := by
  unfold rejectionTrial
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
  · simp only [false_iff]
    exact fun heq => h (heq ▸ accepted.isLt)

theorem rejectionPrefix_none_iff (N R : ℕ) (words : List (Fin R)) :
    rejectionPrefix N R words = none ↔ ∀ word ∈ words, N ≤ word.val := by
  induction words with
  | nil => simp [rejectionPrefix]
  | cons word words ih =>
    simp only [rejectionPrefix]
    cases htrial : rejectionTrial N R word with
    | none => simp [ih, (rejectionTrial_none_iff N R word).mp htrial]
    | some accepted =>
      have hlt : word.val < N := by
        rw [(rejectionTrial_some_iff N R word accepted).mp htrial]
        exact accepted.isLt
      simp [show ¬N ≤ word.val by omega]

theorem rejectionPrefix_first_success (N R : ℕ) (words : List (Fin R))
    (last : Fin R) (accepted : Fin N)
    (hfailed : ∀ word ∈ words, N ≤ word.val) (hlast : last.val = accepted.val) :
    rejectionPrefix N R (words ++ [last]) = some accepted := by
  induction words with
  | nil =>
    simp only [List.nil_append, rejectionPrefix]
    rw [(rejectionTrial_some_iff N R last accepted).mpr hlast]
  | cons word words ih =>
    have hword := hfailed word (by simp)
    have hwords : ∀ next ∈ words, N ≤ next.val := fun next hnext => hfailed next (by simp [hnext])
    simp only [List.cons_append, rejectionPrefix]
    rw [(rejectionTrial_none_iff N R word).mpr hword]
    exact ih hwords

/-- Finite traces with `n` failed words followed by the specified
accepted integer. -/
def firstSuccessEvent (N R n : ℕ) (accepted : Fin N) :
    Set ((Fin n → Fin R) × Fin R) :=
  {samples | (∀ j, N ≤ (samples.1 j).val) ∧ samples.2.val = accepted.val}

/-- Each failed word is represented uniquely by its offset above `N`;
the final accepted word is fixed. -/
def firstSuccessEquiv (N R n : ℕ) (hNR : N ≤ R) (accepted : Fin N) :
    firstSuccessEvent N R n accepted ≃ (Fin n → Fin (R - N)) where
  toFun samples j := ⟨(samples.val.1 j).val - N, by
    have hlt := (samples.val.1 j).isLt
    have hge := samples.property.1 j
    omega⟩
  invFun failed := ⟨(fun j => ⟨N + (failed j).val, by
    have hlt := (failed j).isLt
    omega⟩, ⟨accepted.val, accepted.isLt.trans_le hNR⟩), by
    constructor
    · intro j
      simp only
      omega
    · rfl⟩
  left_inv samples := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      apply Fin.ext
      simp only
      have hge := samples.property.1 j
      omega
    · apply Fin.ext
      exact samples.property.2.symm
  right_inv failed := by
    funext j
    apply Fin.ext
    simp

/-- First-success events are actual terminating executions of the
finite-prefix rejection program. -/
theorem firstSuccessEvent_runs (N R n : ℕ) (accepted : Fin N)
    (samples : (Fin n → Fin R) × Fin R) (hsamples : samples ∈ firstSuccessEvent N R n accepted) :
    rejectionPrefix N R (List.ofFn samples.1 ++ [samples.2]) = some accepted := by
  apply rejectionPrefix_first_success N R _ _ accepted _ hsamples.2
  intro word hword
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hword
  exact hsamples.1 j

/-- Exact finite counting probability for `n` failures and then a
specified accepted value, under independent uniform trial words. -/
theorem firstSuccessEvent_probability (N R n : ℕ) (hN : 0 < N) (hNR : N ≤ R)
    (accepted : Fin N) :
    let : NeZero R := ⟨by omega⟩
    ((PMF.uniformOfFintype ((Fin n → Fin R) × Fin R)).toMeasure).real
      (firstSuccessEvent N R n accepted) = ((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R) := by
  let : NeZero R := ⟨by omega⟩
  classical
  have hcard : Fintype.card (firstSuccessEvent N R n accepted) = (R - N) ^ n := by
    rw [Fintype.card_congr (firstSuccessEquiv N R n hNR accepted)]
    simp
  dsimp only
  rw [MeasureTheory.measureReal_def, PMF.toMeasure_uniformOfFintype_apply (firstSuccessEvent N R n accepted) (by measurability)]
  rw [hcard]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_natCast, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul]

/-- Rejection probability per trial. -/
noncomputable def rejectionFailureProbability (N R : ℕ) : ℝ := ((R - N : ℕ) : ℝ) / R

theorem rejectionFailureProbability_range (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    0 ≤ rejectionFailureProbability N R ∧ rejectionFailureProbability N R < 1 := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  constructor
  · unfold rejectionFailureProbability
    positivity
  · unfold rejectionFailureProbability
    rw [div_lt_one hR, Nat.cast_sub hNR]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    linarith

/-- The sum over all first-success times is exactly uniform on the
requested range. This also establishes total terminating mass one. -/
theorem rejection_exact_output_mass (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    HasSum (fun n : ℕ => ((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R)) (1 / (N : ℝ)) := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := rejectionFailureProbability_range N R hN hNR
  have hseries := (hasSum_geometric_of_lt_one hq.1 hq.2).div_const (R : ℝ)
  have hterm (n : ℕ) : rejectionFailureProbability N R ^ n / R =
      ((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R) := by
    simp only [rejectionFailureProbability, div_pow]
    ring
  have hsum : (1 - rejectionFailureProbability N R)⁻¹ / R = 1 / (N : ℝ) := by
    unfold rejectionFailureProbability
    rw [Nat.cast_sub hNR]
    field_simp [hR.ne', hNreal.ne']
    ring
  simpa only [hterm, hsum] using hseries

/-- The expected rejection-loop trial count is the sum of its failure
tails, namely `R/N`. -/
theorem rejection_expected_trials (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    HasSum (fun n : ℕ => rejectionFailureProbability N R ^ n) ((R : ℝ) / N) := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := rejectionFailureProbability_range N R hN hNR
  have hsum : (1 - rejectionFailureProbability N R)⁻¹ = (R : ℝ) / N := by
    unfold rejectionFailureProbability
    rw [Nat.cast_sub hNR]
    field_simp [hR.ne', hNreal.ne']
    ring
  simpa only [hsum] using hasSum_geometric_of_lt_one hq.1 hq.2

theorem rejection_fair_bits_expected_trials_lt_two (N : ℕ) (hN : 0 < N) :
    (∑' n : ℕ, rejectionFailureProbability N (2 ^ rejectionBitCount N) ^ n) < 2 := by
  have hrange := rejectionWord_range N hN
  rw [(rejection_expected_trials N _ hN hrange.1).tsum_eq]
  apply (div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  exact_mod_cast hrange.2

/-- The actual first-success trace law has expected trial count `R/N`;
this identifies the tail-sum calculation with the terminating executions. -/
theorem rejection_first_success_expected_trials (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * N *
      (((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R))) ((R : ℝ) / N) := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := rejectionFailureProbability_range N R hN hNR
  have hnorm : ‖rejectionFailureProbability N R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq.1]
    exact hq.2
  have hseries := ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hq.1 hq.2)).mul_right ((N : ℝ) / R)
  have hterm (n : ℕ) :
      ((n : ℝ) * rejectionFailureProbability N R ^ n + rejectionFailureProbability N R ^ n) *
          ((N : ℝ) / R) =
        ((n : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R)) := by
    simp only [rejectionFailureProbability, div_pow]
    ring
  have hratio : 1 - rejectionFailureProbability N R = (N : ℝ) / R := by
    unfold rejectionFailureProbability
    rw [Nat.cast_sub hNR]
    field_simp
    ring
  have hsum : (rejectionFailureProbability N R / (1 - rejectionFailureProbability N R) ^ 2 +
        (1 - rejectionFailureProbability N R)⁻¹) * ((N : ℝ) / R) = (R : ℝ) / N := by
    rw [hratio]
    have hqeq : rejectionFailureProbability N R = 1 - (N : ℝ) / R := by linarith [hratio]
    rw [hqeq]
    field_simp [hR.ne', hNreal.ne']
    ring
  simpa only [hterm, hsum] using hseries

/-- A streaming rejection sampler only retains its current accepted
value and the current bounded-width random word. -/
def rejectionTransition (N R : ℕ) (state : Option (Fin N)) (word : Fin R) : Option (Fin N) :=
  match state with
  | none => rejectionTrial N R word
  | some accepted => some accepted

theorem rejectionTransition_absorbs (N R : ℕ) (accepted : Fin N) (word : Fin R) :
    rejectionTransition N R (some accepted) word = some accepted := rfl

/-- The sampler state space is independent of the number of failures. -/
theorem rejection_fixed_state_space (N R : ℕ) :
    Fintype.card (Option (Fin N)) = N + 1 ∧ Fintype.card (Fin R) = R := by
  simp

/-- Summing the first-success trace probabilities gives exactly the
probability of each value in the uniform target distribution. -/
theorem rejection_output_is_uniform (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R)
    (accepted : Fin N) :
    let : NeZero N := ⟨Nat.ne_of_gt hN⟩
    (∑' n : ℕ, ((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R)) =
      (PMF.uniformOfFintype (Fin N) accepted).toReal := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  rw [(rejection_exact_output_mass N R hN hNR).tsum_eq]
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, one_div]

/-- Total mass of terminating rejection executions is one. -/
theorem rejection_terminating_mass (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    (∑ _ : Fin N, ∑' n : ℕ, ((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R)) = 1 := by
  simp only [(rejection_exact_output_mass N R hN hNR).tsum_eq, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

/-- The finite fair-word law factors into the independent fair-bit laws. -/
theorem fair_bit_word_probability (B : ℕ) (bits : Fin B → Bool) :
    PMF.uniformOfFintype (Fin B → Bool) bits =
      ∏ i : Fin B, PMF.uniformOfFintype Bool (bits i) := by
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

theorem rejection_fair_bits_failure_lt_half (N : ℕ) (hN : 0 < N) :
    rejectionFailureProbability N (2 ^ rejectionBitCount N) < 1 / 2 := by
  have hrange := rejectionWord_range N hN
  have hR : (0 : ℝ) < (2 ^ rejectionBitCount N : ℕ) := by positivity
  unfold rejectionFailureProbability
  apply (div_lt_iff₀ hR).mpr
  rw [Nat.cast_sub hrange.1]
  have hRbound : ((2 ^ rejectionBitCount N : ℕ) : ℝ) < 2 * N := by exact_mod_cast hrange.2
  linarith

theorem optimizerTriangularMass_monotone : Monotone optimizerTriangularMass := by
  intro a b hab
  have hproduct := Nat.mul_le_mul hab (Nat.add_le_add_right hab 1)
  rw [← optimizerTriangularMass_twice a, ← optimizerTriangularMass_twice b] at hproduct
  omega

theorem optimizerTriangularMass_positive (K : ℕ) (hK : 0 < K) :
    0 < optimizerTriangularMass K := by
  have hproduct : 0 < K * (K + 1) := Nat.mul_pos hK (by omega)
  rw [← optimizerTriangularMass_twice K] at hproduct
  omega

/- Executable triangular-block lookup. Its finite linear search also
has polynomial cost in the prescribed number of optimizer steps. -/


/-- The lookup assigns precisely the `j+1` integers in block `j`. -/
theorem triangularChoice_fiber (K : ℕ) (integer : Fin (optimizerTriangularMass K))
    (j : ℕ) (hj : j < K) :
    (triangularChoice K integer).val = j ↔
      optimizerTriangularMass j ≤ integer.val ∧ integer.val < optimizerTriangularMass (j + 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
    simp only [triangularChoice]
    split_ifs with hprevious
    · by_cases hjK : j < K
      · exact ih ⟨integer.val, hprevious⟩ hjK
      · have hjEq : j = K := by omega
        subst j
        have hchosen := (triangularChoice K ⟨integer.val, hprevious⟩).isLt
        simp only [Fin.val_castSucc]
        constructor
        · intro heq
          omega
        · intro hblock
          omega
    · change K = j ↔ _
      by_cases hjEq : j = K
      · subst j
        exact ⟨fun _ => ⟨by omega, integer.isLt⟩, fun _ => rfl⟩
      · have hjK : j + 1 ≤ K := by omega
        have hupper := optimizerTriangularMass_monotone hjK
        constructor
        · intro heq
          omega
        · intro hblock
          omega

/-- Each triangular lookup fiber is exactly a finite interval of the
claimed integer length. -/
def triangularChoiceFiberEquiv (K j : ℕ) (hj : j < K) :
    {integer : Fin (optimizerTriangularMass K) // (triangularChoice K integer).val = j} ≃ Fin (j + 1) where
  toFun integer := ⟨integer.val.val - optimizerTriangularMass j, by
    have hblock := (triangularChoice_fiber K integer.val j hj).mp integer.property
    rw [optimizerTriangularMass_succ] at hblock
    omega⟩
  invFun offset := ⟨⟨optimizerTriangularMass j + offset.val, by
    have hupper := optimizerTriangularMass_monotone (show j + 1 ≤ K by omega)
    rw [optimizerTriangularMass_succ] at hupper
    have hoffset := offset.isLt
    omega⟩, by
      apply (triangularChoice_fiber K _ j hj).mpr
      constructor
      · simp only
        omega
      · simp only
        rw [optimizerTriangularMass_succ]
        have hoffset := offset.isLt
        omega⟩
  left_inv integer := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have hblock := (triangularChoice_fiber K integer.val j hj).mp integer.property
    omega
  right_inv offset := by
    apply Fin.ext
    simp

theorem triangularChoice_fiber_card (K : ℕ) (j : Fin K) :
    Fintype.card {integer : Fin (optimizerTriangularMass K) // triangularChoice K integer = j} = j.val + 1 := by
  have hcard := Fintype.card_congr (triangularChoiceFiberEquiv K j.val j.isLt)
  simpa only [Fin.ext_iff, Fintype.card_fin] using hcard

/-- Uniform integer rejection followed by triangular lookup gives the
stored exact optimizer weights. -/
theorem triangularChoice_uniform_weights (K : ℕ) (hK : 0 < K) (j : Fin K) :
    let : NeZero (optimizerTriangularMass K) := ⟨Nat.ne_of_gt (optimizerTriangularMass_positive K hK)⟩
    (((PMF.uniformOfFintype (Fin (optimizerTriangularMass K))).map (triangularChoice K)) j).toReal =
      (optimizerMixtureWeight K j.val : ℝ) := by
  let : NeZero (optimizerTriangularMass K) := ⟨Nat.ne_of_gt (optimizerTriangularMass_positive K hK)⟩
  classical
  dsimp only
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  have hcard : (univ.filter fun integer : Fin (optimizerTriangularMass K) =>
      j = triangularChoice K integer).card = j.val + 1 := by
    rw [← Fintype.card_subtype]
    simpa only [eq_comm] using triangularChoice_fiber_card K j
  rw [hcard]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← optimizerSampler_block_weight K j.val hK]
  push_cast
  ring

/-- Exact coordinate mean of the sampler, including repeated selected
actions, equals the actual rational optimizer iterate. -/
theorem triangularChoice_coordinate_mean {ι : Type*} (initial : ι → ℚ)
    (selected : ℕ → ι → ℚ) (K : ℕ) (hK : 0 < K) (i : ι) :
    (∑ integer : Fin (optimizerTriangularMass K), selected (triangularChoice K integer).val i) /
        optimizerTriangularMass K = rationalOptimizerIterate initial selected K i := by
  classical
  have hsum : (∑ integer : Fin (optimizerTriangularMass K), selected (triangularChoice K integer).val i) =
      ∑ j : Fin K, ((j.val + 1 : ℕ) : ℚ) * selected j.val i := by
    rw [← Fintype.sum_fiberwise' (triangularChoice K) (fun j => selected j.val i)]
    apply sum_congr rfl
    intro j hj
    rw [sum_const, card_univ, triangularChoice_fiber_card, nsmul_eq_mul]
  have hmixture := rationalOptimizerIterate_eq_mixture initial selected (K - 1) i
  rw [Nat.sub_add_cancel (show 1 ≤ K by omega)] at hmixture
  rw [hsum, sum_div, hmixture, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j hj
  rw [← optimizerSampler_block_weight K j.val hK]
  ring

/-- The exactly sampled action has the mean computed by the finite
rational optimizer, with no distinction assumption on its selections. -/
theorem finiteRationalOptimizer_sampler_mean {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G K : ℕ) (hK : 0 < K) (i : ι) :
    (∑ integer : Fin (optimizerTriangularMass K),
      finiteOptimizerSelection coordinates vertices linear G (triangularChoice K integer).val i) /
        optimizerTriangularMass K = finiteRationalOptimizer coordinates vertices linear G K i := by
  rw [finiteRationalOptimizer_eq_iterate]
  exact triangularChoice_coordinate_mean _ _ K hK i

end EditApproximation

end OAI
