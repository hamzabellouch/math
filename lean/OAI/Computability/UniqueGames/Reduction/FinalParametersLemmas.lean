import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Games.CompletedSamplingLemmas
import OAI.Computability.UniqueGames.Games.FactorizationLemmas
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas
import OAI.Computability.UniqueGames.Soundness.PartnerLinearLemmas

namespace OAI

section

/-! Existence of the finite numerical choices in Section 4.1. All errors and
search tests here are rational, including the fourth-power test in (4.1). -/

namespace UniqueGamesTheorem.Integration.FinalParameters

open UniqueGamesTheorem.Soundness.RepetitionUpper

def rho (r s : Nat) : ℚ := (1 / 2 : ℚ) ^ (s - (r + 1))
def levelConstant (r : Nat) : ℚ := (r + 1 : ℚ) * 2 ^ (30 * r ^ 2)
def alpha (δ : ℚ) (s : Nat) : ℚ := δ / (8 * (2 : ℚ) ^ s * 2 ^ (s ^ 2))
def beta (r s : Nat) : ℚ := rho r s / 2 * (1 / 2 : ℚ) ^ (r * s)
def theta (δ : ℚ) (r s : Nat) : ℚ := alpha δ s * beta r s
def repetitionRate : ℚ := 1 - 1 / (100000 * 192 ^ 3)

theorem levelConstant_pos (r : Nat) : 0 < levelConstant r := by
  unfold levelConstant
  positivity

theorem rho_pos (r s : Nat) : 0 < rho r s := by
  unfold rho
  positivity

theorem theta_pos {δ : ℚ} (hδ : 0 < δ) (r s : Nat) : 0 < theta δ r s := by
  unfold theta alpha beta
  have := rho_pos r s
  positivity

theorem repetitionRate_bounds : 0 ≤ repetitionRate ∧ repetitionRate < 1 := by
  norm_num [repetitionRate]

/-- Selecting the exponent as a multiple of four supplies an exact rational
fourth root. No approximation of a real root enters the parameter search. -/
theorem exists_symbol_dimension (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧ ∃ u : ℚ,
      0 < u ∧ u ^ 4 = rho r s ∧ levelConstant r * u ≤ δ / 8 := by
  have hA := levelConstant_pos r
  have ht : 0 < δ / (8 * levelConstant r) := by positivity
  obtain ⟨n, hn, hsmall⟩ := exists_power_lt (1 / 2 : ℚ)
    (δ / (8 * levelConstant r)) (by norm_num) (by norm_num) ht
  refine ⟨r + 1 + 4 * n, by omega, (1 / 2 : ℚ) ^ n, by positivity, ?_, ?_⟩
  · unfold rho
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    congr 1
    omega
  · have hbound : (1 / 2 : ℚ) ^ n * (8 * levelConstant r) < δ :=
      (lt_div_iff₀ (by positivity)).mp hsmall
    linarith

/-- The repetition length is chosen first; the comparison dimension is then
large enough for both the subset experiment and its squared error bound. -/
theorem exists_repetition_and_dimension (L q : Nat) {θ : ℚ}
    (hθ : 0 < θ) (hq : 0 < q) :
    ∃ t k : Nat, 0 < t ∧ t ≤ k ∧
      (1 - zeroProbability L * (1 - repetitionRate)) ^ t < decoderThreshold θ q ∧
      16 * (t : ℚ) ^ 2 * 2 ^ (t * L) ≤ (k : ℚ) * θ ^ 2 := by
  obtain ⟨t, ht, hrep⟩ := exists_repetition_length L q repetitionRate θ
    repetitionRate_bounds.1 repetitionRate_bounds.2 hθ hq
  let B : ℚ := 16 * (t : ℚ) ^ 2 * 2 ^ (t * L)
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (B / θ ^ 2)
  refine ⟨t, t + n, ht, by omega, hrep, ?_⟩
  have hnlarge : B < (n : ℚ) * θ ^ 2 :=
    (div_lt_iff₀ (by positivity)).mp hlarge
  have ht0 : 0 ≤ (t : ℚ) * θ ^ 2 := by positivity
  dsimp [B] at hnlarge
  simp only [Nat.cast_add]
  nlinarith

def gamma (ε : ℚ) (k : Nat) : ℚ := ε / (4 * (k : ℚ))

theorem gamma_bounds {ε : ℚ} {k : Nat}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hk : 0 < k) :
    0 < gamma ε k ∧ gamma ε k < 1 / 8 := by
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  unfold gamma
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).2
    linarith

theorem exists_source_error {γ : ℚ} (hγ : 0 < γ) :
    ∃ n : Nat, 0 < n ∧ 0 < (1 / 2 : ℚ) ^ n ∧
      (1 / 2 : ℚ) ^ n ≤ 1 / 16 ∧ (1 / 2 : ℚ) ^ n ≤ γ / 4 := by
  have hm : 0 < min (1 / 16 : ℚ) (γ / 4) := by positivity
  obtain ⟨n, hn, hs⟩ := exists_power_lt (1 / 2 : ℚ)
    (min (1 / 16 : ℚ) (γ / 4)) (by norm_num) (by norm_num) hm
  exact ⟨n, hn, by positivity, le_of_lt (lt_min_iff.mp hs).1,
    le_of_lt (lt_min_iff.mp hs).2⟩

theorem exists_parameters (r : Nat) {ε δ : ℚ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧ ∃ u : ℚ,
      0 < u ∧ u ^ 4 = rho r s ∧ levelConstant r * u ≤ δ / 8 ∧
      ∀ L : Nat, ∃ t k n : Nat,
        0 < t ∧ t ≤ k ∧
        (1 - zeroProbability L * (1 - repetitionRate)) ^ t <
          decoderThreshold (theta δ r s) (2 ^ s) ∧
        16 * (t : ℚ) ^ 2 * 2 ^ (t * L) ≤ (k : ℚ) * (theta δ r s) ^ 2 ∧
        0 < gamma ε k ∧ gamma ε k < 1 / 8 ∧
        0 < n ∧ 0 < (1 / 2 : ℚ) ^ n ∧
        (1 / 2 : ℚ) ^ n ≤ 1 / 16 ∧
        (1 / 2 : ℚ) ^ n ≤ gamma ε k / 4 := by
  obtain ⟨s, hs, u, hu, hroot, hlevel⟩ := exists_symbol_dimension r hδ
  refine ⟨s, hs, u, hu, hroot, hlevel, ?_⟩
  intro L
  obtain ⟨t, k, ht, htk, hrep, hcomp⟩ :=
    exists_repetition_and_dimension L (2 ^ s) (theta_pos hδ r s) (by positivity)
  have hk : 0 < k := lt_of_lt_of_le ht htk
  have hγ := gamma_bounds hε hεhalf hk
  obtain ⟨n, hn, hξ, hξ16, hξγ⟩ := exists_source_error hγ.1
  exact ⟨t, k, n, ht, htk, hrep, hcomp, hγ.1, hγ.2, hn, hξ, hξ16, hξγ⟩

/-- The completeness budget uses the same comparison dimension as the other
parameters. This identity is exact, without rounding of rational errors. -/
theorem completeness_budget {ε : ℚ} {k : Nat} (hk : 0 < k) :
    (k : ℚ) * gamma ε k + (ε / 2) / 2 = ε / 2 := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold gamma
  field_simp
  ring

end UniqueGamesTheorem.Integration.FinalParameters

end

section

/-! Exact passage from the rational construction parameters and experiments to
the real inequalities used by the Fourier and soundness proofs. -/

namespace UniqueGamesTheorem.Integration.RealBounds

open BinaryLinear FinalParameters

theorem rho_eq_two_div_pow {r s : Nat} (hs : r + 1 ≤ s) :
    rho r s = 2 / (2 : ℚ) ^ (s - r) := by
  have hn : s - r = (s - (r + 1)) + 1 := by omega
  unfold rho
  rw [hn, pow_succ, div_pow, one_pow]
  field_simp

theorem rho_real_eq_two_div_pow {r s : Nat} (hs : r + 1 ≤ s) :
    (rho r s : ℝ) = 2 / (2 : ℝ) ^ (s - r) := by
  simpa using congrArg (fun q : ℚ => (q : ℝ)) (rho_eq_two_div_pow hs)

theorem beta_eq_div (r s : Nat) :
    beta r s = rho r s / (2 * (2 : ℚ) ^ (r * s)) := by
  unfold beta
  rw [div_pow, one_pow]
  ring

/-- The exact signal threshold used by selection, expressed in real scalars.
There is no loss between the rational parameter search and this product. -/
theorem theta_real_product (δ : ℚ) (r s : Nat) :
    (theta δ r s : ℝ) =
      ((δ : ℝ) / (8 * (2 : ℝ) ^ s * 2 ^ (s * s))) *
        ((rho r s : ℝ) / (2 * (2 : ℝ) ^ (r * s))) := by
  simp [theta, alpha, beta_eq_div, pow_two]

theorem fourth_root_as_rpow {u ρ : ℚ} (hu : 0 < u) (hfour : u ^ 4 = ρ) :
    (ρ : ℝ) ^ (1 / 4 : ℝ) = (u : ℝ) := by
  have hpow : (u : ℝ) ^ 4 = (ρ : ℝ) := by exact_mod_cast hfour
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast (le_of_lt hu)
  rw [← hpow, one_div]
  exact Real.pow_rpow_inv_natCast hu' (by decide : (4 : Nat) ≠ 0)

theorem exists_symbol_dimension_real (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧
      (levelConstant r : ℝ) * (rho r s : ℝ) ^ (1 / 4 : ℝ) ≤ (δ : ℝ) / 8 := by
  obtain ⟨s, hs, u, hu, hfour, hbound⟩ := exists_symbol_dimension r hδ
  refine ⟨s, hs, ?_⟩
  rw [fourth_root_as_rpow hu hfour]
  exact_mod_cast hbound

/-- Casting the finite experiment changes only its scalar values, retaining
the same noise indices and the same event. -/
theorem kernelProbability_real {s d : Nat}
    (g : UniqueGamesTheorem.Reduction.ActualSource.SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] [DecidableEq P]
    (S : (Vector s × Vector d) →ₗ[F2] P) :
    (SplitGadget.kernelProbability g S : ℝ) =
      Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℝ) else 0) := by
  classical
  unfold SplitGadget.kernelProbability
  simp only [Finset.expect_eq_sum_div_card, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : S (g.noise i) = 0 <;> simp [h]

theorem kernelProbability_real_le {s d : Nat}
    (g : UniqueGamesTheorem.Reduction.ActualSource.SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] [DecidableEq P]
    (S : (Vector s × Vector d) →ₗ[F2] P) {ν : ℚ}
    (h : SplitGadget.kernelProbability g S ≤ ν) :
    Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℝ) else 0) ≤ (ν : ℝ) := by
  classical
  rw [← kernelProbability_real g S]
  exact_mod_cast h

theorem comparison_square_budget {t k L : Nat} {θ : ℚ} (hk : 0 < k)
    (h : 16 * (t : ℚ) ^ 2 * 2 ^ (t * L) ≤ (k : ℚ) * θ ^ 2) :
    ((t : ℝ) ^ 2 / (k : ℝ)) * 2 ^ (t * L) ≤ ((θ : ℝ) / 4) ^ 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h' : 16 * (t : ℝ) ^ 2 * 2 ^ (t * L) ≤ (k : ℝ) * (θ : ℝ) ^ 2 := by
    exact_mod_cast h
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  nlinarith

end UniqueGamesTheorem.Integration.RealBounds

end

section

namespace UniqueGamesTheorem.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

theorem rate_bounds {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    0 < rate gap ∧ rate gap < 1 := by
  have hcube : gap ^ 3 ≤ 1 := pow_le_one₀ hgap.le hgap1
  have hcubePos : 0 < gap ^ 3 := pow_pos hgap _
  constructor <;> unfold rate <;> linarith

theorem fourth_power_comparison {gap : ℚ} (hgap : 0 ≤ gap) (hgap1 : gap ≤ 1) :
    1 - (gap : ℝ) ^ 3 / 6000 ≤ (rate gap : ℝ) ^ 4 := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hc0 : 0 ≤ (gap : ℝ) ^ 3 := pow_nonneg hg _
  have hb := one_add_mul_le_pow (a := -(gap : ℝ) ^ 3 / 100000)
    (by linarith : (-2 : ℝ) ≤ -(gap : ℝ) ^ 3 / 100000) 4
  have hr : (rate gap : ℝ) = 1 - (gap : ℝ) ^ 3 / 100000 := by
    simp only [rate, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat]
  rw [hr]
  calc
    _ ≤ 1 + 4 * (-(gap : ℝ) ^ 3 / 100000) := by linarith
    _ ≤ _ := by simpa only [Nat.cast_ofNat, sub_eq_add_neg, neg_div] using hb

/-- The answer alphabet product is 16, so its binary logarithm is four.
This converts the genuine repetition theorem's real exponent to a rational
base raised to the integral repetition length. -/
theorem four_bit_rate_comparison {gap : ℚ}
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (n : Nat) :
    (1 - (gap : ℝ) ^ 3 / 6000) ^ ((n : ℝ) / 4) ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap.le
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hr : (0 : ℝ) ≤ rate gap := by exact_mod_cast (rate_bounds hgap hgap1).1.le
  calc
    _ ≤ ((rate gap : ℝ) ^ 4) ^ ((n : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) (fourth_power_comparison hgap.le hgap1) (by positivity)
    _ = (rate gap : ℝ) ^ ((4 : ℝ) * ((n : ℝ) / 4)) :=
      (Real.rpow_natCast_mul hr 4 ((n : ℝ) / 4)).symm
    _ = (rate gap : ℝ) ^ (n : ℝ) := by congr 1; ring
    _ = _ := Real.rpow_natCast _ _

theorem logTwo_sixteen : UniqueGamesTheorem.Foundations.Repetition.logTwo 16 = 4 := by
  unfold UniqueGamesTheorem.Foundations.Repetition.logTwo
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp [hlog]

/-- The actual finite game's repetition rate, with its answer cardinality
checked as an ordinary finite count. No repetition estimate is assumed. -/
theorem game_repetition_rate {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : UniqueGamesTheorem.Foundations.Games.Game Q₁ Q₂ A₁ A₂)
    {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hcards : Fintype.card A₁ * Fintype.card A₂ = 16)
    (hvalue : G.value ≤ 1 - (gap : ℝ)) (n : Nat) :
    (G.repetition n).value ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) < gap := by exact_mod_cast hgap
  have halphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ 4 := by
    rw [← Nat.cast_mul, hcards]
    exact logTwo_sixteen.le
  have h := UniqueGamesTheorem.Foundations.Repetition.holenstein_repetition_value
    G n hvalue (by linarith) (by norm_num : (1 : ℝ) ≤ 4) halphabet
  simp only [sub_sub_cancel] at h
  exact h.trans (four_bit_rate_comparison hgap hgap1 n)

def sourceThreshold (D : Nat) (δ : ℚ) : ℚ := 4 * (D : ℚ)⁻¹ * δ ^ 2

theorem sourceThreshold_pos {D : Nat} (hD : 0 < D) {δ : ℚ} (hδ : 0 < δ) :
    0 < sourceThreshold D δ := by
  unfold sourceThreshold
  positivity

theorem exists_repetition_length {gap δ : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) {D : Nat} (hD : 0 < D) :
    ∃ u : Nat, 0 < u ∧ (rate gap) ^ u < sourceThreshold D δ :=
  UniqueGamesTheorem.Soundness.RepetitionUpper.exists_power_lt (rate gap) (sourceThreshold D δ)
    (rate_bounds hgap hgap1).1.le (rate_bounds hgap hgap1).2 (sourceThreshold_pos hD hδ)

/-- Exact rational search, independent of the input formula. -/
def repetitionLength (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) : Nat :=
  Nat.find (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_spec (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    0 < repetitionLength gap δ hgap hgap1 hδ D hD ∧
      rate gap ^ repetitionLength gap δ hgap hgap1 hδ D hD < sourceThreshold D δ :=
  Nat.find_spec (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_real_bound (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    (rate gap : ℝ) ^ repetitionLength gap δ hgap hgap1 hδ D hD ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2 := by
  have h := (repetitionLength_spec gap δ hgap hgap1 hδ D hD).2.le
  unfold sourceThreshold at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  exact hr

end UniqueGamesTheorem.Integration.SourceParameters

end

end OAI
