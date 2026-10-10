import Mathlib
import OAI.Computability.MaxCut.PCP.DistributionMaps
import OAI.Computability.MaxCut.PCP.MatrixParityRow
import OAI.Computability.MaxCut.Games.MatrixNoise

namespace OAI

noncomputable section

namespace MaxCutGames.Decoder.PrivateFourier

open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixParity
open MaxCutGames.Fourier.MatrixParityRow
open scoped BigOperators Classical

section Signs

/-- A real-valued binary character, with the uniform Fourier normalization. -/
def sign (a : F2) : ℝ := (binarySign a).re

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_sq (a : F2) : sign a ^ 2 = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

@[simp] theorem sign_abs (a : F2) : |sign a| = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  simp [sign, binarySign_add, Complex.mul_re]

theorem sign_add_one (a : F2) : sign (a + 1) = -sign a := by
  rw [sign_add, sign_one]
  ring

end Signs

section CharacterAverages

variable {H K : Type*} [AddCommGroup H] [Module F2 H]
    [AddCommGroup K] [Module F2 K]

theorem binary_neg_eq_self (x : K) : -x = x := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hh := congrArg (fun a : F2 => a • x) htwo
  exact neg_eq_iff_add_eq_zero.mpr
    (by simpa only [add_smul, one_smul, zero_smul] using hh)

theorem binary_add_eq_zero_iff (x y : K) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, binary_neg_eq_self]

theorem average_sign_dual [Fintype (K →ₗ[F2] F2)] (x : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x)) = if x = 0 then 1 else 0 := by
  have h := congrArg Complex.re
    (MaxCutGames.Fourier.MatrixNoise.average_evaluationCharacter x)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re, sign] using h

theorem average_sign_primal [Fintype H] (σ : H →ₗ[F2] F2) :
    (𝔼 h : H, sign (σ h)) = if σ = 0 then 1 else 0 := by
  have h := congrArg Complex.re (expect_linearFunctionalCharacter σ)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re,
    linearFunctionalCharacter_apply, sign] using h

/-- Exact character expansion of equality in the actual output space. -/
theorem average_sign_equality [Fintype (K →ₗ[F2] F2)] (x y : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x) * sign (σ y)) =
      if x = y then 1 else 0 := by
  simp_rw [← sign_add, ← map_add]
  rw [average_sign_dual, binary_add_eq_zero_iff]

/-- The ambient uniform character has trivial restriction to `H` with exactly
the reciprocal cardinality of `H`.  No conditioning on the private character
is substituted for the real experiment. -/
theorem trivial_restriction_probability [Fintype H] [Fintype (K →ₗ[F2] F2)]
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) :
    (𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0) =
      1 / (Fintype.card H : ℝ) := by
  calc
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 h : H, sign (σ (ι h)) := by
      apply Finset.expect_congr rfl
      intro σ _
      exact (average_sign_primal (σ.comp ι)).symm
    _ = 𝔼 h : H, 𝔼 σ : K →ₗ[F2] F2, sign (σ (ι h)) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 h : H, if h = 0 then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro h _
      rw [average_sign_dual]
      have heq : ι h = 0 ↔ h = 0 := by
        rw [← map_zero ι]
        exact hι.eq_iff
      rw [heq]
    _ = _ := by simp []

theorem trivial_restriction_probability_pow [Fintype H]
    [FiniteDimensional F2 H] [Fintype (K →ₗ[F2] F2)]
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) :
    (𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0) =
      1 / (2 : ℝ) ^ Module.finrank F2 H := by
  rw [trivial_restriction_probability ι hι]
  have hc : Fintype.card H = 2 ^ Module.finrank F2 H := by
    simpa [F2, Integration.BinaryLinear.F2, ZMod.card] using
      Module.card_fintype (Module.finBasis F2 H)
  rw [hc]
  norm_cast

end CharacterAverages

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

/-- The private sign function, formed from the table on one visible row fiber. -/
def tableSign (F : (E →ₗ[F2] H) → K) (σ : K →ₗ[F2] F2)
    (N : E →ₗ[F2] H) : ℝ := sign (σ (F N))

/-- The actual probability assigned to a reverse-map frequency. -/
def frequencyWeight (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) : ℝ :=
  linearCoeff f Φ ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
theorem frequencyWeight_nonneg (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) :
    0 ≤ frequencyWeight f Φ := sq_nonneg _

/-- Squared Fourier coefficients of the private sign form a probability law. -/
theorem tableSign_frequencyWeight_sum (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) :
    ∑ Φ : H →ₗ[F2] E, frequencyWeight (tableSign F σ) Φ = 1 := by
  simp only [frequencyWeight, linear_parseval, tableSign, sign_sq]
  exact Fintype.expect_const 1

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem tableSign_antifold (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (σ : K →ₗ[F2] F2) (h : H)
    (folded : ∀ N, F (N + τ.smulRight h) = F N + ι h)
    (hσ : σ (ι h) = 1) :
    ∀ N, tableSign F σ (N + τ.smulRight h) = -tableSign F σ N := by
  intro N
  simp only [tableSign, folded, map_add, hσ, sign_add_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
/-- Translation of the input multiplies a coefficient by its character. -/
theorem linearCoeff_translate (f : (E →ₗ[F2] H) → ℝ)
    (D : E →ₗ[F2] H) (Φ : H →ₗ[F2] E) :
    linearCoeff (fun N => f (N + D)) Φ =
      linearCoeff f Φ * (linearTraceCharacter Φ D).re := by
  have hself : D + D = 0 :=
    (linearMap_add_eq_zero_iff D D).2 rfl
  have hchange := Fintype.expect_equiv (Equiv.addRight D)
    (fun N => f (N + D) * (linearTraceCharacter Φ N).re)
    (fun N => f N * (linearTraceCharacter Φ (N + D)).re)
    (fun N => by simp only [Equiv.coe_addRight, add_assoc, hself, add_zero])
  unfold linearCoeff
  rw [hchange]
  simp only [traceCharacter_re_add, ← mul_assoc]
  exact (Finset.expect_mul _ _ _).symm

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] in
/-- Anti-folding forces every positive-mass frequency to return first bit one. -/
theorem positive_frequency_first_bit (f : (E →ₗ[F2] H) → ℝ)
    (τ : E →ₗ[F2] F2) (h : H) (Φ : H →ₗ[F2] E)
    (folded : ∀ N, f (N + τ.smulRight h) = -f N)
    (positive : 0 < frequencyWeight f Φ) : τ (Φ h) = 1 := by
  have hcoeff : linearCoeff f Φ ≠ 0 := by
    intro hz
    simp [frequencyWeight, hz] at positive
  have heq := linearCoeff_translate f (τ.smulRight h) Φ
  have hneg : linearCoeff (fun N => f (N + τ.smulRight h)) Φ =
      -linearCoeff f Φ := by
    simp only [linearCoeff, folded, neg_mul]
    simp [Fintype.expect_eq_sum_div_card]
  rw [hneg] at heq
  have hchar : (linearTraceCharacter Φ (τ.smulRight h)).re = sign (τ (Φ h)) := by
    simp only [linearTraceCharacter_apply, linearTracePair, trace_smulRight_comp, sign]
  rw [hchar] at heq
  rcases Integration.BinaryLinear.scalar_cases (τ (Φ h)) with hz | hone
  · rw [hz, sign_zero, mul_one] at heq
    exact False.elim (hcoeff (by linarith))
  · exact hone

end ActualFourier

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

/-- Frequencies in the affine target's annihilator coset.  With `q = Q.mkQ`,
this is exactly `θ + Hom(H,Q)` in the ambient reverse-map space. -/
def frequencyCoset (q : E →ₗ[F2] V) (θ : H →ₗ[F2] E) :
    Finset (H →ₗ[F2] E) := Finset.univ.filter fun Φ => q.comp (Φ + θ) = 0

/-- Correlation on a genuine affine slice.  `N₀` is retained: its phase cannot
be discarded when the witness has a nonzero affine intercept. -/
def sliceCorrelation (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) : ℝ :=
  𝔼 A : V →ₗ[F2] H,
    f (N₀ + A.comp q) * (linearTraceCharacter θ (N₀ + A.comp q)).re

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem traceCharacter_re_mul (Φ θ : H →ₗ[F2] E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter Φ N).re * (linearTraceCharacter θ N).re =
      (linearTraceCharacter (Φ + θ) N).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- The exact Fourier coset expansion of the affine conditional correlation. -/
theorem sliceCorrelation_eq_coset (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ =
      ∑ Φ ∈ frequencyCoset q θ,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re := by
  unfold sliceCorrelation
  calc
    _ = 𝔼 A : V →ₗ[F2] H, ∑ Φ : H →ₗ[F2] E,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) (N₀ + A.comp q)).re := by
      apply Finset.expect_congr rfl
      intro A _
      rw [← linear_fourier_inversion f (N₀ + A.comp q), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Φ _
      rw [mul_assoc, traceCharacter_re_mul]
    _ = ∑ Φ : H →ₗ[F2] E, if q.comp (Φ + θ) = 0 then
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re else 0 := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro Φ _
      simp only [traceCharacter_re_add, ← mul_assoc]
      rw [← Finset.mul_expect, row_character_average]
      split <;> simp
    _ = _ := by simp [frequencyCoset, Finset.sum_filter]

/-- Cauchy--Schwarz bounds an affine correlation by the actual Fourier mass
in its target coset; no spectral mass is assumed. -/
theorem sliceCorrelation_sq_le_coset_mass (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ ^ 2 ≤
      (frequencyCoset q θ).card *
        ∑ Φ ∈ frequencyCoset q θ, frequencyWeight f Φ := by
  rw [sliceCorrelation_eq_coset]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (frequencyCoset q θ)
    (linearCoeff f) (fun Φ => (linearTraceCharacter (Φ + θ) N₀).re)
  have hs : ∀ Φ : H →ₗ[F2] E,
      (linearTraceCharacter (Φ + θ) N₀).re ^ 2 = 1 := by
    intro Φ
    exact sign_sq _
  simpa only [hs, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul,
    frequencyWeight, mul_comm] using hcs

end AffineSlice

section AffineEquality

variable {E H K V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K] [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)] [Fintype (K →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- The pure-tensor target character is literally evaluation at `z`. -/
theorem target_character (σ : H →ₗ[F2] F2) (z : E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter (σ.smulRight z) N).re = sign (σ (N z)) := by
  simp only [linearTraceCharacter_apply, sign]
  congr 2
  rw [linearTracePair_swap]
  exact trace_smulRight_comp σ z N

omit [FiniteDimensional F2 V] in
omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Affine target equality expands into the correlations with the intercept
phase `sign (σ b)`.  In the projected experiment `b = M₀ z + u`. -/
theorem affine_equality_character_expansion (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) =
      𝔼 σ : K →ₗ[F2] F2, sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z) := by
  calc
    _ = 𝔼 A : V →ₗ[F2] H, 𝔼 σ : K →ₗ[F2] F2,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := by
      apply Finset.expect_congr rfl
      intro A _
      exact (average_sign_equality _ _).symm
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 A : V →ₗ[F2] H,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := Finset.expect_comm _ _ _
    _ = _ := by
      apply Finset.expect_congr rfl
      intro σ _
      unfold sliceCorrelation
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro A _
      simp only [map_add, sign_add, target_character, tableSign, LinearMap.comp_apply]
      ring

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
/-- Every slice correlation has absolute value at most one. -/
theorem sliceCorrelation_tableSign_abs_le_one (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) (θ : H →ₗ[F2] E) :
    |sliceCorrelation q N₀ (tableSign F σ) θ| ≤ 1 := by
  unfold sliceCorrelation
  calc
    _ ≤ 𝔼 A : V →ₗ[F2] H,
        |tableSign F σ (N₀ + A.comp q) *
          (linearTraceCharacter θ (N₀ + A.comp q)).re| := Finset.abs_expect_le _ _
    _ = 1 := by
      have hp (N : E →ₗ[F2] H) : |(linearTraceCharacter θ N).re| = 1 := sign_abs _
      simp only [abs_mul, tableSign, sign_abs, hp, mul_one]
      exact Fintype.expect_const 1

omit [FiniteDimensional F2 V] in
omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Dropping the unit intercept phase can only increase the average absolute
correlation; the hypothesis is the actual affine-slice agreement probability. -/
theorem agreement_le_average_abs_correlation (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) ≤
      𝔼 σ : K →ₗ[F2] F2,
        |sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := by
  rw [affine_equality_character_expansion]
  apply Finset.expect_le_expect
  intro σ _
  calc
    _ ≤ |sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := le_abs_self _
    _ = _ := by rw [abs_mul, sign_abs, one_mul]

end AffineEquality

section CosetCardinality

variable {E H : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (H →ₗ[F2] E)]

/-- The exact number of frequencies in the affine coset.  Translation does not
alter the annihilator cardinality, including when the target is nonzero. -/
theorem frequencyCoset_card (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) :
    (frequencyCoset Q.mkQ θ).card =
      2 ^ (Module.finrank F2 H * Module.finrank F2 Q) := by
  classical
  rw [frequencyCoset, ← Fintype.card_subtype]
  calc
    Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp (Φ + θ) = 0} =
        Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp Φ = 0} :=
      Fintype.card_congr (Equiv.subtypeEquiv (Equiv.addRight θ) (fun _ => Iff.rfl))
    _ = Fintype.card (H →ₗ[F2] Q) :=
      MaxCutGames.Fourier.MatrixRestrictions.quotientKernel_card Q
    _ = _ := card_linearMaps

theorem frequencyCoset_card_le (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r) :
    (frequencyCoset Q.mkQ θ).card ≤ 2 ^ (ℓ * r) := by
  rw [frequencyCoset_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul hH hQ)

end CosetCardinality

section Averaging

variable {SigmaChar : Type*} [Fintype SigmaChar] [Nonempty SigmaChar]

omit [Nonempty SigmaChar] in
/-- Discarding a set of characters costs at most its actual uniform mass. -/
theorem remove_bad_characters (C : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (a b : ℝ) (hC : ∀ σ, |C σ| ≤ 1)
    (hcorrelation : a ≤ 𝔼 σ, |C σ|)
    (hbad : (𝔼 σ, if good σ then (0 : ℝ) else 1) ≤ b) :
    a - b ≤ 𝔼 σ, if good σ then |C σ| else 0 := by
  classical
  have hp : (𝔼 σ, |C σ|) ≤
      (𝔼 σ, if good σ then |C σ| else 0) +
      (𝔼 σ, if good σ then (0 : ℝ) else 1) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simp [hg]
    · simpa [hg] using hC σ
  linarith

/-- The second Cauchy--Schwarz step in private decoding.  The first step is
`sliceCorrelation_sq_le_coset_mass`; the mass is the actual sampled Fourier
mass and `good` selects nontrivial output characters. -/
theorem average_coset_mass_lower (C mass : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (N c : ℝ) (hN : 0 < N) (hc : 0 ≤ c)
    (hcorrelation : c ≤ 𝔼 σ, if good σ then |C σ| else 0)
    (hpoint : ∀ σ, good σ → C σ ^ 2 ≤ N * mass σ) :
    c ^ 2 / N ≤ 𝔼 σ, if good σ then mass σ else 0 := by
  classical
  let d : SigmaChar → ℝ := fun σ => if good σ then |C σ| else 0
  have hj := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hj
  have hp : (𝔼 σ, d σ ^ 2) ≤ N * (𝔼 σ, if good σ then mass σ else 0) := by
    rw [Finset.mul_expect]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simpa [d, hg, sq_abs] using hpoint σ hg
    · simp [d, hg]
  have hs : c ^ 2 ≤ (𝔼 σ, d σ) ^ 2 := by
    have hd : c ≤ 𝔼 σ, d σ := hcorrelation
    nlinarith
  apply (div_le_iff₀ hN).2
  nlinarith

end Averaging

section Contraction

variable {E H : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup H] [Module F2 H]

/-- A frequency in the target coset contracts into `z + Q`. -/
theorem contraction_mem_target_coset (Q : Submodule F2 E)
    (σ : H →ₗ[F2] F2) (z : E) (Φ : H →ₗ[F2] E) (h : H)
    (hσ : σ h = 1) (hcoset : Q.mkQ.comp (Φ + σ.smulRight z) = 0) :
    Φ h - z ∈ Q := by
  have hq := LinearMap.congr_fun hcoset h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    hσ, one_smul, LinearMap.zero_apply] at hq
  have hmem : Φ h + z ∈ Q := by
    change Q.mkQ (Φ h + z) = 0 at hq
    exact (Submodule.Quotient.mk_eq_zero Q).mp hq
  have hz : -z = z := by
    have htwo : (1 + 1 : F2) = 0 := by decide
    have hzz : z + z = 0 := by
      have hh := congrArg (fun a : F2 => a • z) htwo
      simpa only [add_smul, one_smul, zero_smul] using hh
    exact neg_eq_iff_add_eq_zero.mpr hzz
  simpa only [sub_eq_add_neg, hz] using hmem

end Contraction

variable {U O Ω : Type*} [Fintype Ω]

/-- If the returned projected answer has a preimage in the candidate set, the
uniform, independently sampled candidate finds a preimage with this probability. -/
theorem uniform_preimage_probability (s : Finset U) (π : U → O) (b : O)
    (preimage : ∃ u ∈ s, π u = b) :
    1 / (s.card : ℝ) ≤ 𝔼 u ∈ s, if π u = b then (1 : ℝ) else 0 := by
  classical
  obtain ⟨u, hu, hπ⟩ := preimage
  have hsum : (1 : ℝ) ≤ ∑ v ∈ s, if π v = b then (1 : ℝ) else 0 := by
    have hnonneg : ∀ v ∈ s, (0 : ℝ) ≤ if π v = b then 1 else 0 := by
      intro v _
      split <;> norm_num
    have h := Finset.single_le_sum hnonneg hu
    simpa only [hπ, ite_true] using h
  rw [Finset.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- An explicit product sampling law: the left strategy samples uniformly from
`s`, independently of the right strategy's private sample.  Only positive-mass
good samples need a preimage; no private Fourier information is passed left. -/
theorem independent_agreement_lower (s : Finset U) (π : U → O)
    (answer : Ω → O) (weight : Ω → ℝ) (good : Ω → Prop)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (preimage : ∀ ω, good ω → 0 < weight ω → ∃ u ∈ s, π u = answer ω) :
    (∑ ω, if good ω then weight ω else 0) / (s.card : ℝ) ≤
      ∑ ω, weight ω * (𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω _
  have havg : 0 ≤ 𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0 :=
    Finset.expect_nonneg fun _ _ => by positivity
  by_cases hg : good ω
  · simp only [hg, ite_true]
    by_cases hw : 0 < weight ω
    · have hb := uniform_preimage_probability s π (answer ω) (preimage ω hg hw)
      have := mul_le_mul_of_nonneg_left hb (hweight ω)
      simpa only [div_eq_mul_inv, one_mul] using this
    · have hz : weight ω = 0 := le_antisymm (le_of_not_gt hw) (hweight ω)
      simp [hz]
  · simp only [hg, ite_false, zero_div]
    exact mul_nonneg (hweight ω) havg

end MaxCutGames.Decoder.PrivateFourier

/-!
# Actual private response laws for v2 Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

namespace MaxCutGames.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Foundations.Games
open scoped BigOperators Classical

section Candidates

variable {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Fintype E]

def candidates (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2) : Finset E :=
  Finset.univ.filter fun v => v - z ∈ Z ∧ τ v = 1

theorem mem_candidates (Z : Submodule F2 E) (z v : E) (τ : E →ₗ[F2] F2) :
    v ∈ candidates Z z τ ↔ v - z ∈ Z ∧ τ v = 1 := by simp [candidates]

theorem candidates_nonempty (Z : Submodule F2 E) (z : E)
    (τ : E →ₗ[F2] F2) (hz : τ z = 1) : (candidates Z z τ).Nonempty := by
  exact ⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩

theorem candidates_card_le (Z : Submodule F2 E) [Fintype Z] (z : E)
    (τ : E →ₗ[F2] F2) : (candidates Z z τ).card ≤ Fintype.card Z := by
  let f : {v // v ∈ candidates Z z τ} → Z := fun v =>
    ⟨v.1 - z, ((mem_candidates Z z v.1 τ).1 v.2).1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change x.val - z = y.val - z at he
    exact sub_left_injective he
  simpa using Fintype.card_le_of_injective f hf

theorem candidates_card_le_pow (Z : Submodule F2 E) [Fintype Z]
    [FiniteDimensional F2 Z] (z : E) (τ : E →ₗ[F2] F2)
    (r : ℕ) (hr : Module.finrank F2 Z ≤ r) :
    (candidates Z z τ).card ≤ 2 ^ r := by
  have hc : Fintype.card Z = 2 ^ Module.finrank F2 Z := by
    simpa [F2, MaxCutGames.Integration.BinaryLinear.F2, ZMod.card] using
      Module.card_fintype (Module.finBasis F2 Z)
  calc
    _ ≤ Fintype.card Z := candidates_card_le Z z τ
    _ = 2 ^ Module.finrank F2 Z := hc
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr

/-- First-bit preservation converts a projected coset member into an actual
answer in the left candidate set. -/
theorem candidate_preimage (Z : Submodule F2 E) (z : E)
    (π : E →ₗ[F2] E') (τ : E →ₗ[F2] F2) (τ' : E' →ₗ[F2] F2)
    (hτ : τ'.comp π = τ) (y : E') (hy : y - π z ∈ Z.map π)
    (hybit : τ' y = 1) : ∃ v ∈ candidates Z z τ, π v = y := by
  obtain ⟨w, hw, hwπ⟩ := Submodule.mem_map.mp hy
  have heq : π (z + w) = y := by
    rw [map_add, hwπ]
    rw [add_comm, sub_add_cancel]
  refine ⟨z + w, (mem_candidates Z z (z + w) τ).2 ⟨?_, ?_⟩, heq⟩
  · simpa only [add_sub_cancel_left] using hw
  · rw [← hτ, LinearMap.comp_apply, heq, hybit]

end Candidates

section RightRule

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [FiniteDimensional F2 H] in
theorem exists_unit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : ∃ h, σ h = 1 := by
  have hn : ∃ h, σ h ≠ 0 := by
    by_contra hh
    apply hne
    ext h
    by_contra hh'
    exact hh ⟨h, hh'⟩
  obtain ⟨h, hh⟩ := hn
  exact ⟨h, (MaxCutGames.Integration.BinaryLinear.scalar_cases _).resolve_left hh⟩

def chooseUnit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : H :=
  Classical.choose (exists_unit σ hne)

omit [FiniteDimensional F2 H] in
theorem chooseUnit_spec (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) :
    σ (chooseUnit σ hne) = 1 := Classical.choose_spec (exists_unit σ hne)

abbrev ActualAnswer (τ : E →ₗ[F2] F2) := {v : E // τ v = 1}

/-- The uniform output character followed by its actual Fourier frequency. -/
def privateSeedLaw (F : (E →ₗ[F2] H) → K) :
    FiniteDistribution ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) where
  weight p := frequencyWeight (tableSign F p.1) p.2 /
    (Fintype.card (K →ₗ[F2] F2) : ℝ)
  nonnegative p := div_nonneg (frequencyWeight_nonneg _ _) (Nat.cast_nonneg _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, tableSign_frequencyWeight_sum]
    simp [Fintype.card_ne_zero]

theorem privateSeedLaw_expectation (F : (E →ₗ[F2] H) → K)
    (g : ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) → ℝ) :
    (privateSeedLaw F).expectation g =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ * g (σ, Φ) := by
  simp only [FiniteDistribution.expectation, privateSeedLaw, Fintype.sum_prod_type,
    Fintype.expect_eq_sum_div_card]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

/-- The decoder receives no left witness.  The first-bit repair affects only
zero-mass frequencies when the table is folded. -/
def privateOutput (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2)
    (fallback : ActualAnswer τ) (p : (K →ₗ[F2] F2) × (H →ₗ[F2] E)) :
    ActualAnswer τ :=
  if hn : p.1.comp ι = 0 then fallback else
    let v := p.2 (chooseUnit (p.1.comp ι) hn)
    if hv : τ v = 1 then ⟨v, hv⟩ else fallback

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
theorem privateOutput_eq_contraction (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (σ : K →ₗ[F2] F2) (Φ : H →ₗ[F2] E)
    (hn : σ.comp ι ≠ 0) (hp : 0 < frequencyWeight (tableSign F σ) Φ) :
    (privateOutput ι τ fallback (σ, Φ)).1 = Φ (chooseUnit (σ.comp ι) hn) := by
  have hunit : σ (ι (chooseUnit (σ.comp ι) hn)) = 1 := chooseUnit_spec (σ.comp ι) hn
  have hfold := tableSign_antifold F ι τ σ (chooseUnit (σ.comp ι) hn)
    (fun N => folded N _) hunit
  have hbit := positive_frequency_first_bit (tableSign F σ) τ
    (chooseUnit (σ.comp ι) hn) Φ hfold hp
  simp [privateOutput, hn, hbit]

/-- This is an actual finite distribution on actual answers, for every visible
row table.  The sampler's normalization is Parseval, not a hypothesis. -/
def privateLaw [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    FiniteDistribution (ActualAnswer τ) :=
  (privateSeedLaw F).pushforward (privateOutput ι τ fallback)

theorem privateLaw_expectation [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (g : ActualAnswer τ → ℝ) :
    (privateLaw F ι τ fallback).expectation g =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ * g (privateOutput ι τ fallback (σ, Φ)) := by
  rw [privateLaw, FiniteDistribution.expectation_pushforward, privateSeedLaw_expectation]

end RightRule

section LeftRule

variable {E : Type*} [AddCommGroup E] [Module F2 E] [Fintype E]

/-- The left rule is uniform on its own chosen affine-answer candidates. -/
def candidateLaw (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2)
    (hz : τ z = 1) : FiniteDistribution (ActualAnswer τ) := by
  letI : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  exact (FiniteDistribution.uniform {v // v ∈ candidates Z z τ}).pushforward
    (fun v => ⟨v.1, ((mem_candidates Z z v.1 τ).1 v.2).2⟩)

theorem candidateLaw_expectation (Z : Submodule F2 E) (z : E)
    (τ : E →ₗ[F2] F2) (hz : τ z = 1) (g : E → ℝ) :
    (candidateLaw Z z τ hz).expectation (fun v => g v.1) =
      𝔼 v ∈ candidates Z z τ, g v := by
  let : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  unfold candidateLaw
  rw [FiniteDistribution.expectation_pushforward, FiniteDistribution.expectation_uniform,
    Finset.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Finset.sum_coe_sort]

end LeftRule

section ConditionalAgreement

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

/-- Actual independent response-law success, with the literal projection test. -/
def conditionalAgreement (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) : ℝ :=
  ((candidateLaw Z z τU hz).product (privateLaw F ι τ fallback)).probability
    (fun a => decide (π a.1.1 = a.2.1))

theorem conditionalAgreement_eq_sum (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    conditionalAgreement Z z τU hz π F ι τ fallback =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ *
          (𝔼 v ∈ candidates Z z τU,
            if π v = (privateOutput ι τ fallback (σ, Φ)).1 then (1 : ℝ) else 0) := by
  unfold conditionalAgreement
  have hp (μ : FiniteDistribution (ActualAnswer τU × ActualAnswer τ)) :
      μ.probability (fun a => decide (π a.1.1 = a.2.1)) =
      μ.expectation (fun a => if π a.1.1 = a.2.1 then (1 : ℝ) else 0) := by
    simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
  rw [hp, FiniteDistribution.expectation_product]
  simp_rw [privateLaw_expectation]
  rw [candidateLaw_expectation Z z τU hz (fun v =>
    𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
      frequencyWeight (tableSign F σ) Φ *
        (if π v = (privateOutput ι τ fallback (σ, Φ)).1 then (1 : ℝ) else 0)),
    Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro σ _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Φ _
  exact (Finset.mul_expect _ _ _).symm

/-- The exact good Fourier mass in a witness coset; unlike the response law,
this analysis-only quantity is allowed to mention the witness. -/
def goodCosetMass (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) : ℝ :=
  𝔼 σ : K →ₗ[F2] F2, if σ.comp ι ≠ 0 then
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ else 0

omit [Fintype E] in
omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] in
theorem goodCosetMass_nonneg (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) :
    0 ≤ goodCosetMass Q z' F ι := by
  apply Finset.expect_nonneg
  intro σ _
  split
  · exact Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _
  · exact le_rfl

omit [Fintype E] in
omit [FiniteDimensional F2 E] [Fintype (K →ₗ[F2] F2)] in
/-- A good sampled frequency has a valid left preimage.  Neither decoder is
given the proof or the witness used here. -/
theorem good_frequency_preimage (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (σ : K →ₗ[F2] F2) (Φ : H →ₗ[F2] E)
    (hn : σ.comp ι ≠ 0)
    (hc : Φ ∈ frequencyCoset (Z.map π).mkQ ((σ.comp ι).smulRight (π z)))
    (hp : 0 < frequencyWeight (tableSign F σ) Φ) :
    ∃ v ∈ candidates Z z τU, π v = (privateOutput ι τ fallback (σ, Φ)).1 := by
  have hout := privateOutput_eq_contraction F ι τ fallback folded σ Φ hn hp
  apply candidate_preimage Z z π τU τ hτ
  · rw [hout]
    apply contraction_mem_target_coset (Z.map π) (σ.comp ι) (π z) Φ
      (chooseUnit (σ.comp ι) hn) (chooseUnit_spec _ _)
    simpa [frequencyCoset] using hc
  · exact (privateOutput ι τ fallback (σ, Φ)).2

/-- The actual independent policies agree with at least the good Fourier mass
divided by the number of left candidates. -/
theorem conditionalAgreement_ge_mass_div_card (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h) :
    goodCosetMass (Z.map π) (π z) F ι / (candidates Z z τU).card ≤
      conditionalAgreement Z z τU hz π F ι τ fallback := by
  rw [goodCosetMass, Finset.expect_div, conditionalAgreement_eq_sum]
  apply Finset.expect_le_expect
  intro σ _
  have hi := independent_agreement_lower (candidates Z z τU) π
    (fun Φ => (privateOutput ι τ fallback (σ, Φ)).1)
    (frequencyWeight (tableSign F σ))
    (fun Φ => σ.comp ι ≠ 0 ∧
      Φ ∈ frequencyCoset (Z.map π).mkQ ((σ.comp ι).smulRight (π z)))
    (frequencyWeight_nonneg _)
    (fun Φ hΦ hp => good_frequency_preimage Z z τU π F ι τ fallback
      hτ folded σ Φ hΦ.1 hΦ.2 hp)
  by_cases hn : σ.comp ι ≠ 0
  · simpa [hn, Finset.sum_filter] using hi
  · simpa [hn] using hi

end ConditionalAgreement

section SliceBound

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H] [Fintype H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [Fintype E] in
/-- The actual transferred affine-slice agreement supplies the sampled good
Fourier mass, including removal of characters trivial on the hidden kernel. -/
theorem goodCosetMass_lower_from_slice (Q : Submodule F2 E)
    [Fintype (H →ₗ[F2] Q)] [Fintype ((E ⧸ Q) →ₗ[F2] H)]
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) (z' : E) (b : K)
    (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r)
    (hsmall : 1 / (Fintype.card H : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤ 𝔼 A : (E ⧸ Q) →ₗ[F2] H,
      if F (N₀ + A.comp Q.mkQ) = b + ι ((N₀ + A.comp Q.mkQ) z')
      then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) ≤ goodCosetMass Q z' F ι := by
  let good : (K →ₗ[F2] F2) → Prop := fun σ => σ.comp ι ≠ 0
  let : DecidablePred good := fun _ => Classical.propDecidable _
  let C : (K →ₗ[F2] F2) → ℝ := fun σ =>
    sliceCorrelation Q.mkQ N₀ (tableSign F σ) ((σ.comp ι).smulRight z')
  let mass : (K →ₗ[F2] F2) → ℝ := fun σ =>
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ
  have habs : α / 4 ≤ 𝔼 σ : K →ₗ[F2] F2, |C σ| :=
    hagreement.trans (agreement_le_average_abs_correlation Q.mkQ N₀ F ι z' b)
  have hbad : (𝔼 σ : K →ₗ[F2] F2,
      if good σ then (0 : ℝ) else 1) ≤ α / 8 := by
    have ht := trivial_restriction_probability ι hι
    have heq : (𝔼 σ : K →ₗ[F2] F2,
        if good σ then (0 : ℝ) else 1) = 1 / (Fintype.card H : ℝ) := by
      calc
        _ = 𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0 := by
          apply Finset.expect_congr rfl
          intro σ _
          by_cases hn : σ.comp ι = 0 <;> simp [good, hn]
        _ = _ := ht
    exact heq.le.trans hsmall
  have hselected : α / 8 ≤ 𝔼 σ : K →ₗ[F2] F2,
      if good σ then |C σ| else 0 := by
    have hh := remove_bad_characters C good (α / 4) (α / 8)
      (fun σ => sliceCorrelation_tableSign_abs_le_one Q.mkQ N₀ F σ
        ((σ.comp ι).smulRight z')) habs hbad
    linarith
  have hbound := average_coset_mass_lower C mass good
    ((2 : ℝ) ^ (ℓ * r)) (α / 8) (by positivity) (by positivity) hselected
    (by
      intro σ _
      have hcs := sliceCorrelation_sq_le_coset_mass Q.mkQ N₀ (tableSign F σ)
        ((σ.comp ι).smulRight z')
      have hc : ((frequencyCoset Q.mkQ ((σ.comp ι).smulRight z')).card : ℝ) ≤
          (2 : ℝ) ^ (ℓ * r) := by
        exact_mod_cast frequencyCoset_card_le Q ((σ.comp ι).smulRight z') ℓ r hH hQ
      exact hcs.trans (mul_le_mul_of_nonneg_right hc
        (Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _)))
  calc
    _ ≤ 𝔼 σ : K →ₗ[F2] F2, if good σ then mass σ else 0 := hbound
    _ = goodCosetMass Q z' F ι := by
      unfold goodCosetMass
      apply Finset.expect_congr rfl
      intro σ _
      by_cases hn : σ.comp ι = 0 <;> simp [good, mass, hn]

end SliceBound

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H] [Fintype H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 U] [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

theorem conditionalAgreement_from_slice (Z : Submodule F2 U) [Fintype Z]
    (z : U) (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    [Fintype (H →ₗ[F2] Z.map π)] [Fintype ((E ⧸ Z.map π) →ₗ[F2] H)]
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (b : K) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    (hsmall : 1 / (Fintype.card H : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤ 𝔼 A : (E ⧸ Z.map π) →ₗ[F2] H,
      if F (N₀ + A.comp (Z.map π).mkQ) =
        b + ι ((N₀ + A.comp (Z.map π).mkQ) (π z)) then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      conditionalAgreement Z z τU hz π F ι τ fallback := by
  have hQ : Module.finrank F2 (Z.map π) ≤ r :=
    (Submodule.finrank_map_le π Z).trans hZ
  have hmass := goodCosetMass_lower_from_slice (Z.map π) N₀ F ι hι (π z) b
    α hα ℓ r hH hQ hsmall hagreement
  have hcard : ((candidates Z z τU).card : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast candidates_card_le_pow Z z τU r hZ
  have hcardpos : (0 : ℝ) < (candidates Z z τU).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (candidates_nonempty Z z τU hz))
  calc
    _ ≤ goodCosetMass (Z.map π) (π z) F ι / (2 : ℝ) ^ r :=
      div_le_div_of_nonneg_right hmass (by positivity)
    _ ≤ goodCosetMass (Z.map π) (π z) F ι / (candidates Z z τU).card :=
      div_le_div_of_nonneg_left (goodCosetMass_nonneg _ _ _ _) hcardpos hcard
    _ ≤ _ := conditionalAgreement_ge_mass_div_card Z z τU hz π F ι τ fallback hτ folded

end MaxCutGames.Decoder.PrivateStrategy
end

end OAI
