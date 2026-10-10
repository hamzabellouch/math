import OAI.Computability.UniqueGames.Analysis.ParityLemmas
import OAI.Computability.UniqueGames.Decoding.AdviceFibersLemmas
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI

section

/-!
# Actual private response laws for Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Foundations.Games
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
    simpa [F2, UniqueGamesTheorem.Integration.BinaryLinear.F2, ZMod.card] using
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
  exact ⟨h, (UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases _).resolve_left hh⟩

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

omit [Fintype E] [FiniteDimensional F2 E] [FiniteDimensional F2 H] in
theorem goodCosetMass_nonneg (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) :
    0 ≤ goodCosetMass Q z' F ι := by
  apply Finset.expect_nonneg
  intro σ _
  split
  · exact Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _
  · exact le_rfl

omit [Fintype E] [FiniteDimensional F2 E] [Fintype (K →ₗ[F2] F2)] in
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

section FinalConditionalBound

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

end FinalConditionalBound

end UniqueGamesTheorem.Decoder.PrivateStrategy

end

end

section

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

namespace UniqueGamesTheorem.Decoder.SurrogateFibers

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier
open PositiveMultiplier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

/-- Uniform shortcode sampling; neither nonzero-factor conditioning nor
rank-one-matrix-uniform sampling is substituted for its two independent factors. -/
def shortcodeAcceptance (f : (E →ₗ[F2] K) → C) : ℝ := by
  classical
  exact 𝔼 M, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
    if f M = f (M + l.smulRight a) then (1 : ℝ) else 0

omit [Fintype K] [Fintype W] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)] [Fintype (E →ₗ[F2] K × W)] in
theorem product_perturbation (M : E →ₗ[F2] K) (T : E →ₗ[F2] W)
    (l : E →ₗ[F2] F2) (a : K) :
    M.prod T + l.smulRight ((LinearMap.inl F2 K W) a) =
      (M + l.smulRight a).prod T := by
  ext x <;> simp

theorem surrogate_acceptance_eq_fiber_average
    (label : (E →ₗ[F2] K × W) → C) :
    equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 T : E →ₗ[F2] W,
        shortcodeAcceptance (fun M : E →ₗ[F2] K => label (M.prod T)) := by
  classical
  have hsampling : equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 X : E →ₗ[F2] K × W, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight ((LinearMap.inl F2 K W) a)) then
          (1 : ℝ) else 0 := by
    unfold equalityAcceptance
    apply Finset.expect_congr rfl
    intro X _
    rw [subspaceLaw_sum, Fintype.expect_eq_sum_div_card]
    ring
  rw [hsampling, SplitMaps.expect_codomain_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro T _
  unfold shortcodeAcceptance
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro l _
  rw [product_perturbation]

end
end UniqueGamesTheorem.Decoder.SurrogateFibers

end

end OAI
