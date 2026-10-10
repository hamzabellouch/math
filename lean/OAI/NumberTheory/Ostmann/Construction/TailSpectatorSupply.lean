import OAI.NumberTheory.Ostmann.Characters.AllCharacterDecorrelation
import OAI.NumberTheory.Ostmann.Construction.TailBandBalance

namespace OAI

/-! # Spectator primes for the actual normalized tail transforms -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_tail_spectator_supply
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (α β ε c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) (hc : 0 < c)
    (hsmall : (fun L => tailCharacterBandMass A N α β L) =o[atTop] (fun L : ℝ => L)) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      ∃ Q ⊆ P, (∑ p ∈ P, (p : ℝ)⁻¹) - c * L ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
        ∀ p ∈ Q, 3 ≤ p ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3 ∧
          tailCharacterBias A N p ≤ ε / 2 ∧
          ∀ hp : p.Prime,
            @MixedFourierBound p ⟨hp⟩
              (@normalizedResidueTransform p ⟨hp.ne_zero⟩ (tailDensityMask A N p)) ε := by
  classical
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgrowth : Tendsto (fun L : ℝ => Real.exp (Real.exp (α * L))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα))
  filter_upwards [h.eventual_unbalanced_band_mass hsize hM hA hB N hN α β (c / 2)
    hα hβ (by positivity), eventual_bad_tail_character_mass A N α β δ (c / 2)
      hδ (by positivity) hsmall,
    hgrowth.eventually (eventually_ge_atTop (max 3 ((3 / ε) ^ 2)))]
    with L hbal hchar hlarge P hP
  let balanced := fun p => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
    residueDensity (tailDensityMask A N p) ≤ 2 / 3
  let Q := P.filter (fun p => balanced p ∧ tailCharacterBias A N p ≤ δ)
  have hmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) + c * L := by
    have hpwise (p : ℕ) (_hp : p ∈ P) : (p : ℝ)⁻¹ ≤
        (if balanced p ∧ tailCharacterBias A N p ≤ δ then (p : ℝ)⁻¹ else 0) +
        (if ¬ balanced p then (p : ℝ)⁻¹ else 0) +
        (if δ < tailCharacterBias A N p then (p : ℝ)⁻¹ else 0) := by
      by_cases hb : balanced p <;> by_cases hd : tailCharacterBias A N p ≤ δ
      · simp only [hb, hd, and_self, ite_true, not_true_eq_false, ite_false, not_lt.mpr hd, add_zero]
        exact le_rfl
      · simp only [hb, hd, and_false, ite_false, not_true_eq_false, lt_of_not_ge hd, ite_true, zero_add]
        exact le_rfl
      · simp only [hb, hd, false_and, ite_false, not_false_eq_true, ite_true, not_lt.mpr hd, add_zero, zero_add]
        exact le_rfl
      · simp only [hb, hd, false_and, ite_false, not_false_eq_true, ite_true, lt_of_not_ge hd, zero_add]
        exact le_add_of_nonneg_right (by positivity)
    have hs := Finset.sum_le_sum hpwise
    simp only [Finset.sum_add_distrib] at hs
    rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter] at hs
    have hb := hbal P hP
    have hh := hchar P hP
    change (∑ p ∈ P.filter (fun p => ¬balanced p), (p : ℝ)⁻¹) ≤ _ at hb
    change (∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), (p : ℝ)⁻¹) ≤ _ at hh
    change (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) + _ + _ at hs
    linarith only [hs, hb, hh]
  refine ⟨Q, Finset.filter_subset _ _, by linarith only [hmass], ?_⟩
  intro p hp
  obtain ⟨hpP, hbp, hbias⟩ := Finset.mem_filter.mp hp
  have hband := (mem_closedLogLogPrimeBand_iff α β L p).mp (hP hpP)
  have hpbound := prime_of_loglog_lower p hband.1 _ hband.2.1
  have hp3 : 3 ≤ p := by exact_mod_cast (le_max_left _ _).trans (hlarge.trans hpbound)
  refine ⟨hp3, hbp.1, hbp.2, by simpa only [δ] using hbias, ?_⟩
  intro hpp
  let : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hsq : (3 / ε) ^ 2 ≤ (p : ℝ) := (le_max_right _ _).trans (hlarge.trans hpbound)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity : 0 ≤ 3 / ε)] at hsqrt
  have hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
    have hh := (div_le_iff₀ hε).mp hsqrt
    linarith only [hh]
  have htwobias : 2 * tailCharacterBias A N p ≤ ε := by
    dsimp only [δ] at hbias
    linarith only [hbias]
  intro χ a
  exact (tail_transform_mixed_bound A N p hp2 hbp.1 hbp.2 χ a).trans
    (max_le hprincipal htwobias)

/-- The spectator supply at any fixed admissible tail cutoff, with all
character smallness derived from the cited published inputs. -/
theorem EventuallyPrimeSumset.tail_spectator_supply
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (α β ε c : ℝ) (hα : 0 < α) (hαβ : α < β) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      ∃ Q ⊆ P, (∑ p ∈ P, (p : ℝ)⁻¹) - c * L ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
        ∀ p ∈ Q, 3 ≤ p ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3 ∧
          tailCharacterBias A N p ≤ ε / 2 ∧
          ∀ hp : p.Prime,
            @MixedFourierBound p ⟨hp⟩
              (@normalizedResidueTransform p ⟨hp.ne_zero⟩ (tailDensityMask A N p)) ε := by
  obtain ⟨cψ, ψ, hcψ, hreal, hψ0, hψ1, hsupp⟩ := exists_positive_fourier_cutoff
  have hquad := closedQuadraticBandMass_isLittleO_of_halfopen A N
    (quadraticBandMass_isLittleO hBonami P0 H hSiegel sieve hsize hA hB h N hN C hM
      cψ 3 hcψ le_rfl ψ hreal hψ0 hψ1 hsupp)
  exact eventual_tail_spectator_supply hsize hM.lower h hA hB N hN α β ε c
    hα (hα.trans hαβ) hε hc
    (P0.all_character_decorrelation hsize hM hA hB h N hN hquad α β hα hαβ)

end Ostmann

end OAI
