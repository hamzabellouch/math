import OAI.NumberTheory.Ostmann.Characters.CharacterHigherBias

namespace OAI

/-! # Proposition 4.1: maximal translated higher-order bias has harmonic mass o(L) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

noncomputable def closedLogLogPrimeBand (α β L : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (Real.exp (β * L))⌋₊).filter
    (fun p => α * L ≤ Real.log (Real.log (p : ℝ)))

theorem mem_closedLogLogPrimeBand_iff (α β L : ℝ) (p : ℕ) :
    p ∈ closedLogLogPrimeBand α β L ↔ p.Prime ∧
      α * L ≤ Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L := by
  simp only [closedLogLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    refine ⟨hprime, hlo, ?_⟩
    have hpp : (p : ℝ) ≤ Real.exp (Real.exp (β * L)) :=
      (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans
        (Nat.floor_le (Real.exp_nonneg _))
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast hprime.one_lt
    apply (Real.log_le_iff_le_exp (Real.log_pos hp1)).mpr
    exact (Real.log_le_iff_le_exp hp0).mpr hpp
  · rintro ⟨hprime, hlo, hhi⟩
    exact ⟨⟨Nat.le_floor (prime_of_loglog_upper p hprime _ hhi), hprime⟩, hlo⟩

noncomputable def higherCharacterBandMass (A : Set ℕ) (N : ℕ) (α β L : ℝ) : ℝ :=
  ∑ p ∈ closedLogLogPrimeBand α β L, (p : ℝ)⁻¹ * higherCharacterBias A N p

theorem PublishedProgressionInput.eventual_higher_character_mass_bound
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L ≤ Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      (∑ p ∈ P, (p : ℝ)⁻¹ * higherCharacterBias Aset N₀ p) ≤ ε * L := by
  classical
  let C := (Real.exp 1 + 1) * (β - α / 2 + 1)
  have hαhalf : 0 < α / 2 := by positivity
  have hhalfβ : α / 2 < β := by linarith only [hα, hαβ]
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hexc := P0.eventual_large_character_bias_mass hsize hM hAset hBset hsum N₀ hN₀
    (α / 2) β (ε / 2) δ hαhalf hhalfβ (by positivity) hδ
  filter_upwards [hexc, eventual_character_prime_total hM (α / 2) β hαhalf hhalfβ,
    eventually_gt_atTop (0 : ℝ)] with L hexc htotal hL P hP hrange
  have hrange' (p : ℕ) (hp : p ∈ P) : (α / 2) * L < Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) ≤ β * L := by
    refine ⟨?_, (hrange p hp).2⟩
    have hh : (α / 2) * L < α * L := mul_lt_mul_of_pos_right (by linarith only [hα]) hL
    exact hh.trans_le (hrange p hp).1
  let E := P.filter (fun p => δ < higherCharacterBias Aset N₀ p)
  have hEmass : (∑ p ∈ E, (p : ℝ)⁻¹) < (ε / 2) * L :=
    hexc E (fun p hp => hP p (Finset.mem_filter.mp hp).1)
      (fun p hp => hrange' p (Finset.mem_filter.mp hp).1)
      (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hPmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ C * L := by
    have hh := htotal P hP hrange'
    rw [Finset.sum_coe_sort P (fun p : ℕ => (p : ℝ)⁻¹)] at hh
    exact hh
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (p : ℝ)⁻¹ * higherCharacterBias Aset N₀ p ≤
        (p : ℝ)⁻¹ * δ + if p ∈ E then (p : ℝ)⁻¹ else 0 := by
    by_cases he : p ∈ E
    · rw [ite_eq_left he]
      have hh := mul_le_mul_of_nonneg_left (higherCharacterBias_le_one Aset N₀ p)
        (show 0 ≤ (p : ℝ)⁻¹ by positivity)
      have hpos : 0 ≤ (p : ℝ)⁻¹ * δ := by positivity
      simpa only [mul_one] using hh.trans (le_add_of_nonneg_left hpos)
    · rw [ite_eq_right he, add_zero]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_of_not_gt (fun hh => he (Finset.mem_filter.mpr ⟨hp, hh⟩))
  have hsum := Finset.sum_le_sum hpoint
  have hEsum : (∑ p ∈ P, if p ∈ E then (p : ℝ)⁻¹ else 0) = ∑ p ∈ E, (p : ℝ)⁻¹ := by
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp only [E, Finset.mem_filter, and_self_left]
  rw [Finset.sum_add_distrib, hEsum, ← Finset.sum_mul] at hsum
  have hδC : C * δ = ε / 2 := by dsimp [δ]; field_simp
  have hsmall := mul_le_mul_of_nonneg_right hPmass hδ.le
  have heq : C * L * δ = (ε / 2) * L := by rw [mul_right_comm, hδC]
  rw [heq] at hsmall
  linarith only [hsum, hsmall, hEmass]

/-- The manuscript's Proposition 4.1, with the maximum represented by the
supremum over all translated characters whose square is nonprincipal. -/
theorem PublishedProgressionInput.higher_character_decorrelation
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    (fun L => higherCharacterBandMass Aset N₀ α β L) =o[atTop] (fun L : ℝ => L) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [P0.eventual_higher_character_mass_bound hsize hM hAset hBset hsum N₀ hN₀
    α β ε hα hαβ hε, eventually_ge_atTop (0 : ℝ)] with L hbound hL
  have hnonneg : 0 ≤ higherCharacterBandMass Aset N₀ α β L :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (by positivity) (higherCharacterBias_nonneg _ _ _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs, abs_of_nonneg hL]
  exact hbound _ (fun p hp => ((mem_closedLogLogPrimeBand_iff α β L p).mp hp).1)
    (fun p hp => ((mem_closedLogLogPrimeBand_iff α β L p).mp hp).2)

end Ostmann

end OAI
