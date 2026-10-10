import OAI.NumberTheory.Ostmann.Characters.CharacterPositiveMassExclusion
import OAI.NumberTheory.Ostmann.Characters.TailCharacterRotation

namespace OAI

/-! # Uniform translated higher-order character bias of the actual residue supports -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def translatedResidueCharacterMean (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) : ℂ :=
  (∑ r ∈ tailSupport A N p, χ ((r : ZMod p) - t)) / ((tailSupport A N p).card : ℂ)

theorem translatedResidueCharacterMean_norm_le_one (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ 1 := by
  unfold translatedResidueCharacterMean
  rw [norm_div, Complex.norm_natCast]
  have hs : ‖∑ r ∈ tailSupport A N p, χ ((r : ZMod p) - t)‖ ≤ (tailSupport A N p).card := by
    calc
      _ ≤ ∑ r ∈ tailSupport A N p, ‖χ ((r : ZMod p) - t)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ tailSupport A N p, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => χ.norm_le_one _)
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)).trans (div_self_le_one _)

noncomputable def higherCharacterBias (A : Set ℕ) (N p : ℕ) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ χ : DirichletCharacter ℂ p, χ ^ 2 ≠ 1 ∧
    ∃ t : ZMod p, r = ‖translatedResidueCharacterMean A N p χ t‖})

theorem higherCharacterBias_nonneg (A : Set ℕ) (N p : ℕ) : 0 ≤ higherCharacterBias A N p := by
  apply le_csSup _ (Set.mem_insert 0 _)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨χ, _, t, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p χ t

theorem higherCharacterBias_le_one (A : Set ℕ) (N p : ℕ) : higherCharacterBias A N p ≤ 1 := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro r (rfl | ⟨χ, _, t, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p χ t

theorem higherCharacterBias_witness (A : Set ℕ) (N p : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : δ < higherCharacterBias A N p) :
    ∃ χ : DirichletCharacter ℂ p, χ ^ 2 ≠ 1 ∧
      ∃ t : ZMod p, δ < ‖translatedResidueCharacterMean A N p χ t‖ := by
  obtain ⟨r, hr, hδr⟩ := exists_lt_of_lt_csSup (Set.insert_nonempty 0 _) h
  rcases hr with rfl | ⟨χ, hχ, t, rfl⟩
  · exact (not_lt_of_ge hδ hδr).elim
  · exact ⟨χ, hχ, t, hδr⟩

theorem PublishedProgressionInput.eventual_large_character_bias_mass
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β c δ : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      (∀ p ∈ P, δ < higherCharacterBias Aset N₀ p) →
      (∑ p ∈ P, (p : ℝ)⁻¹) < c * L := by
  classical
  let ε := min (δ / 4) 1
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : 2 * ε ≤ δ / 2 := by
    have hh := min_le_left (δ / 4) (1 : ℝ)
    change 2 * min (δ / 4) 1 ≤ δ / 2
    linarith only [hh]
  have hcut := P0.eventual_positive_character_mass_exclusion hsize hM hAset hBset hsum N₀ hN₀
    α β (c / 4) ε hα hαβ (by positivity) hε hε1
  filter_upwards [hcut] with L hcut P hP hrange hbias
  by_contra hm
  have hmass : c * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := le_of_not_gt hm
  have hchoice : ∀ p : ℕ, ∃ χ : DirichletCharacter ℂ p, ∃ t : ZMod p,
      p ∈ P → χ ^ 2 ≠ 1 ∧ δ < ‖translatedResidueCharacterMean Aset N₀ p χ t‖ := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨χ, hχ, t, ht⟩ := higherCharacterBias_witness Aset N₀ p hδ.le (hbias p hp)
      exact ⟨χ, t, fun _ => ⟨hχ, ht⟩⟩
    · exact ⟨1, 0, fun hh => (hp hh).elim⟩
  choose χ center hchoice using hchoice
  obtain ⟨ζ, E, hζ, hEP, hEmass, href⟩ := common_positive_tail_character_rotation Aset N₀ P χ center δ
    (fun p hp => (hchoice p hp).2.le)
  apply hcut E (fun p hp => hP p (hEP hp)) (fun p hp => hrange p (hEP hp))
    (by nlinarith only [hmass, hEmass]) χ (fun p hp => (hchoice p (hEP hp)).1) center ζ hζ
  exact fun p hp => hεδ.trans (href p hp)

end Ostmann

end OAI
