import OAI.NumberTheory.Ostmann.Characters.CharacterConcreteBandContradiction
import OAI.NumberTheory.Ostmann.Characters.CharacterBandSelection
import OAI.NumberTheory.Ostmann.Characters.CharacterFixedParameters

namespace OAI

/-! # Positive harmonic mass of uniformly biased higher-order characters is impossible -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.eventual_positive_character_mass_exclusion
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β c δ : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      c * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
      (∀ p ∈ P, 2 * δ ≤ residueTestMean (tailSupport Aset N₀ p)
        (realTranslatedCharacterTest χ center ζ p)) → False := by
  classical
  obtain ⟨q, hq, H, hselect⟩ := exists_character_band_selection hM α β c hα hαβ hc
  let c₀ := c / (32 * (β - α))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  let a := min (c / (2 * q)) 1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 := min_le_right _ _
  obtain ⟨C₀, hC₀, hconcrete⟩ := P0.concrete_character_band_contradiction
    hsize hM hAset hBset hsum N₀ hN₀ α β c₀ δ hα hαβ hc₀ hδ hδ1
  obtain ⟨Kmin, hKmin⟩ := exists_nat_ge
    (max 40000 (64 * (Real.exp 1 + 1) * 10000 / (c / (2 * (β - α)))))
  have hdensity : 0 < c / (2 * (β - α)) := by positivity
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨_, _, B, hB, hstrong, hrepeat, hanchor, K, hKminK, hKlarge, hdepth⟩ :=
    exists_character_fixed_parameters a β c₀ δ ((Real.exp 1 + 1) * (β - α + 1)) C₀
      hβ hc₀ hδ hδ1 hC₀ Kmin
  have hKminR : (Kmin : ℝ) ≤ K := by exact_mod_cast hKminK
  have hK40000 : (40000 : ℝ) ≤ K := (le_max_left _ _).trans (hKmin.trans hKminR)
  have hKε : 4 ≤ (1 / 10000 : ℝ) * K := by linarith only [hK40000]
  have hKmass : 64 * (Real.exp 1 + 1) ≤ (c / (2 * (β - α))) * (1 / 10000 : ℝ) * K := by
    have hh := (le_max_right _ _).trans (hKmin.trans hKminR)
    have hh' := (div_le_iff₀ hdensity).mp hh
    nlinarith only [hh']
  let Triple := {t : Fin q × Fin q × Fin q // t.1.val + 1 < t.2.1.val ∧ t.2.1.val + 1 < t.2.2.val}
  have hfinite (h : Fin (H + 1)) (t : Triple) := by
    let d := K * 200000 ^ h.val
    have hKd : K ≤ d := Nat.le_mul_of_pos_right K (pow_pos (by decide) _)
    have hd1 : 1 ≤ d := by omega
    have hdn : d - 1 + 1 = d := Nat.sub_add_cancel hd1
    obtain ⟨hz, hC, hentropy, hbudget⟩ := hdepth d hKd
    have hdlarge : 20000 ≤ d - 1 + 1 := by omega
    exact hconcrete q (d - 1) hq hdlarge (by simpa only [hdn] using hC)
      t.val.1 t.val.2.1 t.val.2.2 t.property.1 t.property.2
      a (cellRoleScale d) B ha ha1 hz hB hstrong hrepeat hanchor hentropy
      (by simpa only [hdn, show d - 1 + 2 = d + 1 by omega] using hbudget)
  have hall := eventually_all.mpr (fun h : Fin (H + 1) =>
    eventually_all.mpr (fun t : Triple => hfinite h t))
  filter_upwards [hall, hselect K (by omega) hKε hKmass, eventually_ge_atTop (0 : ℝ)]
    with L hall hselect hL
  intro P hP hrange hmass χ hχ center ζ hζ href
  have hmass' : c * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
      (fun p => (p : ℝ)⁻¹) (α * L) (β * L) := by
    convert hmass using 1
    unfold weightedIntervalMass
    rw [Finset.filter_eq_self.mpr hrange]
  obtain ⟨i, j, k, hij, hjk, hbulk, us, huslo, hushi, hsmall, h, hh, U, hUlo, hUhi, hrich⟩ :=
    hselect P hP hmass'
  let d := K * 200000 ^ h
  have hd1 : 1 ≤ d := by
    have hKd : K ≤ d := Nat.le_mul_of_pos_right K (pow_pos (by decide) _)
    omega
  have hdn : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨v, hvlo, hvhi, hvmass⟩ := hrich
    (U + (d : ℝ) / 10000) (U + 2 * (d : ℝ) / 10000)
    (by linarith only [hdpos]) (by linarith only [hdpos]) (by linarith only [])
  have hpoint (x : ℕ) : characterBandPoint α β q x * L + ((β - α) / q) * L =
      characterBandPoint α β q (x + 1) * L := by
    rw [characterBandPoint_succ]
    ring
  have hbulk' : a * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
      (fun p => (p : ℝ)⁻¹) (characterBandPoint α β q j.val * L)
        (characterBandPoint α β q (j.val + 1) * L) := by
    have hle := mul_le_mul_of_nonneg_right (min_le_left (c / (2 * q)) 1) hL
    have he : c / (2 * q) * L = c * L / (2 * q) := by ring
    rw [he] at hle
    exact hle.trans (by simpa only [hpoint] using hbulk)
  have hcut := hall ⟨h, by omega⟩ ⟨(i, j, k), hij, hjk⟩
  dsimp only [hfinite] at hcut
  have hdnK : K * 200000 ^ h - 1 + 1 = K * 200000 ^ h := hdn
  have hcastK : ((K * 200000 ^ h - 1 : ℕ) : ℝ) + 1 = (K * 200000 ^ h : ℕ) := by
    exact_mod_cast hdnK
  simp only [hdnK, hcastK] at hcut
  refine hcut P hP hrange hbulk' us U (U + v) huslo ?_ hUlo ?_ hvlo hvhi hsmall hvmass
    hrich χ hχ center ζ hζ href
  · simpa only [hpoint] using hushi
  · simpa only [hpoint] using hUhi

end Ostmann

end OAI
