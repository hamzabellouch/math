import OAI.NumberTheory.Ostmann.Characters.CharacterTestedShellContradiction
import OAI.NumberTheory.Ostmann.Construction.TypicalCharacterShells

namespace OAI

/-! # Actual summand tails supply the endpoints in the character contradiction -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.eventual_tail_character_shell_contradiction
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensLowerBound CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p)) (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 20000 ≤ n + 1 →
      C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
    ∀
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε β Ccode A : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hz : 1 < z)
    (_hCmass : 0 < Cmass) (_hCtotal : 0 ≤ Ctotal) (_hc : 1 ≤ c)
    (_hs : 0 < s) (_hγ : 0 < γ) (_hH : 0 ≤ H) (_hα : 0 < α)
    (_hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (_hB : 0 ≤ B)
    (_hB₁ : 0 ≤ B₁) (_hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (_hBstrong : 2 * B₁ + 5 ≤ B) (_hBpos : 1 ≤ B) (_ha1 : a ≤ 1)
    (_hβg : 0 < βg) (_hγw : 0 ≤ γw) (_hαw : α < βw) (_hsw : γs < βw)
    (_hαa : α < βa) (_hwa : γw < βa) (_hwg : γw ≤ βg)
    (_hβw : βw < νw) (_hβa : βa < νa) (_hε : 0 < ε)
    (_hbudgetAll : 4 * Cmass *
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
    (_hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (_hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (_hβ : 0 ≤ β) (_hβgap : β < βg)
    (_hβmass : β + 1 ≤ Cmass)
    (_hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
    (_hCcode : 0 ≤ Ccode) (_hArate : A + (β + 1) + 4 * Ccode + 4 ≤ Aend)
    (_hBrate : (β + 1) - 2 * Real.log δ ≤ Bword) (_hγδ : γ ≤ δ / 2)
    (_hAtail : 3 * β + 1 ≤ A) (_hcb : c₀ ≤ b)
    (ψ : 𝓢(ℝ, ℂ)) (_hψ : ∀ x, 0 ≤ (ψ x).re) (_hreal : ∀ x, (ψ x).im = 0)
    (_heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (_hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (_hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (_hψlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, s ≤ (ψ t).re),
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ) (D : ℕ),
    α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
    Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) → (∀ i, Q i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (l h : ℝ),
    (∀ p ∈ U, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h) →
    h ≤ Ulate →
    (D + 1 : ℕ) ≤ Real.exp (Ccode * L) → 5 * (n + 1) ≤ D →
    (∀ p ∈ P, primeLogIndex p ≤ D) →
    (∀ u v : ℝ, Ulate ≤ u → v ≤ Ulate + 5 * (n + 1) →
      ((n + 1 : ℕ) : ℝ) / 10000 ≤ v - u →
      ∃ j : ℕ, u ≤ Ulate + j ∧ Ulate + j + 1 ≤ v ∧
        c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) →
    ∀ u : Fin (n + 1) × Bool → ℝ,
    (∀ j, α * L ≤ u j ∧ u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
    (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
    (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
    (∀ j, c₀ ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
    ∀ X : ℕ, (X : ℝ) = Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ) →
    (∀ p ∈ P, 2 * δ ≤ residueTestMean (tailSupport Aset N₀ p)
      (realTranslatedCharacterTest χ center ζ p)) → False := by
  obtain ⟨C₀, hC₀, htested⟩ := P0.eventual_tested_character_shell_contradiction c₀ δ hc₀ hδ hδ1
  refine ⟨C₀, hC₀, ?_⟩
  intro n hn hC₀n a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
    β Ccode A ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong
    hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    hβ hβgap hβmass hcover hCcode hArate hBrate hγδ hAtail hcb ψ hψ hreal heven hψK hsupp hψlower
  let Ck : ℝ := 1000 * (4 : ℝ) ^ (n + 1)
  let Dlog : ℝ := Real.log Ck + 2 * ((n + 1 : ℕ) : ℝ) / 10000
  have hCk : 0 < Ck := by dsimp [Ck]; positivity
  obtain ⟨atail, hatail, L₀, t₀, htail⟩ := eventual_typical_character_shells hsize hM hAset hBset
    hsum N₀ hN₀ (n + 1) α β Dlog (2 * δ) c₀ hα (by positivity) hc₀
  have hcontra := htested n hn hC₀n a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K
    βg βw γs βa γw νw νa ε β Ccode A ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB
    hB₁ hB₁eq hBstrong hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll
    hgapFinal hentropy hβ hβgap hβmass hcover hCcode hArate hBrate hγδ ψ hψ hreal heven hψK hsupp
  have htlarge : ∀ᶠ L : ℝ in atTop, t₀ ≤ Ck * Real.exp (α * L) :=
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)).const_mul_atTop hCk).eventually
      (eventually_ge_atTop t₀)
  have hbulklarge : ∀ᶠ L : ℝ in atTop, c₀ ≤ a * L :=
    (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop c₀)
  filter_upwards [hcontra, eventual_character_tail_count_rate atail β Dlog hatail hβ,
    eventual_character_length_bounds z hz, htlarge, hbulklarge, eventually_ge_atTop L₀]
    with L hcontra hrate hlength htlarge hbulklarge hL₀
  intro m Ulate τ bmax P U T₀ hP Q D hUL hUβ hUτ hτU hτ hτ2 hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate hD hkD hPD hrich
    u hu husep hsmall hbig huτ hmass χ hχ center ζ hζ X hX href
  let T : ℝ := Ck * τ
  have hT : 0 < T := mul_pos hCk hτ
  have hτlo : Real.exp (α * L) ≤ τ :=
    (Real.exp_le_exp.mpr (hUL.trans hUτ)).trans_eq (Real.exp_log hτ)
  have ht₀ : t₀ ≤ T := htlarge.trans (mul_le_mul_of_nonneg_left hτlo hCk.le)
  have hlogT : Real.log T ≤ β * L + Dlog := by
    rw [show T = Ck * τ from rfl, Real.log_mul hCk.ne' hτ.ne']
    dsimp only [Dlog]
    linarith only [hUβ, hτU]
  have hscale : 4 * τ ≤ T / 4 := by
    have hp : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hp hτ.le
    dsimp [T, Ck]
    nlinarith only [hh, hτ]
  have hUP : U ⊆ P := by
    have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 1) hlength.2.1
    simpa only [hsucc] using hQP (Fin.succ ⟨0, hmpos⟩)
  have hTP : T₀ ⊆ P := by simpa only [hzero] using hQP 0
  have hmin (p : ℕ) (hp : p ∈ P) : Real.exp (α * L) ≤ Real.log (p : ℝ) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast (hP p hp).pos)).mpr (hPrange p hp).1
  have hUcut : ∀ p ∈ U, Real.log (p : ℝ) ≤ T / 4 := by
    intro p hp
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hP p (hUP hp)).one_le)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hlength.2.1
    have hh := mul_le_mul_of_nonneg_right hm1 hlog0
    have hh' := mul_le_mul_of_nonneg_left (hbulklog p hp) (Nat.cast_nonneg (α := ℝ) m)
    have hτp : Real.log (p : ℝ) ≤ τ := by nlinarith only [hh, hh', hsizeτ]
    exact hτp.trans (by linarith only [hscale, hτ])
  have hTcut : ∀ p ∈ T₀, Real.log (p : ℝ) ≤ T / 4 := by
    intro p hp
    exact (htoplog p hp).2.trans (by linarith only [hscale, hτ])
  have hucut : ∀ j p, p ∈ loglogShell P (u j) → Real.log (p : ℝ) ≤ T / 4 := by
    rintro ⟨j, b⟩ p hp
    have hh := (character_top_shell_log_bounds P hP (u (j, b)) p hp).2
    have ha' := huτ j
    cases b <;> apply hh.trans <;>
      linarith only [ha', hscale, Real.exp_pos (u (j, false)), Real.exp_pos (u (j, true))]
  obtain ⟨E, hEtail, hEcard, hgood⟩ := htail L T hL₀ ht₀ hlogT X hX P U T₀ Ulate u χ center ζ
    hζ hP hmin hUP hTP (hbulklarge.trans hbulk) (hcb.trans htop) hmass hUcut hTcut hucut href
  have hcount := hrate m T E hlength.2.2.1 hT hlogT hEcard
  have hEA : Real.sqrt (Real.exp T) * Real.exp (-A * m) ≤ E.card := by
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hAtail, Nat.cast_nonneg (α := ℝ) m]))
      (Real.sqrt_nonneg _)).trans hcount
  have hsE : ∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp T)).re := by
    intro x hx
    have hxX := ((mem_summandTail Aset _ _ x).mp (hEtail hx)).2.2
    have hxR : (x : ℝ) ≤ Real.exp T := by rw [← hX]; exact_mod_cast hxX
    exact hψlower _ ⟨div_nonneg (Nat.cast_nonneg x) (Real.exp_nonneg T),
      (div_le_one (Real.exp_pos T)).mpr hxR⟩
  have hgood' := hgood
  simp only [show 2 * δ / 2 = δ by ring] at hgood'
  apply hcontra Ulate τ bmax P U T₀ hP Q D hUL hUβ hUτ hτU hτ hτ2 hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate hD hkD hPD hrich u hu
    husep hsmall hbig huτ hmass χ hχ center ζ hζ E hEA hsE
  · intro x hx i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [hzero] using (hgood' x hx).2.1
    · simpa only [hsucc] using (hgood' x hx).1
  · exact fun x hx => (hgood' x hx).2.2.2
  · exact fun x hx => (hgood' x hx).2.2.1

end Ostmann

end OAI
