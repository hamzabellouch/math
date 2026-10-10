import OAI.NumberTheory.Ostmann.Construction.ConstructedBinnedCharacterPriors
import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedEndpointContradiction

namespace OAI

/-! # Tested original shells force the finite character contradiction -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.eventual_tested_character_shell_contradiction
    (P0 : PublishedProgressionInput) (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
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
    (ψ : 𝓢(ℝ, ℂ)) (_hψ : ∀ x, 0 ≤ (ψ x).re) (_hreal : ∀ x, (ψ x).im = 0)
    (_heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (_hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (_hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0),
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
    ∀ E : Finset ℕ,
    Real.sqrt (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) *
      Real.exp (-A * m) ≤ E.card →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ))).re) →
    (∀ x ∈ E, ∀ i, δ ≤ ‖∑ p : P, (primeSubsetPrior P (Q i) p : ℂ) *
      χ p ((x : ZMod p) - center p)‖) →
    (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * (n + 1) →
      c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ →
      (∀ p ∈ loglogShell P (Ulate + j),
        Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ (n + 1) * τ) / 4) →
      δ * (∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ *
          (ζ * χ p ((x : ZMod p) - center p)).re) →
    (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
      ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - center p)).re) →
    False := by
  obtain ⟨C₀, hC₀, hconstruct⟩ := P0.constructed_binned_character_priors c₀ δ hc₀ hδ hδ1
  refine ⟨C₀, hC₀, ?_⟩
  intro n hn hC₀n a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
    β Ccode A ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong
    hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    hβ hβgap hβmass hcover hCcode hArate hBrate hγδ ψ hψ hreal heven hψK hsupp
  have hsize : ((characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) : ℝ) ≤ z := by
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2))
    have hmul := mul_nonneg (show 0 ≤ 4 * Cmass - 1 by linarith only [hβmass, hβ]) hnonneg
    nlinarith only [hmul, hbudgetAll]
  have hchoose := hconstruct (n + 1) hn hC₀n B z α β Ccode hB hz.le hα hβ hCcode hsize
  have hfalse := eventual_constructed_character_endpoint_contradiction n
    a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε c₀ δ β
    ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong hBpos ha1
    hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    hc₀ hδ hβ hβgap hβmass hcover ψ hψ hreal heven hψK hsupp
  filter_upwards [hchoose, hfalse, eventual_character_length_bounds z hz] with L hchoose hfalse hlength
  intro m Ulate τ bmax P U T₀ hP Q D hUL hUβ hUτ hτU hτ hτ2 hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate hD hkD hPD hrich
    u hu husep hsmall hbig huτ hmass χ hχ center ζ hζ E hE hsE hwordMean htest hmean
  have hEne : E.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < E.card :=
      (mul_pos (Real.sqrt_pos.2 (Real.exp_pos _)) (Real.exp_pos _)).trans_le hE
    exact_mod_cast hp
  obtain ⟨bin, hbinlo, hbinhi, hbinpos, x₀, hx₀, ac, w, hlen, S, hSE, hSne,
    hScard, hsub, hprob, hmass', hmeans, hword⟩ :=
    hchoose Ulate τ m D hUL hUβ hUτ hτU hτ hτ2 hlength.2.2.2.1 hlength.2.2.2.2
      hlength.2.1 hlength.2.2.1 hD hkD P
      (fun x p => χ p ((x : ZMod p) - center p)) ζ E hEne hP hPD hζ
      (fun _ _ p _ => (χ p).norm_le_one _)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hrich) htest bmax U T₀ Q hzero hsucc hsizeτ
      htoplog hbulklog hwordMean u hu huτ hmass hmean
      (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) A (Real.exp_pos _) hE
  apply hfalse Ulate τ bmax P U T₀ hP Q hUL hUβ hUτ hτU hτ hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate u
    (fun j => (hu j).2) husep hsmall hbig huτ
    (fun p => ζ * χ p ((x₀ : ZMod p) - center p)) ac bin hbinlo hbinhi hbinpos w hlen
    χ hχ center S (Real.exp (-Bword * m))
  · exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hArate, Nat.cast_nonneg (α := ℝ) m]))
      (Real.sqrt_nonneg _)).trans hScard
  · exact le_rfl
  · exact fun x hx => hsE x (hSE hx)
  · intro x hx
    exact (Real.exp_le_exp.mpr (by nlinarith only [hBrate, Nat.cast_nonneg (α := ℝ) m])).trans
      (hword x hx)
  · intro x hx v i
    exact hγδ.trans (hmeans x hx v i)

end Ostmann

end OAI
