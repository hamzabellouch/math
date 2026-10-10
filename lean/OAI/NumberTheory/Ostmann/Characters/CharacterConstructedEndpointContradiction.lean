import OAI.NumberTheory.Ostmann.Characters.CharacterUniformEndpoint
import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedCounts
import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedRanges
import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedTargetCutoff

namespace OAI

/-! # The endpoint contradiction for the actual constructed character cells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_constructed_character_endpoint_contradiction (n : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε c₀ δ β : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass *
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hβ : 0 ≤ β) (hβgap : β < βg)
    (hβmass : β + 1 ≤ Cmass)
    (hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ),
    α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
    Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ →
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
    h ≤ Ulate → ∀ u : Fin (n + 1) × Bool → ℝ,
    (∀ j, u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
    (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
    (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
    ∀ (F₀ : ℕ → ℂ) (ac : ∀ j, CharacterAnchorCell P F₀ c₀ δ (u j))
      (bin : Fin (⌊4 * τ⌋₊ + 1)), τ / 2 ≤ (bin.val : ℝ) →
    (bin.val : ℝ) ≤ 4 * τ → 0 < bin.val →
    ∀ w : ∀ j, CharacterTargetWord P F₀ c₀ δ Ulate (n + 1)
      (characterConstructedTargets (n + 1) bin.val
        (1000 * (4 : ℝ) ^ (n + 1) * τ) B z m (fun j => (ac j).index) j),
    (∀ j, 0 < (w j).indices.length) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℕ) (ρ : ℝ),
    Real.sqrt (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) *
      Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ))).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (characterPrimeCells w (characterAnchorCells ac) v i) p : ℂ) *
        χ p ((x : ZMod p) - center p)‖) →
    False := by
  let N := characterTargetLabelBound c₀ δ (n + 1)
  let Bnb := N + (n + 2) + (n + 2)
  have hend := eventual_uniform_character_endpoint_contradiction n N Bnb
    a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
    ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong hBpos
    ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    ψ hψ hreal heven hψK hsupp
  have htarget := eventual_constructed_character_target_cutoff (n + 1) (by omega)
    B z α β βg c hB hz.le hα hβ hβgap (by linarith)
  filter_upwards [hend, htarget, eventual_character_length_bounds z hz,
    eventually_ge_atTop (5 * ((n + 1 : ℕ) : ℝ) - Real.log (δ * c₀ / 32))]
    with L hend htarget hlength hmasscut
  intro m Ulate τ bmax P U T₀ hP Q hUL hUβ hUτ hτU hτ hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsize htoplog hbulklog l h hUlog hUlate u hu husep hsmall
    hbig huτ F₀ ac bin hbinlo hbinhi hbinpos w hlen χ hχ center E ρ hE hρ hsE hword hmean
  let r := fun j => (w (some j)).indices.length
  let f := (w none).indices.length
  let R := characterPrimeCells w (characterAnchorCells ac)
  let nc := Fintype.card (Σ v, Fin (characterCellSize r f v))
  have hcounts := character_constructed_counts w
  have hbudgets := character_constructed_mass_budgets w Cmass z hCmass.le hbudgetAll
  have hRmass : ∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹ := by
    intro v i
    have hh := constructed_character_cells_mass w ac hc₀ hδ β L hUβ hu hmasscut v i
    exact (Real.exp_le_exp.mpr (by nlinarith only [hβmass, hlength.1.le])).trans hh
  have haRanges := constructed_character_anchor_ranges hP w ac L γs νa hsmall hbig
  have hprod := character_selected_product_intervals w (fun j b => (ac (j, b)).index)
    bin.val hc₀ hδ
  let idx := characterCellIndex (fun j => (w (some j)).indices)
    (fun j b => (ac (j, b)).index) (w none).indices
  let lo := fun v : Σ v, Fin (characterCellSize r f v) => primeCellLower (idx v.1 v.2)
  let hi := fun v : Σ v, Fin (characterCellSize r f v) => primeCellUpper (idx v.1 v.2)
  have haτ (j) : ((ac (j, false)).index : ℝ) + (ac (j, true)).index ≤ 4 * τ :=
    by linarith [(ac (j, false)).upper, (ac (j, true)).upper, huτ j]
  have hT := htarget Ulate τ bin.val m (fun j b => (ac (j, b)).index)
    hUL hUβ hUτ hτU hτ hlength.2.2.2.1 hbinlo hbinhi haτ
  have hnc : nc ≤ Bnb := hcounts.2.2.1.trans (by dsimp [Bnb, N]; omega)
  let EZ := E.image (fun x : ℕ => (x : ℤ))
  have hcard : EZ.card = E.card := Finset.card_image_of_injective _ Int.ofNat_injective
  apply hend nc hnc r f (fun j => hlen (some j)) hcounts.1 hcounts.2.1
    hcounts.2.2.2 hbudgets.2 (Fintype.equivFin _)
    (1000 * (4 : ℝ) ^ (n + 1) * τ) τ bmax P U T₀ hP Q R
    (by positivity) hzero hsucc hQP
    (characterPrimeCells_subset w (characterAnchorCells ac) (fun j => (ac j).cell_subset))
    hbulk htop hRmass htotal hPrange hUrange hUT
    (constructed_character_cells_bulk_disjoint w ac U l h hUlog hUlate husep)
    haRanges.1 haRanges.2 hsize htoplog hbulklog lo hi
    (constructed_character_cells_prime_bounds w ac hP)
    (fun j b => ((ac (j, b)).index : ℝ)) bin hbinpos hT
    (fun v => (Real.exp_le_exp.mpr (sub_le_sub_left hcover _)).trans (hprod v).1)
    (fun v => (hprod v).2.trans (Real.exp_le_exp.mpr (add_le_add_right hcover _)))
    χ hχ center EZ ρ (by rwa [hcard]) hρ
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Int.cast_natCast] using hsE y hy
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Int.cast_natCast] using hword y hy
  · intro x hx v i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Int.cast_natCast] using hmean y hy v i

end Ostmann

end OAI
