import OAI.NumberTheory.Ostmann.Characters.CharacterInitialRate
import OAI.NumberTheory.Ostmann.Characters.CharacterScheduledInitial
import OAI.NumberTheory.Ostmann.Characters.CharacterPoissonCutoff
import OAI.NumberTheory.Ostmann.Characters.CharacterWordSupport
import OAI.NumberTheory.Ostmann.Characters.CharacterLengthBounds
import OAI.NumberTheory.Ostmann.Characters.CharacterAtomIteration

namespace OAI

/-! # The actual endpoint statistic starts the scheduled character iteration -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_character_scheduled_initial_rate (k nc : ℕ)
    (a b z Cmass Ctotal Aend Bword B c s γ H α : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 ≤ Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hbudget : 4 * nc * Cmass ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (r : Fin k → ℕ) (f : ℕ)
      (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin k → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)),
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget k bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    ∀ pivot : ℕ → (Σ v, Fin (characterSize m r f v)),
    let V := naturalTransferCutoff Δ m
    let cap := characterPivotCap T (characterRangeError k c)
    let lo := initialWordAtomLower bin.val (fun v => ∏ i, cellLo ⟨v, i⟩)
    let hi := initialWordAtomUpper bin.val (fun v => ∏ i, cellHi ⟨v, i⟩)
    let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
    Real.exp (-(Aend + 2 * Bword + 2) * m) ≤
      ‖scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ₀
        (fun i => primeGaussMultiplier (χ₀ i)) pivot P hP
        (characterFullPrimeCells m r f Q R) lo hi V cap
        (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
          (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
          (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c))) center 0‖ := by
  have hrate := eventual_character_initial_rate k nc a b z Cmass Ctotal Aend Bword B c s γ
    ha hb hz.le hCmass hCtotal hc hs hγ hbudget hgap ψ
  have hd : 0 ≤ B + 20 * Real.log z := by linarith [Real.log_nonneg hz.le]
  filter_upwards [eventually_bulkCount z (by linarith) _ hrate,
    eventual_character_poisson_window z (B + 20 * Real.log z)
      ((Fintype.card (CharacterRole k) : ℝ) * c) H α hz.le hd hH hα,
    eventual_character_length_bounds z hz] with L hrate hwindow hlength
  intro m r f cell logX τ bmax P U T₀ hP Q R hzero hsucc hQP hRP hbulk htop hR htotal
    hPlower hsize htoplog hbulklog cellLo cellHi hcell anchor bin Δ T F hlo hhi χ hχ
    center E ρ hE hρ hsE hword hmean pivot V cap lo hi χ₀
  let Rflat : Fin nc → Finset ℕ := fun j => R (cell.symm j).1 (cell.symm j).2
  have hRf (i) : Rflat (cell i) = R i.1 i.2 := by
    dsimp only [Rflat]
    rw [cell.symm_apply_apply]
  have hcell' (i) (p) (hp : p ∈ Rflat (cell i)) : cellLo i ≤ p ∧ p ≤ cellHi i := by
    rw [hRf] at hp
    exact hcell i.1 i.2 p hp
  have hbin := character_initial_word_support m nc P U T₀ Q Rflat hP hzero hsucc bmax τ
    hsize htoplog hbulklog
  have hraw := hrate r f cell L logX τ hlength.1 hlength.2.2.2.1 hlength.2.2.2.2
    P U T₀ hP Q Rflat hzero hsucc hQP (fun j => hRP _ _) hbulk htop
    (fun j => hR _ _) htotal cellLo cellHi hcell' T anchor bin hlo hhi hbin χ hχ center E ρ H
    hE hρ hψ hreal hH hsE hword (fun x hx j => hmean x hx _ _) (V 0) hsupp
    (fun p hp => hwindow.2 p (hPlower p hp)) hwindow.1
  have he := character_initial_scheduled_amplitude k m nc r f cell P hP Q Rflat
    cellLo cellHi hcell' χ hχ pivot center ψ heven logX Δ τ c hc T anchor V cap bin
    hlo hhi hbin
  have hRcell : (fun v i => Rflat (cell ⟨v, i⟩)) = R := by
    funext v i
    exact hRf ⟨v, i⟩
  rw [hRcell] at he
  exact he.symm ▸ hraw

end Ostmann

end OAI
