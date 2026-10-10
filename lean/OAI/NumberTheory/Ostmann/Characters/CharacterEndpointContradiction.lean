import OAI.NumberTheory.Ostmann.Characters.CharacterUniformIteration
import OAI.NumberTheory.Ostmann.Characters.CharacterScheduledInitialRate
import OAI.NumberTheory.Ostmann.Characters.CharacterLiftCellBounds

namespace OAI

/-! # The selected endpoint family contradicts the character comparison -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_endpoint_contradiction (n N Bnb nc : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hbudget : 4 * nc * Cmass ≤ z)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass * Bnb ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
    (∀ j, r j ≤ N) → f ≤ N →
    1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
    Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
    ∀ (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
    0 < logX → Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (∀ v i, Disjoint U (R v i)) →
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin (n + 1) → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)), 0 < bin.val →
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget (n + 1) bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ j, T j + c ≤ Real.exp (βg * L)) →
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    False := by
  have hconj (x : ℝ) : conj (ψ x) = ψ x := by
    apply Complex.ext <;> simp [hreal x]
  have hstart := eventual_character_scheduled_initial_rate (n + 1) nc a b z Cmass Ctotal
    Aend Bword B c s γ H α ha hb hz hCmass.le hCtotal hc hs hγ hH hα hbudget
    hgapInitial hB ψ hψ hreal heven hsupp
  have hfinish := eventual_uniform_character_iteration_contradiction n N Bnb ψ hconj
    K B B₁ z c a b Cmass α βg βw γs βa γw νw νa ε hBpos hBstrong hB₁ hz hc
    ha ha1 hb hCmass hα hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll
    hgapFinal hψK hentropy
  filter_upwards [hstart, hfinish] with L hstart hfinish
  intro m r f hr hrN hf hnb hpivot cell logX τ bmax P U T₀ hP Q R
    hlogX hzero hsucc hQP hRP hbulk htop hR htotal hPrange hUrange hUT hUR hsmall hbig
    hsize htoplog hbulklog cellLo cellHi hcell anchor bin hbinpos Δ T F hT hlo hhi
    χ hχ center E ρ hE hρ hsE hword hmean
  have hχ' (p : ℕ) (hp : p ∈ P) : χ p ≠ 1 := by
    intro he
    exact hχ p hp (by rw [he, one_pow])
  have hinit := hstart r f cell logX τ bmax P U T₀ hP Q R hzero hsucc hQP hRP hbulk htop
    hR htotal (fun p hp => (hPrange p hp).1) hsize htoplog hbulklog cellLo cellHi hcell
    anchor bin hlo hhi χ hχ' center E ρ hE hρ hsE hword hmean (characterPivot m r f hr)
  let L₀ := characterLiftCellBound m r f 0 cellLo
  let H₀ := characterLiftCellBound m r f (P.sup id) cellHi
  have hcell' := characterLiftCellBound_support m r f P Q R hQP cellLo cellHi hcell
  have hlo' (v : CharacterCell (n + 1)) :
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
        ∏ i, L₀ ⟨(true, some v), i⟩ := hlo v
  have hhi' (v : CharacterCell (n + 1)) :
      (∏ i, H₀ ⟨(true, some v), i⟩ : ℕ) ≤
        Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c) := hhi v
  apply hfinish r f hrN hf hr hnb hpivot P U hP Q R hsucc
    (by simpa only [hzero] using hUT) hUR hQP hRP (by simpa only [hzero] using htop)
    hbulk hR hPrange hUrange hsmall hbig χ hχ bin.val hbinpos anchor F logX hlogX hT
    L₀ H₀ hcell' hlo' hhi' center
  have hcoef : B₁ - 1 = Aend + 2 * Bword + 2 := by linarith only [hB₁eq]
  rw [hcoef]
  exact hinit

end Ostmann

end OAI
