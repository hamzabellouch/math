import OAI.NumberTheory.JointDickman.Amplification.LowAlternativePairs
import Mathlib.Data.Finset.Sigma

namespace OAI

/-! # Injectively counting large alternative representations by numeric classes -/

namespace JointDickman
open Finset Classical

theorem largeLowAlternativePairs_count {B L k j d f : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B) (hU : U ⊆ auxiliaryPrimes B \ A)
    (hAr : RegularPrimeSet B L τ C A) (hUr : RegularPrimeSet B L τ C U)
    (hDr : RegularPrimeSet B L τ C D) (hVr : RegularPrimeSet B L τ C V) :
    (largeLowAlternativePairs B L k j d f τ C Δ A U D V).card ≤
      ∑ Oa ∈ omissionEnvelope B L k τ A d,
        ∑ Od ∈ omissionEnvelope B L k τ D f,
          ∑ Y ∈ regularPrefixChoices B L k V f,
            ((activeLowAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
              ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d).filter (fun Z => Z ⊆ U)).card := by
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let target := E.sigma (fun Oa => F.sigma (fun Od => P.sigma (fun Y =>
    (activeLowAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
      ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d).filter (fun Z => Z ⊆ U))))
  let enc : (Finset ℕ × Finset ℕ) → Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ :=
    fun XY => ⟨A \ XY.1,⟨D \ XY.2,⟨XY.2 \ D,XY.1 \ A⟩⟩⟩
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ largeLowAlternativePairs B L k j d f τ C Δ A U D V) : enc XY ∈ target := by
    have hh := largeLowAlternativePairs_encoding hk hτ hℓ hA hU hAr hUr hDr hVr hXY
    simpa only [target,enc,E,F,P,mem_sigma] using hh
  have hinj : Set.InjOn enc (largeLowAlternativePairs B L k j d f τ C Δ A U D V) := by
    intro XY _ ZW _ he
    have h₁ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.1) he
    have h₂ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.1) he
    have h₃ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.2.1) he
    have h₄ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.2.2) he
    change A \ XY.1 = A \ ZW.1 at h₁
    change D \ XY.2 = D \ ZW.2 at h₂
    change XY.2 \ D = ZW.2 \ D at h₃
    change XY.1 \ A = ZW.1 \ A at h₄
    apply Prod.ext
    · ext p
      have h₁ := Finset.ext_iff.mp h₁ p
      have h₄ := Finset.ext_iff.mp h₄ p
      simp only [Finset.mem_sdiff] at *
      tauto
    · ext p
      have h₂ := Finset.ext_iff.mp h₂ p
      have h₃ := Finset.ext_iff.mp h₃ p
      simp only [Finset.mem_sdiff] at *
      tauto
  have hc := card_le_card_of_injOn enc hmap hinj
  simpa only [target,card_sigma,E,F,P] using hc

end JointDickman

end OAI
