import OAI.NumberTheory.JointDickman.Counting.AuxiliaryBandEnergy
import OAI.NumberTheory.JointDickman.Amplification.CanonicalExceptionalSamples
import OAI.NumberTheory.JointDickman.Amplification.RamareIntegralBound

namespace OAI

/-! # A bound for the full exceptional energy -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

noncomputable def auxiliarySampleCost (C H₀ X : ℝ) (N : ℕ) (T a b : ℝ) : ℝ :=
  (((Real.log a)^10)⁻¹)^2*
    (48000*(2*(1+Real.log (2*T+1))+
      ((H₀*(Real.log X)^2+1)*X^(5/12:ℝ))*Real.sqrt (2*T)*a/N))+
    b^2*(C/(Real.log a)^2)

theorem auxiliary_exceptional_energy (P₀ Q₀ B : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hB : 1 ≤ B) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ᶠ X : ℝ in atTop,
      let J := mellinBandCount Q₀ (Real.sqrt (Real.log X)) hQ₀
      let D := canonicalMellinBands P₀ Q₀ (1/12)
      ∀ (N : ℕ) (P K : Finset ℕ) (bin : ℕ → ℕ) (lower : ℕ → ℝ) (δ : ℝ),
      0 < N → (∀ p ∈ P, p.Prime) → (∀ p ∈ P, bin p ∈ K) →
      1 ≤ δ → δ ≤ 2 →
      (∀ p ∈ P, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p)) →
      (∀ k ∈ K, A ≤ lower k ∧ 2 ≤ (N:ℝ)/lower k) →
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 < T → T ≤ X →
      E ⊆ Set.Ioc (-T) T → E ⊆ mrtNoSmallBand D.bins (D.polynomial F) D.threshold J →
      (∀ k ∈ K, 2*T ≤ (lower k)^B) →
      (∀ k ∈ K, ∀ t ∈ E, ‖mrtCofactorPolynomial P F N (lower k) t‖ ≤ b) →
      (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        5632*Real.exp 1*(T/N+1)*
          ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(δ-1))+
        8*(K.card:ℝ)*(∑ k ∈ K,
          auxiliarySampleCost C (mrtBaseResolution P₀ Q₀ (1/12)) X N T (lower k) b)+
        16*Real.exp 1*(T/N+2)*
          (((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  obtain ⟨C,hC,hbound⟩ := ramare_product_integral_bound B hB
  obtain ⟨A,hA⟩ := eventually_atTop.mp hbound
  refine ⟨C,max 1 A,hC,le_max_left _ _,?_⟩
  filter_upwards [canonical_exceptional_samples P₀ Q₀ hP₀ hPQ hlogP hQ₀ hH] with X hX
  dsimp only at hX ⊢
  intro N P K bin lower δ hN hP hbin hδ hδ2 hL hlow F hF hFb E T b
    hEm hT hTX hET hEres hTB hb
  have hfull := auxiliary_band_full_energy P hP K bin hbin lower hN hδ hδ2 hL
    F hF hFb hT hET
  have hsum := sum_le_sum (s := K) (fun k hk => show
      (∫ t in E, ‖mrtExponentialPolynomial (P.filter (fun p => bin p=k))
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
        mrtCofactorPolynomial P F N (lower k) t‖^2) ≤
      2*auxiliarySampleCost C (mrtBaseResolution P₀ Q₀ (1/12)) X N T (lower k) b from by
    apply hA (lower k) ((le_max_right 1 A).trans (hlow k hk).1)
      N P (P.filter (fun p => bin p=k)) F F
      ((le_max_left 1 A).trans (hlow k hk).1) (hlow k hk).2
      (fun n _ => hFb n) (fun n _ => hFb n) ?_ E T b
      ((mrtBaseResolution P₀ Q₀ (1/12)*(Real.log X)^2+1)*X^(5/12:ℝ))
      hEm hT.le hET (hTB k hk) ?_ (hb k hk)
    · intro p hp
      obtain ⟨hp,hpk⟩ := mem_filter.mp hp
      have hl := hL p hp
      rw [hpk] at hl
      exact ⟨hP p hp,hl.1,hl.2.trans
        (mul_le_mul_of_nonneg_right hδ2 (by linarith [(hlow k hk).1,le_max_left 1 A]))⟩
    · intro U hUE hsep
      refine hX F (fun n _ => hFb n) U ?_ hsep ?_
      · intro t ht
        obtain ⟨hlo,hhi⟩ := hET (hUE t ht)
        exact (abs_le.mpr ⟨by linarith,by linarith⟩).trans hTX
      · intro t ht
        exact hEres (hUE t ht))
  rw [← mul_sum] at hsum
  have hc : (0:ℝ) ≤ K.card := Nat.cast_nonneg _
  nlinarith

end JointDickman

end OAI
