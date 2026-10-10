import OAI.NumberTheory.JointDickman.Analysis.MultiscaleMellinEnergy
import OAI.NumberTheory.JointDickman.Analysis.MellinRestrictionRestore

namespace OAI

/-! # Summing the actual auxiliary-band Ramaré products -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

lemma integral_norm_sum_sq_le_card {ι : Type*} (K : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ k ∈ K, Continuous (F k)) {T : ℝ} (hT : 0 ≤ T)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖∑ k ∈ K, F k t‖^2) ≤
      (K.card:ℝ)*∑ k ∈ K, ∫ t in E, ‖F k t‖^2 := by
  have hi k hk := mrt_continuous_square_integrable (hF k hk) hT hE
  calc
    _ ≤ ∫ t in E, (K.card:ℝ)*∑ k ∈ K, ‖F k t‖^2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum K hi).const_mul _)
      intro t _
      exact mrt_norm_sum_sq_le_card K (fun k => F k t)
    _ = _ := by rw [integral_const_mul,integral_finsetSum K hi]

theorem auxiliary_band_energy {κ : Type*} [DecidableEq κ]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F) t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(δ-1))+
      2*(K.card:ℝ)*∑ k ∈ K, ∫ t in E,
        ‖mrtExponentialPolynomial (P.filter (fun p => bin p=k))
          (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
          mrtCofactorPolynomial P F N (lower k) t‖^2 := by
  let G : κ → ℝ → ℂ := fun k t =>
    mrtExponentialPolynomial (P.filter (fun p => bin p=k))
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
      mrtCofactorPolynomial P F N (lower k) t
  have hG k : Continuous (G k) :=
    (mrtExponentialPolynomial_continuous _ _ _).mul (mrtCofactorPolynomial_continuous _ _ _ _)
  have herr := mrt_typical_general_prime_mean_square ({()} : Finset Unit) (fun _ => P)
    (fun _ _ => hP) (by simpa only [coe_singleton] using Set.pairwiseDisjoint_singleton () (fun _ : Unit => P))
    (mem_singleton_self ()) (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  have hempty : mrtTypicalCoefficient (∅ : Finset Unit) (fun _ => P) F=F := by
    funext n
    simp [mrtTypicalCoefficient,mrtTypical]
  simp only [Finset.erase_singleton] at herr
  rw [hempty] at herr
  simp_rw [mrt_extracted_prime_bins K P bin hbin lower N F F] at herr
  have hs := mrt_restricted_energy_split
    (angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F))
    (fun t => ∑ k ∈ K,G k t) (angularMellinPolynomial_continuous _ _)
    (continuous_finsetSum K (fun k _ => hG k)) hT.le hE
  have hsum := integral_norm_sum_sq_le_card K G (fun k _ => hG k) hT.le hE
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
    (mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F) t-
    ∑ k ∈ K,G k t‖^2) ≤ _ at herr
  change _ ≤ _ + 2*(K.card:ℝ)*∑ k ∈ K, ∫ t in E, ‖G k t‖^2
  linarith

theorem auxiliary_band_full_energy {κ : Type*} [DecidableEq κ]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : ∀ n, ‖F n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
      5632*Real.exp 1*(T/N+1)*
        ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(δ-1))+
      4*(K.card:ℝ)*(∑ k ∈ K, ∫ t in E,
        ‖mrtExponentialPolynomial (P.filter (fun p => bin p=k))
          (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
          mrtCofactorPolynomial P F N (lower k) t‖^2)+
      16*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  classical
  have heq : (fun n => @ite ℂ (¬mrtPrimeAvoids P n) (Classical.propDecidable _) (F n) 0) =
      mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F := by
    funext n
    have hh : mrtTypical ({()} : Finset Unit) (fun _ => P) n ↔ ¬mrtPrimeAvoids P n := by
      simp [mrtTypical,mrtPrimeAvoids]
    by_cases h : mrtPrimeAvoids P n <;> simp [mrtTypicalCoefficient,hh,h]
  have hrestore := angularMellin_energy_of_restriction (fun n => ¬mrtPrimeAvoids P n)
    F hFb hN hT hE
  rw [heq] at hrestore
  simp only [not_not] at hrestore
  have haux := auxiliary_band_energy P hP K bin hbin lower hN hδ hδ2 hL
    F hF (fun n _ => hFb n) hT hE
  linarith

end JointDickman

end OAI
