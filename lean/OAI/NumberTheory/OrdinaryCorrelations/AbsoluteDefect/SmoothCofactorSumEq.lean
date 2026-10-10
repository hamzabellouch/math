import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SieveTriangleKernelErrorAt
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothCofactorHarmonic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCountRoughZero

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothRough
open Finset OrdinaryCorrelations OrdinaryLogIntegral OrdinarySelbergWeights
open OrdinarySmoothDampedFamily Filter

lemma smooth_cofactor_sum_eq (f : ℕ → ℂ) (P S : Finset ℕ) (M L : ℕ) (t : ℝ) :
    (∑ a ∈ (Finset.Ioc M L).filter (fun a => a ∈ Nat.factoredNumbers S), cofactorTerm f P a t) =
      smoothCofactorHarmonic f P S M L t := by
  unfold smoothCofactorHarmonic
  apply sum_congr rfl
  intro a ha
  simp only [cofactorTerm, OrdinaryArchimedeanTwist.twist, logPhase]
  ring

theorem uniform_actual_rectangle_energy {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, M ≤ L → L ≤ 2*M →
      ∀ (P S R : Finset ℕ) (T : Finset ℝ) (u B z : ℕ)
      (_hS : ∀ p ∈ S, Nat.Prime p) (hprime : Squarefree (∏ p ∈ S, p)),
      P ⊆ S →
      (∀ b ∈ R, 0<b ∧ ∀ p ∈ S, Nat.Prime p → ¬p∣b) →
      1 ≤ u → 0 < B → B ≤ u^8 → 1 ≤ z → z^2 ≤ B →
      R ⊆ Finset.Icc (2*B) (4*B) →
      (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u:ℝ)^10) →
      (∀ t ∈ T, |t| ≤ (M:ℝ)^k/2) →
      (∑ t ∈ T, ‖∑ n ∈ (((Finset.Ioc M L).filter (fun a => a ∈ Nat.factoredNumbers S)) ×ˢ R).image
        (fun ab => ab.1*ab.2), cofactorTerm f P n t‖^2) ≤
      ε^2 * ((264*(actualMass (∏ p ∈ S, p) z hprime)⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4*(u:ℝ)^7/B) *
      (44*(actualMass (∏ p ∈ S, p) z hprime)⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7/B)/4) := by
  filter_upwards [uniform_smooth_cofactor_harmonic hf hm hNP k hk hε] with M hM
  intro L hML hL P S R T u B z hS hprime hPS hR hu hB hBU hz hzB hRB hsep hheight hTs
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => hS p (hPS hp)
  have hA : ∀ a ∈ (Finset.Ioc M L).filter (fun a => a ∈ Nat.factoredNumbers S),
      0<a ∧ a ∈ Nat.factoredNumbers S := by
    intro a ha
    obtain ⟨haI,has⟩ := mem_filter.mp ha
    exact ⟨lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp haI).1,has⟩
  have hcop : ∀ b ∈ R, b.Coprime (∏ p ∈ S, p) := by
    intro b hb
    exact Nat.Coprime.prod_right (fun p hp => ((hS p hp).coprime_iff_not_dvd.mpr
      ((hR b hb).2 p hp (hS p hp))).symm)
  have he (t : ℝ) : (∑ n ∈ (((Finset.Ioc M L).filter (fun a => a ∈ Nat.factoredNumbers S)) ×ˢ R).image
      (fun ab => ab.1*ab.2), cofactorTerm f P n t) =
        smoothCofactorHarmonic f P S M L t * (∑ b ∈ R, (f b/(b:ℂ))*logPhase t b) := by
    rw [rectangular_cofactor_factorization f hm P S _ R hPS hP hA hR,
      smooth_cofactor_sum_eq]
  simp_rw [he]
  exact signed_product_energy_at_scale R T f (smoothCofactorHarmonic f P S M L)
    u B (∏ p ∈ S, p) z hprime hu hB hBU hz hzB hRB hcop (fun n _ => hf n) hsep hheight hε.le
    (fun t ht => hM L hML hL P S hP t (hTs t ht))

end OrdinarySmoothRough

end

end OAI
