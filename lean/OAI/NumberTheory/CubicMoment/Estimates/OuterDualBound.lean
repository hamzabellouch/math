import OAI.NumberTheory.CubicMoment.Estimates.OuterScale
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeZeroMode

namespace OAI

/-! Summation of every dual frequency in the common-factor Gram kernel,
with the unit zero mode explicitly subtracted. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment

 theorem coprimeGramForm_outer_dual_bound {ε R : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 1 ≤ R) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      ‖coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z‖ ≤
        (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2))*
          ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprime_poisson_outer_annulus hε hR W hW hW'
  refine ⟨C,hC,?_⟩
  intro S u Z N hZ hN hS
  let E := ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => by positivity)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hR0 : 0 ≤ R*N := mul_nonneg (zero_le_one.trans hR) hNp.le
  have hfinite (I : Finset ℕ) :
      ‖∑ j ∈ I, coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
        (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2))*E := by
    have hf (j : ℕ) (_ : j ∈ I) := hbound S u Z N j hZ hN hS
    have hh := finite_outer_poisson_sum I
      (fun j => coprimePoissonDyad S (frequencyDyad j) u W Z)
      (C := C*E) (T := R*N) (ε := ε) (mul_nonneg hC.le hE) hZ hNp hR0 hε hε1
      (fun j hj => (hf j hj).trans_eq (by dsimp only [E]; ring))
    exact hh.trans_eq (by ring)
  have hs := hasSum_coprimePoissonDyad_with_zero S
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u W hW hW' hZ
  exact le_of_tendsto hs.norm (Eventually.of_forall hfinite)

end CubicFirstMoment

end

end OAI
