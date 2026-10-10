import OAI.NumberTheory.CubicMoment.Estimates.OuterDualBound
import OAI.NumberTheory.CubicMoment.Estimates.OuterPrimalScale
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeUnitFrequency

namespace OAI

/-! All frequencies of the compact Gram kernel. Its zero mode has no
epsilon loss; the remaining frequencies have the three primal powers. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimePoissonDyad_zero_bound (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    ‖coprimePoissonDyad S {0} u W Z‖ ≤
      (‖normProfileFourier W 0‖/9)*Z*
        ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  rw [coprimePoissonDyad_unit_frequency S hS]
  by_cases h1 : (1:Eisenstein) ∈ S
  · rw [ite_eq_left h1,norm_mul,norm_mul,norm_mul,norm_star,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < Z/9)]
    have he : ‖u 1‖^2 ≤ ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
      calc
        ‖u 1‖^2 ≤ (2:ℝ)^(primaryPrimeFactors 1).card*‖u 1‖^2 :=
          le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num))
        _ ≤ _ := Finset.single_le_sum
          (f := fun a => (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2)
          (fun a ha => mul_nonneg (by positivity) (sq_nonneg _)) h1
    calc
      _ = (‖normProfileFourier W 0‖/9)*Z*‖u 1‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
  · rw [ite_eq_right h1,norm_zero]
    positivity

 theorem coprimeGramForm_outer_complete {ε R : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 1 ≤ R) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      ‖coprimeGramForm S u W Z‖ ≤
        ((‖normProfileFourier W 0‖/9)*Z + C*(N^3/Z)^ε*
          (N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)))*
            ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimeGramForm_outer_dual_bound hε hε1 hR W hW hW'
  have hRp : 0 < R := zero_lt_one.trans_le hR
  refine ⟨C*outerPowerConstant ε R,mul_pos hC (outerPowerConstant_pos hε hε1 hRp),?_⟩
  intro S u Z N hZ hN hS
  have hE : 0 ≤ ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hd := (hbound S u Z N hZ hN hS).trans
    (mul_le_mul_of_nonneg_right
      (outer_primal_scale_bound hZ (zero_lt_one.trans_le hN) hRp hC.le hε hε1) hE)
  have hz := coprimePoissonDyad_zero_bound S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    u W hZ
  have hh := norm_add_le (coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z)
    (coprimePoissonDyad S {0} u W Z)
  rw [sub_add_cancel] at hh
  exact hh.trans ((add_le_add hd hz).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
