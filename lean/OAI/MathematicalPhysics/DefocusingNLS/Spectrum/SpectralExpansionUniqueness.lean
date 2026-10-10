import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialStability
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionCompatibility

namespace OAI

/-! Independence of the truncation used to construct a coupled outgoing solution. -/

open Polynomial Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularPolynomialJet_sub (U V : ℂ[X] × ℂ[X]) (t : ℝ) :
    circularPolynomialJet (U-V) t=circularPolynomialJet U t-circularPolynomialJet V t := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [circularPolynomialJet,radialExteriorPolynomialFunction,radialPolynomialEuler,
      derivative_sub,mul_sub]

theorem circularPolynomialJet_factor_decay (U : ℂ[X] × ℂ[X]) (j : ℕ)
    (hU : X^j ∣ U.1) (hV : X^j ∣ U.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖circularPolynomialJet U t‖ ≤ C*Real.exp (-(2*(j : ℝ))*t) := by
  obtain ⟨C,hC,hCb⟩ := radialPolynomialJet_factor_decay U.1 j hU
  obtain ⟨D,hD,hDb⟩ := radialPolynomialJet_factor_decay U.2 j hV
  refine ⟨max C D,le_max_of_le_left hC,?_⟩
  intro t ht
  change max ‖radialPolynomialJet U.1 t‖ ‖radialPolynomialJet U.2 t‖ ≤ _
  apply max_le
  · exact (hCb t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  · exact (hDb t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))

theorem circular_profile_expansions_difference (ν νp νm η b : ℂ) (n : ℕ)
    (c : ℂ × ℂ) (j k : ℕ) (hjk : j ≤ k) (v w : CircularTailSpace) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖(circularPolynomialJet (spectralOutgoingPolynomial νp νm η n
          (radialExteriorExpansion ν n b j) c j) t+circularUnweight (2*(j : ℝ)) v t)-
       (circularPolynomialJet (spectralOutgoingPolynomial νp νm η n
          (radialExteriorExpansion ν n b k) c k) t+circularUnweight (2*(k : ℝ)) w t)‖ ≤
        C*Real.exp (-(2*(j : ℝ))*t) := by
  let U := spectralOutgoingPolynomial νp νm η n (radialExteriorExpansion ν n b j) c j
  let V := spectralOutgoingPolynomial νp νm η n (radialExteriorExpansion ν n b k) c k
  have hPQ : X^j ∣ radialExteriorExpansion ν n b j-radialExteriorExpansion ν n b k := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_sub,radialExteriorExpansion_coeff_initial ν n b j k i hjk (by omega),sub_self]
  obtain ⟨hU,hV⟩ := spectralOutgoingPolynomial_order_difference νp νm η n
    (radialExteriorExpansion ν n b j) (radialExteriorExpansion ν n b k) c j k hjk hPQ
  have hpow : (X : ℂ[X])^j ∣ X^(j+1) := pow_dvd_pow X (Nat.le_succ j)
  obtain ⟨C,hC,hCb⟩ := circularPolynomialJet_factor_decay (V-U) j
    (hpow.trans hU) (hpow.trans hV)
  refine ⟨C+‖v‖+‖w‖,by positivity,?_⟩
  intro t ht
  have hE : Real.exp (-(2*(k : ℝ))*t) ≤ Real.exp (-(2*(j : ℝ))*t) := by
    apply Real.exp_le_exp.mpr
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith
  have hpoly : ‖circularPolynomialJet U t-circularPolynomialJet V t‖ ≤
      C*Real.exp (-(2*(j : ℝ))*t) := by
    simpa only [circularPolynomialJet_sub,norm_sub_rev] using hCb t ht
  change ‖(circularPolynomialJet U t+circularUnweight (2*(j : ℝ)) v t)-
    (circularPolynomialJet V t+circularUnweight (2*(k : ℝ)) w t)‖ ≤ _
  have he : (circularPolynomialJet U t+circularUnweight (2*(j : ℝ)) v t)-
      (circularPolynomialJet V t+circularUnweight (2*(k : ℝ)) w t)=
      (circularPolynomialJet U t-circularPolynomialJet V t)+
        circularUnweight (2*(j : ℝ)) v t-circularUnweight (2*(k : ℝ)) w t := by abel
  rw [he]
  calc
    _ ≤ ‖circularPolynomialJet U t-circularPolynomialJet V t‖+
        ‖circularUnweight (2*(j : ℝ)) v t‖+‖circularUnweight (2*(k : ℝ)) w t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C*Real.exp (-(2*(j : ℝ))*t)+Real.exp (-(2*(j : ℝ))*t)*‖v‖+
        Real.exp (-(2*(k : ℝ))*t)*‖w‖ :=
      add_le_add (add_le_add hpoly (circularUnweight_norm _ _ v)) (circularUnweight_norm _ _ w)
    _ ≤ C*Real.exp (-(2*(j : ℝ))*t)+Real.exp (-(2*(j : ℝ))*t)*‖v‖+
        Real.exp (-(2*(j : ℝ))*t)*‖w‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
    _ = _ := by ring

theorem circular_outgoing_orders_unique (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (c : ℂ × ℂ) (j k : ℕ) (hjk : j ≤ k) (v w : CircularTailSpace)
    (M T : ℝ) (q : ℝ → ℂ) (Z W : ℝ → E₄)
    (hq : ∀ t, T ≤ t → ‖q t‖ ≤ M)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η n (q t) (Z t)) t)
    (hW : ∀ t, T ≤ t → HasDerivAt W
      (circularLeadingField t (W t)+circularBoundedField νp νm η n (q t) (W t)) t)
    (heZ : ∀ t, T ≤ t → Z t=circularPolynomialJet
      (spectralOutgoingPolynomial νp νm η n (radialExteriorExpansion ν n b j) c j) t+
        circularUnweight (2*(j : ℝ)) v t)
    (heW : ∀ t, T ≤ t → W t=circularPolynomialJet
      (spectralOutgoingPolynomial νp νm η n (radialExteriorExpansion ν n b k) c k) t+
        circularUnweight (2*(k : ℝ)) w t)
    (hκ : circularFieldBound νp νm η n M < 2*(j : ℝ)) :
    ∀ t, max T 0 ≤ t → Z t=W t := by
  obtain ⟨C,_,hC⟩ := circular_profile_expansions_difference ν νp νm η b n c j k hjk v w
  intro t ht
  apply circular_fast_decay_unique νp νm η n hn M (2*(j : ℝ)) C (max T 0) q Z W
    (fun s hs => hq s ((le_max_left _ _).trans hs))
    (fun s hs => hZ s ((le_max_left _ _).trans hs))
    (fun s hs => hW s ((le_max_left _ _).trans hs)) _ hκ t ht
  intro s hs
  rw [heZ s ((le_max_left _ _).trans hs),heW s ((le_max_left _ _).trans hs)]
  exact hC s ((le_max_right _ _).trans hs)

end DefocusingNLS

end OAI
