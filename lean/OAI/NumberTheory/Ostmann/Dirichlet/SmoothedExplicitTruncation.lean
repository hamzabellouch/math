import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitAbsorption
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitChosenEdges
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitScale
import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitZeroSum

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set
open scoped Topology BigOperators SchwartzMap

def upperZeroWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (H X : ℝ) (A : ℕ) : ℝ :=
  ∑ p ∈ (zerosUpTo_finite χ hχ H).toFinset.filter (fun p => (1:ℝ)/2 ≤ p.re),
    (zeroMultiplicity χ p:ℝ)*X^p.re/(1+|p.im|)^A

theorem upperZeroWeight_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H X : ℝ) (A : ℕ) (hX : 0 ≤ X) :
    0 ≤ upperZeroWeight χ hχ H X A := by
  unfold upperZeroWeight
  exact Finset.sum_nonneg fun p _ => by positivity

theorem exists_smoothed_explicit_truncation (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X T : ℝ),
      Real.exp 2 ≤ X → 2 ≤ T →
      ‖∑' n : ℕ, χ n*(ArithmeticFunction.vonMangoldt n:ℂ)*ρ ((n:ℝ)/X)‖ ≤
        C*(upperZeroWeight χ hχ (T+1) X A +
          Real.sqrt X*((q:ℝ)*(T+2))^7 +
          X*((q:ℝ)*(T+2))^7/T^A*(1+Real.log X)^7) := by
  obtain ⟨E,hE,hgood⟩ := exists_good_contour_edges
  obtain ⟨D,hD,hright⟩ := uniform_log_derivative_right
  obtain ⟨K,hK,hker,hker0,hker2⟩ := exists_smooth_kernel_bounds ρ A
  let M : ℝ := 128000000*absoluteZetaTwo
  have hM : 0 ≤ M := by have := one_le_absoluteZetaTwo; dsimp [M]; positivity
  obtain ⟨C,hC,habsorb⟩ := exists_smoothed_error_absorption E K M D smoothTailIntegral
    hE.le hK hM hD smoothTailIntegral_nonneg
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ X T hX hT
  obtain ⟨hXone,hr,hinv,hpow⟩ := smoothRightAbscissa_properties hX
  let right := smoothRightAbscissa X
  let R : ℝ := (q:ℝ)*(T+2)
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hR : 1 ≤ R := contour_scale_ge_one hT
  obtain ⟨left,lo,hi,hl,hlo,hhi,hbound⟩ := hgood q χ hχ T hT
  have hlr : left ≤ right := by dsimp [right]; linarith [hl.2,hr.1]
  have hlohi : lo ≤ hi := by linarith [hlo.2,hhi.1]
  have hedge (s : ℂ)
      (hs : (s.re=left ∧ lo ≤ s.im ∧ s.im ≤ hi) ∨
        (s.im=lo ∧ left ≤ s.re ∧ s.re ≤ right) ∨
        (s.im=hi ∧ left ≤ s.re ∧ s.re ≤ right)) :
      χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ E*R^5 := by
    have hrightle : right ≤ 2 := hr.2
    rcases hs with ⟨hre,himlo,himhi⟩ | ⟨him,hrelo,hrehi⟩ | ⟨him,hrelo,hrehi⟩
    · simpa only [logDeriv_apply,R] using hbound s (by rw [hre]; exact hl.1)
        (by rw [hre]; linarith [hl.2])
        (abs_le.mpr ⟨by linarith [hlo.1],by linarith [hhi.2]⟩) (Or.inl hre)
    · simpa only [logDeriv_apply,R] using hbound s (hl.1.trans hrelo) (hrehi.trans hrightle)
        (abs_le.mpr ⟨by rw [him]; linarith [hlo.1],by rw [him]; linarith [hlo.2]⟩)
        (Or.inr (Or.inl him))
    · simpa only [logDeriv_apply,R] using hbound s (hl.1.trans hrelo) (hrehi.trans hrightle)
        (abs_le.mpr ⟨by rw [him]; linarith [hhi.1],by rw [him]; exact hhi.2⟩)
        (Or.inr (Or.inr him))
  have hrightbound (t : ℝ) :
      ‖logDeriv χ.LFunction ((right:ℂ)+t*Complex.I)‖ ≤ (right-1)⁻¹+D := by
    simpa only [logDeriv_apply,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_zero,add_zero] using hright q χ ((right:ℂ)+t*Complex.I)
      (by simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
        mul_zero,zero_mul,sub_zero,add_zero] using hr.1)
  have htotal := smooth_contour_bound_of_edges χ hχ ρ A hXone hT hl hr hlo hhi
    (by positivity : 0 ≤ E*R^5) hK.le (add_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hr.1.le)) hD)
    hedge hker hker0 hker2 hrightbound
  let S := zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I)
  have hS (p : ℂ) (hp : p ∈ S) : p ∈ zerosUpTo χ (T+1) :=
    zerosInRectangle_subset_zerosUpTo χ hχ (by linarith [hl.1]) hlr hlohi hlo.1 hhi.2 hp
  have hstrip (p : ℂ) (hp : p ∈ S) : p.re ∈ Icc (1/4:ℝ) 2 := by
    obtain ⟨hrp,_⟩ := (mem_zerosInRectangle χ hχ _ _ p).mp hp
    have hp' : left ≤ p.re := by
      simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
        mul_zero,zero_mul,sub_zero,add_zero] using
        ((mem_Rect (by simpa using hlr) (by simpa using hlohi) p).mp hrp).1
    exact ⟨hl.1.trans hp',(hS p hp).1.2.2.le.trans (by norm_num)⟩
  have hmass : (∑ p ∈ S, (zeroMultiplicity χ p:ℝ)) ≤ M*R^5 :=
    zerosInRectangle_multiplicity_polynomial χ hχ hT hl.1 hlr hlohi hlo.1 hhi.2
  have hzero := mellin_smoothed_zero_sum_le χ hχ S ρ A hXone hK.le hS hmass
    (fun p hp => hker p (hstrip p hp)) (fun p hp => hker0 p (hstrip p hp))
  have hwidth := contour_vertical_length_le (q := q) hT
  have hleftbudget : E*R^5*K*Real.sqrt X*(2*T+2) ≤ 2*E*K*Real.sqrt X*R^6 := by
    calc
      _ ≤ E*R^5*K*Real.sqrt X*(2*R) := by gcongr
      _ = _ := by ring
  have hinv' : (right-1)⁻¹ = Real.log X := hinv
  have hpow' : X^right = Real.exp 1*X := hpow
  rw [hinv',hpow'] at htotal
  have hab := habsorb (Real.sqrt X) (X/T^A) (upperZeroWeight χ hχ (T+1) X A) R
    (Real.log X) (Real.sqrt_nonneg _) (by positivity)
    (upperZeroWeight_nonneg χ hχ _ _ _ hXp.le) hR hlog
  calc
    _ ≤ K*(upperZeroWeight χ hχ (T+1) X A+Real.sqrt X*(M*R^5)) +
        2*E*K*Real.sqrt X*R^6 + 4*(E*R^5)*K*(Real.exp 1*X)/T^A +
        2*(Real.log X+D)*K*(Real.exp 1*X)/T^A*smoothTailIntegral := by
      change _ ≤ _ at htotal
      have hz := hzero
      change (∑ p ∈ S, (zeroMultiplicity χ p:ℝ)*X^p.re*‖mellin (ρ:ℝ→ℂ) p‖) ≤
        K*(upperZeroWeight χ hχ (T+1) X A+Real.sqrt X*(M*R^5)) at hz
      exact htotal.trans (by gcongr)
    _ = K*upperZeroWeight χ hχ (T+1) X A + K*M*Real.sqrt X*R^5 +
        2*E*K*Real.sqrt X*R^6 + 4*E*K*Real.exp 1*(X/T^A)*R^5 +
        2*K*Real.exp 1*smoothTailIntegral*(X/T^A)*(Real.log X+D) := by ring
    _ ≤ C*(upperZeroWeight χ hχ (T+1) X A+Real.sqrt X*R^7+(X/T^A)*R^7*(1+Real.log X)^7) := hab
    _ = _ := by dsimp [R]; ring

end Ostmann.Dirichlet

end

end OAI
