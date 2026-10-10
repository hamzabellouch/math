import Mathlib
import OAI.Probability.SKGap.Localization.SusceptibilityMiddle

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma cutoff_square_derivative (C : Observables n) {s A : ℝ} (hs : 0<s) (hA : 0≤A)
    (hc : ∀x,|C x|≤1) (hd : ∀x,‖derivativeVector C x‖≤A/s) :
    ∀x,∑i,(halfDiff i (fun y=>(C y)^2) x)^2≤(4*A/s)^2 := by
  intro x
  have H:=derivativeVector_mul_bound C C x hc hc (div_nonneg hA hs.le) (div_nonneg hA hs.le) (hd x) (hd x)
  have H' : ‖derivativeVector (fun y=>(C y)^2) x‖≤4*A/s := by
    simpa only [←sq] using H.trans_eq (show 2*(A/s+A/s)=4*A/s by ring)
  simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) H' 2

lemma cutoff_susceptibility_star (P C L : Observables n) (hP : ∀x,0≤P x)
    (hp : ∑x,P x=1) {s A B D : ℝ} (hs : 0<s) (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (hc : ∀x,|C x|≤1) (hdC : ∀x,‖derivativeVector C x‖≤A/s)
    (hL : ∀x,|L x|≤B*s) (hdL : ∀x,‖derivativeVector L x‖≤D) :
    starSquared P (fun x=>(C x)^2*L x)≤
      (∑x,P x*(C x*L x)^2)+(32*A^2*B^2+2*D^2) := by
  have hc2 : ∀x,|(C x)^2|≤1 := by
    intro x
    simpa only [sq_abs,abs_sq,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hc x) 2
  have hdC2:=cutoff_square_derivative C hs hA hc hdC
  have hdL2 : ∀x,∑i,(halfDiff i L x)^2≤D^2 := by
    intro x
    simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) (hdL x) 2
  have hg:= (scalar_product_bounds (fun x=>(C x)^2) L (by norm_num) (by positivity)
    (mul_nonneg hB hs.le) hD hc2 hdC2 hL hdL2).2
  have he : varianceEnergy P (fun x=>(C x)^2*L x)≤32*A^2*B^2+2*D^2 := by
    have H:=varianceEnergy_gradient_bound P hP hp (fun x=>(C x)^2*L x) hg
    rw [Real.sq_sqrt (by positivity)] at H
    convert H using 1
    field_simp
    ring
  have hv : (∑x,P x*((C x)^2*L x)^2)≤∑x,P x*(C x*L x)^2 := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hP x)
    have H : (C x)^2≤1 := by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hc x) 2
    have H':=mul_le_mul_of_nonneg_right H (sq_nonneg (C x*L x))
    nlinarith only [H']
  exact add_le_add hv he

end SKGapCutoff.Static

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static

theorem literalSusceptibility_cutoff_test (j K B ρ : ℝ) (hK : 0≤K) (hB : 0≤B)
    (hρ : 0<ρ) (k : ℕ) :
    ∃D≥0,∀n:ℕ,0<n→∀(J:Interaction n) (h r:Fin n→ℝ) (P:Observables n),
      (∀x,0≤P x)→(∑x,P x=1)→SKGap.opNorm J≤K→
      (∀x l,l<k+3→ShapeBound (formalField j J h x l) B)→
      let C:=residualCutoff ρ j J h k
      let L:=literalSusceptibility (fld j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r
      starSquared P (fun x=>(C x)^2*L x)≤(∑x,P x*(C x*L x)^2)+D := by
  obtain ⟨S,hS,hdL⟩:=literalSusceptibility_global_derivative j K B hK hB k
  obtain ⟨Q,hQ⟩:=residualScalarCutoff_lipschitz
  let U:=residualDerivativeBudget j K B k
  let V:=residualDerivativeBudget j K B (k+1)
  let A:=2*(Q:ℝ)/ρ^2*((4*U+2*U^2)+(4*V+2*V^2))
  have hU : 0≤U:=residualDerivativeBudget_nonneg hK hB _
  have hV : 0≤V:=residualDerivativeBudget_nonneg hK hB _
  have hA : 0≤A:=by dsimp [A];positivity
  refine ⟨32*A^2*(Real.exp (|j|/2)+1)^2+2*S^2,by positivity,?_⟩
  intro n hn J h r P hP hp hop hformal
  dsimp only
  apply cutoff_susceptibility_star P _ _ hP hp (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
    hA (by positivity) hS
  · intro x
    rw [abs_of_nonneg (residualCutoff_bounds ρ j J h k x).1]
    exact (residualCutoff_bounds ρ j J h k x).2
  · intro x
    exact residualCutoff_gradient hn hρ hQ J h k x hU hV
      (residual_derivative_bound hn hK hB J h hop k (fun v l hl=>hformal v l (by omega)) x)
      (residual_derivative_bound hn hK hB J h hop (k+1) (fun v l hl=>hformal v l (by omega)) x)
  · exact literalSusceptibility_global_size hn j J h r (k+1)
  · exact hdL n hn J h r hop hformal

end SKGapCutoff.Recipe

end
end
end

end OAI
