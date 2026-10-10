import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualCommonCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessProbability

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_actual_selected_common_center (d : Decomposition)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ F : Finset ℕ,F.card=auxiliaryK Z z →
      (∀p∈F,BalancedResiduePrime d p) →
      (∀p∈F,z≤p) → (∀p∈F,p<Z) →
      ((∏p∈F,p:ℕ):ℝ) ≤ (Z:ℝ)^(1/50:ℝ) →
      ∀ P : Finset ℕ,(∀r∈P,r.Prime) → (∀r∈P,Odd r) →
      (∀r∈P,Z≤r ∧ r≤2*Z) → c*(Z:ℝ)/Real.log Z ≤ P.card →
      ∀ ε t : ℕ→ℤ,(∀r∈P,ε r = -1 ∨ ε r = 1) →
      (∀r∈P,δ/4 ≤ (∑a∈positiveIntegerWindow d.A (parameterX T),
        ((ε r*jacobiSym (a-t r) r:ℤ):ℝ))/(positiveIntegerWindow d.A (parameterX T)).card) →
      ∃ h : ℤ, ∃ m : ℕ, ∃ P₀ : Finset ℕ,
        0 < m ∧ m ≤ quadraticLiftMultiplierBound Z ∧ IsCoprime h (m:ℤ) ∧
        h.natAbs ≤ quadraticLiftHeight (parameterX T) Z ∧ P₀ ⊆ P ∧
        commonCenterCutoff Z ≤ P₀.card ∧
        commonCenterMomentScale P.card Z (evenMomentParameter (parameterX T) Z)/4 ≤
          2*(P.card:ℝ)*(P₀.card:ℝ)^(evenMomentParameter (parameterX T) Z-1) ∧
        ∀p∈P₀,(p:ℤ) ∣ h-(m:ℤ)*t p := by
  classical
  filter_upwards [eventually_actual_witness_probability d c δ hc hδ,
    eventually_common_center_of_witness_probability c 6 hc (by norm_num)] with T hprob hcenter
  intro Z z hZl hZu hz hzl hzu F hcard hbal hlow hhigh hprod P hP ho hband hJ ε t hε hbias
  let : ∀p:F,NeZero p.val := fun p => ⟨(balancedResiduePrime_prime (hbal p p.property)).ne_zero⟩
  let : NeZero (∏p:F,p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  have hF : ∀p∈F,p.Prime := fun p hp => balancedResiduePrime_prime (hbal p hp)
  have hLeq : (∏p:F,p.val) = ∏p∈F,p := Finset.prod_coe_sort F (fun p:ℕ => p)
  have hsf : Squarefree (∏p:F,p.val) := by
    simpa only [hLeq] using canonicalAuxiliary_full_squarefree hF
  have hsize : (((∏p:F,p.val):ℕ):ℝ) ≤ (Z:ℝ)^(1/50:ℝ) := by
    simpa only [hLeq] using hprod
  exact hcenter Z z (∏p:F,p.val) hZl hZu hz hzl hzu hsf hsize
    (quadraticResidueFamily d) P hP hband hJ t
    (hprob Z z hZl hZu hz hzl hzu F hcard hbal hlow hhigh hprod
      P hP ho hband hJ ε t hε hbias)

end Ostmann.QuadraticCenter

end

end OAI
