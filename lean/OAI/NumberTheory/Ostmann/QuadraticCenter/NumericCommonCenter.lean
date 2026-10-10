import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterParameters
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterWitness

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

structure CommonCenterNumericInputs (X Z J k E : ℕ) : Prop where
  multiplier_pos : 0 < quadraticLiftMultiplierBound Z
  multiplier_lt : quadraticLiftMultiplierBound Z < Z
  k_ten_le : 10 ≤ k
  mass_pos : 0 < commonCenterMass J Z k
  mass_lower : commonCenterMomentScale J Z k/4 ≤ (commonCenterMass J Z k:ℝ)
  budget : commonCenterMass J Z k +
    commonCenterCutoff Z^(k-(k-10)) *
      (J^(k-10)*(2*quadraticLiftHeight X Z/Z^(k-10)+1)) ≤
        k.factorial*E/quadraticLiftMultiplierBound Z
  spacing : 2*quadraticLiftHeight X Z < Z^(k+1)
  gap : 2*k*J ≤ commonCenterCutoff Z^2

theorem commonCenter_numeric_inputs {X Z J k E K : ℕ} {C : ℝ}
    (h : CommonCenterElementaryBounds X Z J k)
    (hcost : C*(K:ℝ)≤Real.log Z/1000)
    (hprob : Real.exp (-C*K)≤(E:ℝ)/(J.choose k:ℝ)) :
    CommonCenterNumericInputs X Z J k E := by
  have hupper := h.event_quotient_lower hcost hprob
  have hmass := commonCenterMass_moment_input J Z k
    (J^(k-10)*(2*quadraticLiftHeight X Z/Z^(k-10)+1))
    (k.factorial*E/quadraticLiftMultiplierBound Z) h.momentScale_large
    h.lower_moment_negligible hupper
  refine ⟨h.multiplier_pos,h.multiplier_lt,h.k_ten_le,hmass.1,
    (commonCenterMass_bounds J Z k h.momentScale_large).2.1,?_,h.height_spacing,h.incidence_gap⟩
  have he : k-(k-10)=10 := by have := h.k_ten_le; omega
  simpa only [he] using hmass.2

theorem eventually_commonCenter_numeric_inputs (c C : ℝ) (hc : 0<c) (hC : 0<C) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2≤Real.log Z → Real.log Z≤2*T →
      1≤z → T^auxiliaryExponent/2≤Real.log z →
      Real.log z≤2*T^auxiliaryExponent →
      ∀ J E : ℕ, c*(Z:ℝ)/Real.log Z≤(J:ℝ) → J≤2*Z →
      Real.exp (-C*(auxiliaryK Z z:ℝ))≤
        (E:ℝ)/(J.choose (evenMomentParameter (parameterX T) Z):ℝ) →
      CommonCenterNumericInputs (parameterX T) Z J
        (evenMomentParameter (parameterX T) Z) E := by
  filter_upwards [eventually_commonCenterElementaryBounds c hc,
    eventually_auxiliaryK_le_log (1/(1000*C)) (by positivity)] with T he hK
  intro Z z hZl hZu hz hzl hzu J E hJ hJu hprob
  have hk := hK Z z hZl hZu hz hzl hzu
  have hcost : C*(auxiliaryK Z z:ℝ)≤Real.log Z/1000 := by
    have hh := mul_le_mul_of_nonneg_left hk hC.le
    have hid : C*(1/(1000*C)*Real.log Z)=Real.log Z/1000 := by
      field_simp
    simpa only [hid] using hh
  exact commonCenter_numeric_inputs (he Z hZl J hJ hJu) hcost hprob

end Ostmann.QuadraticCenter

end

end OAI
