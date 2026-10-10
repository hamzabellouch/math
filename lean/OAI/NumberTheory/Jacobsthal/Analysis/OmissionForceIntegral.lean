import OAI.NumberTheory.Jacobsthal.Estimates.OmissionSeries

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.ReferenceAdmission

theorem reciprocal_square_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b,(x^2)⁻¹)=a⁻¹-b⁻¹ := by
  have hn : ∀ x ∈ uIcc a b,x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (uIcc a b) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hn x hx))
  have hd : ∀ x ∈ uIcc a b,HasDerivAt (fun t : ℝ => -t⁻¹) ((x^2)⁻¹) x := by
    intro x hx
    simpa only [neg_neg] using! (hasDerivAt_inv (hn x hx)).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
  ring

theorem omissionForce_odd_integral (r b : ℝ) :
    omissionForce .odd r b=∫ x : ℝ in upperCutoff .odd r b..baseCutoff b,(x^2)⁻¹ := by
  rw [reciprocal_square_integral (upperCutoff_bounds .odd r b).1 (cutoff_le_base .odd r b)]
  rfl

theorem literal_omission_window (r b x : ℝ) :
    x ∈ Ioc (upperCutoff .odd r b) (baseCutoff b) ↔
      1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ ¬childAdmitted .odd r x := by
  constructor
  · intro hx
    have hx1 : 1 < x := (upperCutoff_bounds .odd r b).1.trans_lt hx.1
    have he : x ∈ Ioc 1 (upperCutoff .even r b) := ⟨hx1,hx.2⟩
    obtain ⟨_,hx2,hxb,_⟩ := (mem_upperCutoff .even r b x).mp he
    refine ⟨hx1,hx2,hxb,?_⟩
    intro hgate
    have ha := (mem_upperCutoff .odd r b x).mpr ⟨hx1,hx2,hxb,hgate⟩
    exact (not_lt_of_ge ha.2) hx.1
  · rintro ⟨hx1,hx2,hxb,hbad⟩
    have he := (mem_upperCutoff .even r b x).mpr ⟨hx1,hx2,hxb,trivial⟩
    refine ⟨?_,he.2⟩
    apply lt_of_not_ge
    intro hcap
    exact hbad ((mem_upperCutoff .odd r b x).mp ⟨hx1,hcap⟩).2.2.2

end ErdosContinuousOmission

end

end Erdos970

end OAI
