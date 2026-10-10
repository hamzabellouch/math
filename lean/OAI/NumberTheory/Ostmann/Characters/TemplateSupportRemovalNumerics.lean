import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open Filter
open scoped Topology BigOperators

theorem familyRemovalCost_le {κ : Type*} (D : Finset κ) (degree : κ → ℕ)
    {A α β H Z : ℝ} (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hdegree : ∀ q ∈ D, (degree q : ℝ) ≤ Z) :
    A*(∑ q ∈ D, ((degree q : ℝ)*α+β*(H/Real.log 2))) ≤
      A*(D.card:ℝ)*(Z*α+β*(H/Real.log 2)) := by
  calc
    _ ≤ A*(∑ _q ∈ D, (Z*α+β*(H/Real.log 2))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Finset.sum_le_sum (fun q hq => add_le_add
        (mul_le_mul_of_nonneg_right (hdegree q hq) hα) le_rfl)
    _ = _ := by simp; ring

theorem removalCost_exponential_bound {A N Z H α β P c t : ℝ}
    (_hA0 : 0 ≤ A) (hN0 : 0 ≤ N) (hZ0 : 0 ≤ Z) (hH0 : 0 ≤ H)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hP0 : 0 ≤ P)
    (hA : A ≤ Real.exp P) (hN : N ≤ Real.exp P) (hZ : Z ≤ Real.exp P)
    (hH : H ≤ Real.exp (2*P))
    (hα : α ≤ Real.exp (-c*t)) (hβ : β ≤ Real.exp (-c*t)) :
    A*N*(Z*α+β*(H/Real.log 2)) ≤
      (1+(Real.log 2)⁻¹)*Real.exp (4*P-c*t) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  calc
    _ ≤ Real.exp P*Real.exp P*
        (Real.exp P*Real.exp (-c*t)+Real.exp (-c*t)*(Real.exp (2*P)/Real.log 2)) := by gcongr
    _ = Real.exp (3*P-c*t)+Real.exp (4*P-c*t)/Real.log 2 := by
      rw [mul_add]
      have he1 : Real.exp P*Real.exp P*(Real.exp P*Real.exp (-c*t))=Real.exp (3*P-c*t) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      have he2 : Real.exp P*Real.exp P*(Real.exp (-c*t)*(Real.exp (2*P)/Real.log 2))=
          Real.exp (4*P-c*t)/Real.log 2 := by
        rw [← mul_div_assoc,← mul_div_assoc]
        congr 1
        simp only [← Real.exp_add]
        congr 1
        ring
      rw [he1,he2]
    _ ≤ Real.exp (4*P-c*t)+Real.exp (4*P-c*t)/Real.log 2 :=
      add_le_add (Real.exp_le_exp.mpr (by linarith)) le_rfl
    _ = _ := by ring

theorem eventually_removalCost_small (C z : ℝ) (d : ℕ) {a c : ℝ}
    (hC : 0 ≤ C) (hz : 0 ≤ z) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ A N Z H α β : ℝ,
      0 ≤ A → 0 ≤ N → 0 ≤ Z → 0 ≤ H → 0 ≤ α → 0 ≤ β →
      A ≤ Real.exp (historyPolynomialCost C z d L) →
      N ≤ Real.exp (historyPolynomialCost C z d L) →
      Z ≤ Real.exp (historyPolynomialCost C z d L) →
      H ≤ Real.exp (2*historyPolynomialCost C z d L) →
      α ≤ Real.exp (-c*Real.exp (a*L)) → β ≤ Real.exp (-c*Real.exp (a*L)) →
      A*N*(Z*α+β*(H/Real.log 2)) ≤ Real.exp (-(c/2)*Real.exp (a*L)) := by
  let K : ℝ := 1+(Real.log 2)⁻¹
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  have ht : Tendsto (fun L : ℝ => Real.exp (a*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
  filter_upwards [eventually_historyPolynomialCost_le (4*C) z d hz ha (by positivity : 0<c/4),
    ht.eventually (eventually_ge_atTop (4*Real.log K/c))] with L hpoly hconstant
  intro A N Z H α β hA0 hN0 hZ0 hH0 hα0 hβ0 hA hN hZ hH hα hβ
  have hP0 : 0 ≤ historyPolynomialCost C z d L := by unfold historyPolynomialCost; positivity
  have hpoly' : 4*historyPolynomialCost C z d L ≤ (c/4)*Real.exp (a*L) := by
    convert hpoly using 1
    simp only [historyPolynomialCost]
    ring
  have hconst := (div_le_iff₀ hc).mp hconstant
  calc
    _ ≤ K*Real.exp (4*historyPolynomialCost C z d L-c*Real.exp (a*L)) :=
      removalCost_exponential_bound hA0 hN0 hZ0 hH0 hα0 hβ0 hP0 hA hN hZ hH hα hβ
    _ = Real.exp (Real.log K+4*historyPolynomialCost C z d L-c*Real.exp (a*L)) := by
      rw [show Real.log K+4*historyPolynomialCost C z d L-c*Real.exp (a*L)=
        Real.log K+(4*historyPolynomialCost C z d L-c*Real.exp (a*L)) by ring,
        Real.exp_add,Real.exp_log hK]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
