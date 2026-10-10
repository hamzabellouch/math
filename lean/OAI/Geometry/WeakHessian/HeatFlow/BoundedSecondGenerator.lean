import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric
import OAI.Geometry.WeakHessian.HeatFlow.CheegerScaledResolventNonneg

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile201
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

omit [MetricSpace X] in
lemma lp_scaled_sub_bounded {u v : Lp ℝ 2 m} {B C a : ℝ}
    (hu : ∀ᵐ x ∂m,|u x| ≤ B) (hv : ∀ᵐ x ∂m,|v x| ≤ C) :
    ∀ᵐ x ∂m,|(a • (u-v)) x| ≤ |a| *(B+C) := by
  filter_upwards [hu,hv,Lp.coeFn_smul a (u-v),Lp.coeFn_sub u v] with x hx hy hs hd
  rw [hs,Pi.smul_apply,smul_eq_mul,hd,Pi.sub_apply,abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hx hy)) (abs_nonneg _)

lemma cheeger_double_resolvent_core (h : QuadraticCheegerEnergy m)
    {t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (u : Lp ℝ 2 m)
    (hub : ∀ᵐ x ∂m,|u x| ≤ B) :
    ∃ v A AA : Lp ℝ 2 m,
      v = ((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear
        (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) ∧
      (cheeger_closedQuadraticEnergy h).IsFormGenerator v A ∧
      (cheeger_closedQuadraticEnergy h).IsFormGenerator A AA ∧
      (∀ᵐ x ∂m,|v x| ≤ B) ∧
      (∀ᵐ x ∂m,|A x| ≤ |t⁻¹| *(B+B)) ∧
      (∀ᵐ x ∂m,|AA x| ≤ |t⁻¹| *(|t⁻¹| *(B+B)+|t⁻¹| *(B+B))) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := (Q.scale ht).resolventLinear
  let v := R (R u)
  let A := t⁻¹ • (v-R u)
  let Au := t⁻¹ • (R u-u)
  have hg : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht (R u) v).mp rfl
  have hu : Q.IsFormGenerator (R u) Au := (Q.scaled_resolvent_iff ht u (R u)).mp rfl
  have hA : Q.IsFormGenerator A (t⁻¹ • (A-Au)) := Q.formGenerator_smul _ (Q.formGenerator_sub hg hu)
  have hb1 : ∀ᵐ x ∂m,|R u x| ≤ B := cheeger_scaled_resolvent_bounded h ht hB u hub
  have hb2 : ∀ᵐ x ∂m,|v x| ≤ B := cheeger_scaled_resolvent_bounded h ht hB (R u) hb1
  have hbA : ∀ᵐ x ∂m,|A x| ≤ |t⁻¹| *(B+B) := lp_scaled_sub_bounded hb2 hb1
  have hbAu : ∀ᵐ x ∂m,|Au x| ≤ |t⁻¹| *(B+B) := lp_scaled_sub_bounded hb1 hub
  exact ⟨v,A,t⁻¹ • (A-Au),rfl,hg,hA,hb2,hbA,lp_scaled_sub_bounded hbA hbAu⟩

lemma cheeger_double_resolvent_nonneg (h : QuadraticCheegerEnergy m)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x) :
    ∀ᵐ x ∂m,0 ≤ ((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear
      (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x :=
  cheeger_scaled_resolvent_nonneg h ht _ (cheeger_scaled_resolvent_nonneg h ht u hu)

variable [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable [IsLocallyFiniteMeasure m]

lemma cheeger_double_resolvent_tendsto (h : QuadraticCheegerEnergy m)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : ∀ i,0 < t i)
    (hl : Tendsto t l (𝓝 0)) (u : Lp ℝ 2 m) :
    Tendsto (fun i => ((cheeger_closedQuadraticEnergy h).scale (ht i)).resolventLinear
      (((cheeger_closedQuadraticEnergy h).scale (ht i)).resolventLinear u)) l (𝓝 u) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := fun i => (Q.scale (ht i)).resolventLinear
  have H : Tendsto (fun i => R i u) l (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) ht hl u
  have hb (i : ι) : ‖R i (R i u)-u‖ ≤ 2*‖R i u-u‖ := by
    calc
      _ ≤ ‖R i (R i u)-R i u‖+‖R i u-u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖R i (R i u-u)‖+‖R i u-u‖ := by rw [map_sub]
      _ ≤ ‖R i u-u‖+‖R i u-u‖ := by
        gcongr
        exact ((R i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right
          (Q.scale (ht i)).resolvent_norm_le_one (norm_nonneg _)).trans_eq (one_mul _))
      _ = _ := by ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [sub_self,norm_zero,mul_zero] using (H.sub_const u).norm.const_mul 2
end WeakHessian

end
end InlinedFile201

end OAI
