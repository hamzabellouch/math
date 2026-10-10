import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Rational Reparam. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent.RationalCurve
variable {X : ComplexManifold.{u}} (g : RationalCurve X)

 
def homogeneousValue (a b : ℂ) : X.Carrier :=
  if b=0 then g.infinity 0 else g.finite (a/b)

lemma homogeneousValue_finite {a b : ℂ} (hb : b≠0) :
    g.homogeneousValue a b = g.finite (a/b) := ite_eq_right hb

lemma homogeneousValue_infinity {a b : ℂ} (ha : a≠0) :
    g.homogeneousValue a b = g.infinity (b/a) := by
  by_cases hb : b=0
  · simp [homogeneousValue,hb]
  · rw [g.homogeneousValue_finite hb,g.overlap (a/b) (div_ne_zero ha hb),inv_div]

lemma homogeneousValue_holomorphicAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : E → ℂ} {z : E} (ha : AnalyticAt ℂ a z) (hb : AnalyticAt ℂ b z)
    (hnz : a z≠0 ∨ b z≠0) :
    ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω (fun y => g.homogeneousValue (a y) (b y)) z := by
  rcases hnz with h | h
  · have H := g.infinity_holomorphic.contMDiffAt.comp z ((hb.div ha h).contDiffAt.contMDiffAt)
    apply H.congr_of_eventuallyEq
    filter_upwards [ha.continuousAt.eventually_ne h] with y hy
    exact g.homogeneousValue_infinity hy
  · have H := g.finite_holomorphic.contMDiffAt.comp z ((ha.div hb h).contDiffAt.contMDiffAt)
    apply H.congr_of_eventuallyEq
    filter_upwards [hb.continuousAt.eventually_ne h] with y hy
    exact g.homogeneousValue_finite hy

lemma homogeneousValue_smul {a b s : ℂ} (hs : s≠0) :
    g.homogeneousValue (s*a) (s*b)=g.homogeneousValue a b := by
  by_cases hb : b=0
  · simp [homogeneousValue,hb]
  · rw [g.homogeneousValue_finite (mul_ne_zero hs hb),g.homogeneousValue_finite hb,
      mul_div_mul_left _ _ hs]

 
def mobius (a b c d : ℂ) (hdet : a*d-b*c≠0) : RationalCurve X where
  finite z := g.homogeneousValue (a*z+b) (c*z+d)
  infinity z := g.homogeneousValue (a+b*z) (c+d*z)
  finite_holomorphic := by
    intro z
    apply g.homogeneousValue_holomorphicAt (by fun_prop) (by fun_prop)
    by_contra! h
    apply hdet
    linear_combination a*h.2-c*h.1
  infinity_holomorphic := by
    intro z
    apply g.homogeneousValue_holomorphicAt (by fun_prop) (by fun_prop)
    by_contra! h
    apply hdet
    linear_combination d*h.1-b*h.2
  overlap z hz := by
    rw [← g.homogeneousValue_smul (a := a+b*z⁻¹) (b := c+d*z⁻¹) hz]
    congr 1 <;> field_simp

 

theorem normalize_endpoints (a b : OnePoint ℂ) (hab : a≠b) :
    ∃ h : RationalCurve X, h.finite 0=g.value a ∧ h.finite 1=g.value b := by
  classical
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => exact (hab rfl).elim
    | coe b =>
      let h := g.mobius (b-1) 1 1 0 (by norm_num)
      refine ⟨h,?_,?_⟩
      · simp [h,mobius,homogeneousValue,value]
      · simp [h,mobius,homogeneousValue,value]
  | coe a =>
    induction b using OnePoint.rec with
    | infty =>
      let h := g.mobius (1-a) a (-1) 1 (by ring_nf; exact one_ne_zero)
      refine ⟨h,?_,?_⟩
      · simp [h,mobius,homogeneousValue,value]
      · simp [h,mobius,homogeneousValue,value]
    | coe b =>
      have hba : b-a≠0 := sub_ne_zero.mpr (fun hh => hab (congrArg OnePoint.some hh.symm))
      let h := g.mobius (b-a) a 0 1 (by simpa using hba)
      refine ⟨h,?_,?_⟩ <;> simp [h,mobius,homogeneousValue,value]

end SplitTangent.RationalCurve

end

end OAI
