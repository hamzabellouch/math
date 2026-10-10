import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSymmetry
import OAI.Probability.SKBarriers.Parisi.CDFChainAverage
import OAI.Probability.SKBarriers.Parisi.CDFOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchyAverage_nonneg_le_one (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : Continuous g)
    (hb : ∀ y, g y∈Icc (0:ℝ) 1) (x : ℝ) :
    scalarHierarchyAverage n m v f g x∈Icc (0:ℝ) 1 := by
  have hb' : ∀ y, |g y|≤(1:ℝ) := fun y => by rw [abs_of_nonneg (hb y).1]; exact (hb y).2
  rw [scalarHierarchyAverage_eq_integral n m v hf hg zero_le_one hb' x]
  have := hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  refine ⟨integral_nonneg (fun z => (hb _).1),?_⟩
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (C:=1) (f:=fun z => g (x+coordinateLinear n v z))
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb' (x+coordinateLinear n v z)))
  exact (le_abs_self _).trans (by simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs] using H)

theorem scalarCDFAverage_nonneg_le_one (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hg : ∀ y, HasDerivAt g (dg y) y)
    (hdg : Continuous dg) {K C : ℝ≥0} (hfK : LipschitzWith K f)
    (hb : ∀ y, g y∈Icc (0:ℝ) 1) (hC : ∀ y, |dg y|≤C)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    scalarCDFAverage β α s t f g x∈Icc (0:ℝ) 1 := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  have hB : ∀ y, |g y|≤(1:ℝ≥0) := fun y => by rw [abs_of_nonneg (hb y).1]; exact (hb y).2
  have H := dyadicScalarAverage_tendsto β hα hmono hf (boundedPrimitive_regular hg hdg hB hC)
    (boundedPrimitive_hasDerivAt hc) hg hfK (boundedPrimitive_lipschitz hc hB) hB hC s t ht x
  apply isClosed_Icc.mem_of_tendsto H
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_nonneg_le_one _ _ _ hf hc hb x)

theorem scalarCDFGradient_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) : scalarCDFGradient β α s t 0=0 := by
  have H := (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at 0
  have he (n : ℕ) : rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) 0=0 := by
    simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
    exact scalarHierarchy_spin_gradient_zero _ _ _
  simp only [he] at H
  exact tendsto_nhds_unique H tendsto_const_nhds

theorem scalarCDFOverlap_nonneg_le_one (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : scalarCDFOverlap β α q∈Icc (0:ℝ) 1 := by
  have ht : Real.toNNReal (1-q)≤1 := by exact_mod_cast Real.toNNReal_le_iff_le_coe.mpr (by simpa using hq.1)
  have hq' : Real.toNNReal q≤1 := Real.toNNReal_le_iff_le_coe.mpr hq.2
  have HR := scalarCDFGradient_sq_regular β hα hmono q (Real.toNNReal (1-q)) ht
  apply scalarCDFAverage_nonneg_le_one β hα hmono
    (scalarCDFValue_regular β hα hmono q (Real.toNNReal (1-q)) ht)
    HR.1 HR.2.1 (scalarCDFValue_lipschitz β hα hmono q (Real.toNNReal (1-q)) ht)
    (fun z => ⟨sq_nonneg _,(le_abs_self ((scalarCDFGradient β α q (Real.toNNReal (1-q)) z)^2)).trans (HR.2.2.1 z)⟩)
    (C:=2) HR.2.2.2 0 (Real.toNNReal q) hq' 0

theorem scalarCDFOverlap_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) : scalarCDFOverlap β α 0=0 := by
  have HR := scalarCDFGradient_sq_regular β hα hmono 0 1 le_rfl
  have HE := scalarCDFAverage_eq_chainAverage
    (scalarCDFValue_regular β hα hmono 0 1 le_rfl) HR.1 HR.2.1
    (scalarCDFValue_lipschitz β hα hmono 0 1 le_rfl) (B:=1) HR.2.2.1 (C:=2) HR.2.2.2 β hα hmono
    [] (by simp) 0 0 (by norm_num) rfl trivial 0
  simpa only [scalarCDFOverlap,sub_zero,Real.toNNReal_one,Real.toNNReal_zero,
    scalarTimeChainAverage,List.length_nil,scalarHierarchyAverage,scalarCDFGradient_zero β hα hmono 0 1 le_rfl,zero_pow (by decide : 2≠0)] using HE

end SK.Analytic

end
end

end OAI
