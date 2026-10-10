import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFIntervalConvergence
import OAI.Probability.SKBarriers.Parisi.CDFUniformAverage
import OAI.Probability.SKBarriers.Gaussian.BoundedProduct

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFConditionalSusceptibility (β : ℝ) (α : ℝ → ℝ) (r q : ℝ) : ℝ → ℝ :=
  scalarCDFAverage β α r (Real.toNNReal (q-r))
    (scalarCDFValue β α q (Real.toNNReal (1-q)))
    (scalarCDFHessian β α q (Real.toNNReal (1-q)))

def scalarCDFJointSusceptibility (β : ℝ) (α : ℝ → ℝ) (r q : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal r)
    (scalarCDFValue β α r (Real.toNNReal (1-r)))
    (fun x => scalarCDFHessian β α r (Real.toNNReal (1-r)) x*
      scalarCDFConditionalSusceptibility β α r q x) 0

def conditionalSusceptibilityLipschitz : ℝ≥0 := susceptibilityLipschitzConstant+2*Real.toNNReal (Real.exp 2)

theorem scalarCDFConditionalSusceptibility_regular (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    LipschitzWith conditionalSusceptibilityLipschitz (scalarCDFConditionalSusceptibility β α r q) ∧
      ∀ x,|scalarCDFConditionalSusceptibility β α r q x|≤1 := by
  have hs : Real.toNNReal (1-q)≤1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-r)≤1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have H := scalarCDFAverage_lipschitz β ha hm
    (scalarCDFValue_regular β ha hm q _ hs) (scalarCDFValue_lipschitz β ha hm q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) r _ ht
  refine ⟨?_,fun x => scalarCDFAverage_abs_le β ha hm
    (scalarCDFValue_regular β ha hm q _ hs) (scalarCDFValue_lipschitz β ha hm q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) r _ ht x⟩
  simpa only [scalarCDFConditionalSusceptibility,conditionalSusceptibilityLipschitz,NNReal.coe_one,mul_one] using H

theorem scalarCDFConditionalSusceptibility_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    TendstoUniformly (fun n => scalarCDFConditionalSusceptibility β (αn n) r q)
      (scalarCDFConditionalSusceptibility β α r q) atTop := by
  have hs0 : (Real.toNNReal (1-q):ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have ht0 : (Real.toNNReal (q-r):ℝ)=q-r := Real.coe_toNNReal _ (by linarith)
  have hs : Real.toNNReal (1-q)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-r)≤1 := by rw [← NNReal.coe_le_coe,ht0,NNReal.coe_one]; linarith
  exact scalarCDFAverage_tendstoUniformly_varying β ha hm hn hnm hD
    (scalarCDFValue_regular β ha hm q _ hs) (fun n => scalarCDFValue_regular β (hn n) (hnm n) q _ hs)
    (scalarCDFValue_lipschitz β ha hm q _ hs) (fun n => scalarCDFValue_lipschitz β (hn n) (hnm n) q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) q _ hs)
    (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) (fun n => scalarCDFHessian_abs_le_one β (hn n) (hnm n) q _ hs)
    (scalarCDFValue_tendstoUniformly_interval β ha hm hn hnm hD q _ hs (hr.trans hrq) (by rw [hs0]; linarith))
    (scalarCDFHessian_tendstoUniformly_interval β ha hm hn hnm hD q _ hs (hr.trans hrq) (by rw [hs0]; linarith))
    r _ ht hr (by rw [ht0]; linarith)

def scalarCDFJointSusceptibilityTest (β : ℝ) (α : ℝ → ℝ) (r q : ℝ) : ℝ → ℝ :=
  fun x => scalarCDFHessian β α r (Real.toNNReal (1-r)) x*scalarCDFConditionalSusceptibility β α r q x

theorem scalarCDFJointSusceptibilityTest_regular (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    LipschitzWith (susceptibilityLipschitzConstant+conditionalSusceptibilityLipschitz)
      (scalarCDFJointSusceptibilityTest β α r q) ∧
    ∀ x,|scalarCDFJointSusceptibilityTest β α r q x|≤1 := by
  have hs : Real.toNNReal (1-r)≤1 := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have H := scalarCDFConditionalSusceptibility_regular β ha hm hr hrq hq
  refine ⟨unitBoundedProduct_lipschitz (scalarCDFHessian_lipschitz β ha hm r _ hs) H.1
    (scalarCDFHessian_abs_le_one β ha hm r _ hs) H.2,?_⟩
  intro x
  exact unitBoundedProduct_abs_le (scalarCDFHessian_abs_le_one β ha hm r _ hs x) (H.2 x)

theorem scalarCDFJointSusceptibilityTest_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    TendstoUniformly (fun n => scalarCDFJointSusceptibilityTest β (αn n) r q)
      (scalarCDFJointSusceptibilityTest β α r q) atTop := by
  have hs0 : (Real.toNNReal (1-r):ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hs : Real.toNNReal (1-r)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  exact unitBoundedProduct_tendstoUniformly
    (fun n => (scalarCDFConditionalSusceptibility_regular β (hn n) (hnm n) hr hrq hq).2)
    (scalarCDFHessian_abs_le_one β ha hm r _ hs)
    (scalarCDFHessian_tendstoUniformly_interval β ha hm hn hnm hD r _ hs hr (by rw [hs0]; linarith))
    (scalarCDFConditionalSusceptibility_tendstoUniformly β ha hm hn hnm hD hr hrq hq)

theorem scalarCDFJointSusceptibility_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    Tendsto (fun n => scalarCDFJointSusceptibility β (αn n) r q) atTop
      (𝓝 (scalarCDFJointSusceptibility β α r q)) := by
  have hs0 : (Real.toNNReal (1-r):ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have ht0 : (Real.toNNReal r:ℝ)=r := Real.coe_toNNReal _ hr
  have hs : Real.toNNReal (1-r)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  have ht : Real.toNNReal r≤1 := by rw [← NNReal.coe_le_coe,ht0,NNReal.coe_one]; linarith
  have hg := scalarCDFJointSusceptibilityTest_regular β ha hm hr hrq hq
  have hgn (n) := scalarCDFJointSusceptibilityTest_regular β (hn n) (hnm n) hr hrq hq
  have HP := scalarCDFJointSusceptibilityTest_tendstoUniformly β ha hm hn hnm hD hr hrq hq
  exact (scalarCDFAverage_tendstoUniformly_varying β ha hm hn hnm hD
    (scalarCDFValue_regular β ha hm r _ hs) (fun n => scalarCDFValue_regular β (hn n) (hnm n) r _ hs)
    (scalarCDFValue_lipschitz β ha hm r _ hs) (fun n => scalarCDFValue_lipschitz β (hn n) (hnm n) r _ hs)
    hg.1 (fun n => (hgn n).1)
    (B:=1) hg.2 (fun n => (hgn n).2)
    (scalarCDFValue_tendstoUniformly_interval β ha hm hn hnm hD r _ hs hr (by rw [hs0]; linarith)) HP
    0 _ ht le_rfl (by rw [ht0]; linarith)).tendsto_at 0

end SK.Analytic

end
end

end OAI
