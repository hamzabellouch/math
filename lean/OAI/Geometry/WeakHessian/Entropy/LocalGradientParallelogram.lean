import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.Minimal
import OAI.Geometry.WeakHessian.Entropy.PolarAddFourParallelograms

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalSobolev.neg {f : X → ℝ} (hf : LocalSobolev m f) :
    LocalSobolev m (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

lemma LocalSobolev.sub (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) : LocalSobolev m (fun x => f x-g x) :=
  hf.add hfinite hg.neg

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma weakGradient_neg (f : X → ℝ) : weakGradient m (fun x => -f x) =ᵐ[m] weakGradient m f := by
  simpa only [neg_one_mul,abs_neg,abs_one,one_mul] using weakGradient_const_mul (m := m) (-1) f

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gamma_comm (f g : X → ℝ) : gamma m f g =ᵐ[m] gamma m g f := by
  have ep : (fun x => f x+g x) = (fun x => g x+f x) := by funext x; ring
  have em : (fun x => g x-f x) = (fun x => -(f x-g x)) := by funext x; ring
  filter_upwards [weakGradient_neg (m := m) (fun x => f x-g x)] with x hx
  simp only [gamma,ep,em,hx]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gamma_zero_left (g : X → ℝ) : gamma m (fun _ => (0:ℝ)) g =ᵐ[m] 0 := by
  filter_upwards [weakGradient_neg (m := m) g] with x hx
  simp only [gamma,zero_add,zero_sub,hx,sub_self,zero_div,Pi.zero_apply]

def LocalGradientParallelogram (m : Measure X) : Prop :=
  ∀ f g : X → ℝ, LocalSobolev m f → LocalSobolev m g →
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+g y) x)^2 +
      (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2

lemma gamma_add_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m (fun x => f x+g x) h =ᵐ[m] (fun x => gamma m f h x+gamma m g h x) := by
  filter_upwards [hpar _ _ (hf.add hfinite hh) hg, hpar _ _ (hf.sub hfinite hh) hg,
    hpar _ _ (hg.add hfinite hh) hf,hpar _ _ (hg.sub hfinite hh) hf,
    weakGradient_neg (m := m) (fun x => f x-g x-h x),
    weakGradient_neg (m := m) (fun x => f x-g x+h x)] with x h₁ h₂ h₃ h₄ hn₁ hn₂
  exact polar_add_of_four_parallelograms (fun u : X → ℝ => (weakGradient m u x)^2)
    f g h h₁ h₂ h₃ h₄ (congrArg (fun a : ℝ => a^2) hn₁) (congrArg (fun a : ℝ => a^2) hn₂)

lemma gamma_add_right (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m f (fun x => g x+h x) =ᵐ[m] (fun x => gamma m f g x+gamma m f h x) := by
  filter_upwards [gamma_add_left hfinite hpar hg hh hf,gamma_comm (m := m) f (fun x => g x+h x),
    gamma_comm (m := m) g f,gamma_comm (m := m) h f] with x hx h1 h2 h3
  rw [h1,hx,h2,h3]

lemma gamma_neg_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    gamma m (fun x => -f x) g =ᵐ[m] (fun x => -gamma m f g x) := by
  filter_upwards [gamma_add_left hfinite hpar hf hf.neg hg,gamma_zero_left (m := m) g] with x hx h0
  simp only [add_neg_cancel] at hx
  change gamma m (fun _ => (0:ℝ)) g x = 0 at h0
  linarith

lemma gamma_sub_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m (fun x => f x-g x) h =ᵐ[m] (fun x => gamma m f h x-gamma m g h x) := by
  filter_upwards [gamma_add_left hfinite hpar hf hg.neg hh,gamma_neg_left hfinite hpar hg hh] with x hx hn
  simpa only [hn,← sub_eq_add_neg] using hx

lemma weakGradient_dist_le (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, |weakGradient m f x-weakGradient m g x| ≤ weakGradient m (fun y => f y-g y) x := by
  have e : (fun x => g x-f x) = (fun x => -(f x-g x)) := by funext x; ring
  filter_upwards [weakGradient_add_le hfinite (hf.sub hfinite hg) hg,
    weakGradient_add_le hfinite (hg.sub hfinite hf) hf,
    weakGradient_neg (m := m) (fun x => f x-g x)] with x h₁ h₂ hn
  simp only [sub_add_cancel] at h₁ h₂
  rw [e,hn] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma weakGradient_const_mul_add_tendsto (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {cs : ℕ → ℝ} {c : ℝ} (hc : Tendsto cs atTop (𝓝 c)) :
    ∀ᵐ x ∂m, Tendsto (fun n => weakGradient m (fun y => cs n*f y+g y) x) atTop
      (𝓝 (weakGradient m (fun y => c*f y+g y) x)) := by
  have hdist (n : ℕ) : ∀ᵐ x ∂m,
      dist (weakGradient m (fun y => cs n*f y+g y) x) (weakGradient m (fun y => c*f y+g y) x) ≤
      |cs n-c| * weakGradient m f x := by
    have he : (fun y => (cs n*f y+g y)-(c*f y+g y)) = (fun y => (cs n-c)*f y) := by funext y; ring
    filter_upwards [weakGradient_dist_le hfinite ((hf.const_mul (cs n)).add hfinite hg)
      ((hf.const_mul c).add hfinite hg),weakGradient_const_mul (m := m) (cs n-c) f] with x hx hmul
    simpa only [he,hmul,Real.dist_eq] using hx
  filter_upwards [ae_all_iff.mpr hdist] with x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have H : Tendsto (fun n => |cs n-c| * weakGradient m f x) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_mul] using ((hc.sub (tendsto_const_nhds (x := c))).abs.mul_const (weakGradient m f x))
  exact squeeze_zero (fun n => dist_nonneg) hx H

lemma gamma_const_mul_tendsto (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {cs : ℕ → ℝ} {c : ℝ} (hc : Tendsto cs atTop (𝓝 c)) :
    ∀ᵐ x ∂m, Tendsto (fun n => gamma m (fun y => cs n*f y) g x) atTop
      (𝓝 (gamma m (fun y => c*f y) g x)) := by
  filter_upwards [weakGradient_const_mul_add_tendsto hfinite hf hg hc,
    weakGradient_const_mul_add_tendsto hfinite hf hg.neg hc] with x hp hm
  simpa only [gamma, ← sub_eq_add_neg] using ((hp.pow 2).sub (hm.pow 2)).div_const 4
end WeakHessian

end
end InlinedFile0

end OAI
