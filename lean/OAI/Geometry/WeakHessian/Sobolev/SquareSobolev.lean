import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile17
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma Sobolev.square_bounded (hfin : FiniteOnBoundedSets m) {u : X → ℝ}
    (hu : Sobolev m u) {B : ℝ} (hB : ∀ᵐ x ∂m, |u x| ≤ B) :
    Sobolev m (fun x => u x^2) := by
  have hsq : MemLp (fun x => u x^2) 2 m := by
    simpa only [pow_two] using memLp_mul_bounded hu.1 hu.1.aestronglyMeasurable hB
  have hc : ContDiff ℝ 1 (fun s : ℝ => s^2) := contDiff_id.pow 2
  have hd (s : ℝ) : deriv (fun t : ℝ => t^2) s = 2*s := by
    simp
  have hb : ∀ᵐ x ∂m, |deriv (fun s : ℝ => s^2) (u x)| ≤ 2*B := by
    filter_upwards [hB] with x hx
    rw [hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  apply Sobolev.of_upperGradient hfin hsq
    ((weakGradient_isMinimal hu.2.1.2).1.comp_contDiff hu.1.aemeasurable hc hb)
  have hm : AEStronglyMeasurable (fun x => |deriv (fun s : ℝ => s^2) (u x)|) m := by
    simp only [hd]
    exact continuous_abs.comp_aestronglyMeasurable (hu.1.aestronglyMeasurable.const_mul 2)
  simpa only [mul_comm] using memLp_mul_bounded hu.2.2 hm (by simpa only [abs_abs] using hb)

lemma gamma_square_bounded (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v : X → ℝ}
    (hu : Sobolev m u) (hv : LocalSobolev m v) {B : ℝ} (hB : ∀ᵐ x ∂m, |u x| ≤ B) :
    gamma m (fun x => u x^2) v =ᵐ[m] (fun x => 2*u x*gamma m u v x) := by
  have hd (s : ℝ) : deriv (fun t : ℝ => t^2) s = 2*s := by
    simp
  have hb : ∀ᵐ x ∂m, |deriv (fun s : ℝ => s^2) (u x)| ≤ 2*B := by
    filter_upwards [hB] with x hx
    rw [hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  simpa only [Function.comp_def,id_eq,hd] using gamma_comp_contDiff hfin hpar hu.2.1 hv
    (contDiff_id.pow 2) (hu.square_bounded hfin hB).2.1.1 hb

lemma gamma_locality_left (hfin : FiniteOnBoundedSets m) {f g v : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ᵐ x ∂m, x ∈ Q → f x = g x) :
    ∀ᵐ x ∂m, x ∈ Q → gamma m f v x = gamma m g v x := by
  have hp := weakGradient_locality (hf.add hfin hv) (hg.add hfin hv) hQ
    (he.mono fun x hx hxQ => by rw [hx hxQ])
  have hn := weakGradient_locality (hf.sub hfin hv) (hg.sub hfin hv) hQ
    (he.mono fun x hx hxQ => by rw [hx hxQ])
  filter_upwards [hp,hn] with x hx hy h
  simp only [gamma,hx h,hy h]

lemma gamma_zero_off_set (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f v : X → ℝ}
    (hf : LocalSobolev m f) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ᵐ x ∂m, x ∉ Q → f x = 0) :
    ∀ᵐ x ∂m, x ∉ Q → gamma m f v x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [gamma_locality_left hfin hf hz hv hQ.compl he,
    abs_gamma_le hfin hpar hz hv,weakGradient_const (m := m) 0] with x hx hy hz h
  rw [hx h]
  apply abs_nonpos_iff.mp
  simpa only [hz,zero_mul] using hy
end WeakHessian

end
end InlinedFile17

end OAI
