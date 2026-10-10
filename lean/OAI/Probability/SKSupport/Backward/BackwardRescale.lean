import Mathlib
import OAI.Probability.SKSupport.Backward.BackwardComparison

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure BackwardShape (r : ℝ → ℝ) : Prop where
  odd : Function.Odd r
  derivative_pos : ∀ x, 0 < deriv r x
  second_nonpos : ∀ x, 0 ≤ x → iteratedDeriv 2 r x ≤ 0
  rate_nonpos : ∀ x, 0 ≤ x → burgersRate (fun _ => r) 0 x ≤ 0
  wronskian_nonneg : ∀ x, 0 ≤ x → 0 ≤ backwardWronskian (fun _ => r) 0 x

lemma scaled_jet {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (α : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => α*r y) x = α*iteratedDeriv n r x :=
  iteratedDeriv_const_mul α (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)

lemma scaled_rate {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (α x : ℝ) :
    burgersRate (fun _ y => α*r y) 0 x =
      α*burgersRate (fun _ => r) 0 x+α*(α-1)*r x*deriv r x := by
  have he := scaled_jet hr α 1 x
  simp only [iteratedDeriv_one] at he
  simp only [burgersRate,scaled_jet hr α 2 x,he]
  ring

lemma scaled_wronskian {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (α x : ℝ) :
    backwardWronskian (fun _ y => α*r y) 0 x =
      α^2*backwardWronskian (fun _ => r) 0 x+
        α^2*(α-1)*(r x)^2*iteratedDeriv 2 r x := by
  have hr' := contDiff_iteratedDeriv_infty hr 1
  have hr'' := contDiff_iteratedDeriv_infty hr 2
  have hp : ContDiff ℝ ∞ (burgersRate (fun _ => r) 0) := by
    exact (contDiff_const.mul hr'').add (hr.mul (by simpa only [iteratedDeriv_one] using hr'))
  have he : burgersRate (fun _ y => α*r y) 0 = fun y =>
      α*burgersRate (fun _ => r) 0 y+α*(α-1)*r y*deriv r y := funext (scaled_rate hr α)
  have hd := ((hp.differentiable (by simp) x).hasDerivAt.const_mul α).add
    (((hasDerivAt_spatialJet hr 0 x).const_mul (α*(α-1))).mul (hasDerivAt_spatialJet hr 1 x))
  have hd' : HasDerivAt (burgersRate (fun _ y => α*r y) 0)
      (α*deriv (burgersRate (fun _ => r) 0) x+
        α*(α-1)*((deriv r x)^2+r x*iteratedDeriv 2 r x)) x := by
    rw [he]
    convert hd using 1 <;> first | rfl | ((try funext y); simp only
      [Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  have he' := scaled_jet hr α 1 x
  simp only [iteratedDeriv_one] at he'
  rw [backwardWronskian,hd'.deriv,he',scaled_rate hr α x]
  simp only [backwardWronskian]
  ring

theorem BackwardShape.rescale {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : BackwardShape r)
    {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1) : BackwardShape (fun x => α*r x) := by
  have hv : ∀ x, deriv (fun y => α*r y) x=α*deriv r x := fun x => by
    simpa only [iteratedDeriv_one] using scaled_jet hr α 1 x
  have hzero : r 0=0 := by
    have hh := hs.odd 0
    simp only [neg_zero] at hh
    linarith
  have hpos (x : ℝ) (hx : 0 ≤ x) : 0 ≤ r x := by
    have hm := (strictMono_of_deriv_pos hs.derivative_pos).monotone hx
    simpa only [hzero] using hm
  refine ⟨?_,fun x => by rw [hv]; exact mul_pos hα (hs.derivative_pos x),?_,?_,?_⟩
  · intro x
    change α*r (-x) = -(α*r x)
    rw [hs.odd x]
    ring
  · intro x hx
    rw [scaled_jet hr α]
    exact mul_nonpos_of_nonneg_of_nonpos hα.le (hs.second_nonpos x hx)
  · intro x hx
    rw [scaled_rate hr α]
    apply add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα.le (hs.rate_nonpos x hx))
    apply mul_nonpos_of_nonpos_of_nonneg _ (hs.derivative_pos x).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hα.le (sub_nonpos.mpr hα')) (hpos x hx)
  · intro x hx
    rw [scaled_wronskian hr α]
    apply add_nonneg (mul_nonneg (sq_nonneg α) (hs.wronskian_nonneg x hx))
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg α) (sub_nonpos.mpr hα')) (sq_nonneg (r x)))
      (hs.second_nonpos x hx)

end ZeroTemperatureSK.Heat

end
end

end OAI
