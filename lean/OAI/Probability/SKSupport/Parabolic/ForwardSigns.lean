import Mathlib
import OAI.Probability.SKSupport.Diffusion.AffineComparison

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat
namespace SmoothForward
variable {s : ℝ → ℝ → ℝ} (hs : SmoothForward s)
include hs

theorem deriv_ge_inverse {a : ℝ} (ha : 0 < a)
    (hi : ∀ x, a⁻¹ ≤ deriv (s 0) x) :
    ∀ t, 0 ≤ t → ∀ x, (forwardTime a t)⁻¹ ≤ deriv (s t) x := by
  let F (t x : ℝ) := deriv (s t) x-(forwardTime a t)⁻¹
  let Ft (t x : ℝ) := deriv (scoreRate s t) x+((forwardTime a t)⁻¹)^2
  have hF : BoundedSmoothFamily F := by
    convert hs.deriv_family.add ((inverse_forwardTime_family ha).const_mul (-1)) using 1
    funext t x
    simp only [F,neg_one_mul,sub_eq_add_neg]
  have hFc : Continuous (fun p : ℝ × ℝ => F p.1 p.2) :=
    hs.family.deriv.continuous.sub ((inverse_forwardTime_continuous ha).comp continuous_fst)
  have hFt (t : ℝ) (ht : 0 < t) (x : ℝ) : HasDerivAt (fun u => F u x) (Ft t x) t := by
    have hb := (hasDerivAt_forwardTime (a := a) ht).inv (ne_of_gt (forwardTime_pos ha t))
    convert (hs.time_derivative 1 t ht x).sub hb using 1 <;>
     first | rfl | ((try funext u); simp only [F,Ft,iteratedDeriv_one,Pi.sub_apply,Pi.inv_apply] <;> ring)
  have hFx (t x : ℝ) : deriv (F t) x=iteratedDeriv 2 (s t) x := by
    simpa only [F,iteratedDeriv_one] using ((hs.jet_spatial 1 t x).sub_const ((forwardTime a t)⁻¹)).deriv
  have hFxx (t x : ℝ) : iteratedDeriv 2 (F t) x=iteratedDeriv 3 (s t) x := by
    rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,show deriv (F t)=iteratedDeriv 2 (s t) from funext (hFx t)]
    exact (hs.jet_spatial 2 t x).deriv
  have hβ : AffineSmoothFamily (fun t x => -s t x) := by
    simpa only [neg_one_mul] using hs.family.const_mul (-1)
  obtain ⟨V,hV⟩ := hs.deriv_family.bound
  have hh := affineDrift_nonnegative_full hF hβ hFc hFt
    (c := fun t x => -(deriv (s t) x+(forwardTime a t)⁻¹)) (C := (V:ℝ))
    (fun t ht x => ?_) (fun t ht x => ?_) (fun x => ?_)
  · intro t ht x
    exact sub_nonneg.mp (hh t ht x)
  · have hb := inv_pos.mpr (forwardTime_pos ha t)
    have hv := (neg_abs_le (deriv (s t) x)).trans' (neg_le_neg (hV t x))
    linarith
  · rw [hFx,hFxx]
    dsimp only [Ft,F]
    rw [hs.rate_deriv]
    ring
  · simpa only [F,forwardTime,max_self,add_zero] using sub_nonneg.mpr (hi x)

theorem second_nonpos (ho : ∀ t, Function.Odd (s t))
    (hi : ∀ x, 0 ≤ x → iteratedDeriv 2 (s 0) x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (s t) x ≤ 0 := by
  let F (t x : ℝ) := -iteratedDeriv 2 (s t) x
  have hF : BoundedSmoothFamily F := by
    simpa only [neg_one_mul] using (hs.jet_family 1).const_mul (-1)
  have hFc : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := (hs.jet_continuous 2).neg
  have hFx (t x : ℝ) : deriv (F t) x= -iteratedDeriv 3 (s t) x :=
    ((hs.jet_spatial 2 t x).neg).deriv
  have hFxx (t x : ℝ) : iteratedDeriv 2 (F t) x= -iteratedDeriv 4 (s t) x := by
    rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,show deriv (F t)=(fun x => -iteratedDeriv 3 (s t) x) from funext (hFx t)]
    exact ((hs.jet_spatial 3 t x).neg).deriv
  have hβ : AffineSmoothFamily (fun t x => -s t x) := by
    simpa only [neg_one_mul] using hs.family.const_mul (-1)
  obtain ⟨V,hV⟩ := hs.deriv_family.bound
  have hh := affineDrift_nonnegative_half hF hβ hFc
    (fun t ht x => (hs.time_derivative 2 t ht x).neg)
    (c := fun t x => -3*deriv (s t) x) (C := 3*(V:ℝ))
    (fun t ht x hx => ?_) (fun t ht x hx => ?_) (fun t ht => ?_) (fun x hx => neg_nonneg.mpr (hi x hx))
  · intro t ht x hx
    exact neg_nonneg.mp (hh t ht x hx)
  · have hv := (neg_abs_le (deriv (s t) x)).trans' (neg_le_neg (hV t x))
    linarith
  · rw [hFx,hFxx,hs.rate_jet2]
    dsimp only [F]
    ring
  · have hz := hs.second_odd ho t 0
    simp only [neg_zero] at hz
    dsimp [F]
    linarith

end SmoothForward
end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure ForwardDatumShape (f : ℝ → ℝ) : Prop where
  even : Function.Even f
  second : ∀ x, iteratedDeriv 2 f x ≤ 0
  third : ∀ x, 0 ≤ x → 0 ≤ iteratedDeriv 3 f x

lemma forwardCorrection_shape {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hshape : ForwardDatumShape f)
    {t : ℝ} (ht : 0 ≤ t) : ForwardDatumShape (forwardCorrection a f t) := by
  have hi (x : ℝ) : a⁻¹ ≤ deriv (forwardScore a f 0) x := by
    rw [forwardScore_deriv hf hLip,forwardCorrection_terminal a (ne_of_gt ha),forwardTime]
    simp only [max_self,add_zero]
    linarith [hshape.second x]
  have hge := (forwardScore_smooth ha hf hLip).deriv_ge_inverse ha hi t ht
  have h₂ : ∀ x, iteratedDeriv 2 (forwardCorrection a f t) x ≤ 0 := by
    intro x
    have hh := hge x
    rw [forwardScore_deriv hf hLip] at hh
    linarith
  have hi₂ (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 2 (forwardScore a f 0) x ≤ 0 := by
    rw [forwardScore_second hf hLip,forwardCorrection_terminal a (ne_of_gt ha)]
    exact neg_nonpos.mpr (hshape.third x hx)
  have hle := (forwardScore_smooth ha hf hLip).second_nonpos (forwardScore_odd hf hLip hshape.even) hi₂ t ht
  refine ⟨forwardCorrection_even hf hLip hshape.even t,h₂,fun x hx => ?_⟩
  have hh := hle x hx
  rw [forwardScore_second hf hLip] at hh
  exact neg_nonpos.mp hh

lemma ForwardDatumShape.const (c : ℝ) : ForwardDatumShape (fun _ : ℝ => c) := by
  refine ⟨fun _ => rfl,fun x => ?_,fun x hx => ?_⟩ <;> simp [iteratedDeriv_const]

lemma ForwardDatumShape.jump {f φ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hshape : ForwardDatumShape f) (heφ : Function.Even φ)
    (hv : ∀ x, 0 ≤ iteratedDeriv 2 φ x) (hw : ∀ x, 0 ≤ x → iteratedDeriv 3 φ x ≤ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) : ForwardDatumShape (fun x => f x-δ*φ x) := by
  have hj (n : ℕ) (x : ℝ) : iteratedDeriv n (fun x => f x-δ*φ x) x =
      iteratedDeriv n f x-δ*iteratedDeriv n φ x := by
    rw [iteratedDeriv_fun_sub (n := n)
      (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      ((contDiff_const.mul hφ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt),
      iteratedDeriv_const_mul_field]
  refine ⟨?_,?_,?_⟩
  · intro x
    change f (-x) - δ * φ (-x) = f x - δ * φ x
    rw [hshape.even x,heφ x]
  · intro x
    rw [hj]
    linarith [hshape.second x,mul_nonneg hδ (hv x)]
  · intro x hx
    rw [hj]
    linarith [hshape.third x hx,mul_nonpos_of_nonneg_of_nonpos hδ (hw x hx)]

end ZeroTemperatureSK.Heat

end
end

end OAI
