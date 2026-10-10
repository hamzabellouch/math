import Mathlib
import OAI.Probability.SKSupport.Density.RatioJets

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure ReverseBurgers (r : ℝ → ℝ → ℝ) (H : ℝ) : Prop where
  family : BoundedSmoothFamily r
  continuous : ContinuousOn (fun p : ℝ × ℝ => r p.1 p.2) (Icc (0:ℝ) H ×ˢ univ)
  time_derivative : ∀ n t, 0 < t → t < H → ∀ x,
    HasDerivAt (fun u => iteratedDeriv n (r u) x) (-iteratedDeriv n (burgersRate r t) x) t

lemma SmoothBurgers.reverse {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r) {H : ℝ} (_ : 0 ≤ H) :
    ReverseBurgers (fun t x => r (H-t) x) H := by
  have hfm : BoundedSmoothFamily (fun t x => r (H-t) x) := by
    simpa only [one_mul] using hr.family.reparam (A := fun t => H-t) (C := fun _ => 1)
      (measurable_const.sub measurable_id) measurable_const (fun _ => by norm_num)
  refine ⟨hfm,?_,?_⟩
  · apply (hr.continuous H).comp
      (f := fun p : ℝ × ℝ => (H-p.1,p.2))
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    intro p hp
    exact ⟨⟨sub_nonneg.mpr hp.1.2,sub_le_self _ hp.1.1⟩,mem_univ _⟩
  · intro n t ht htH x
    have hd := (hr.time_derivative n (H-t) (sub_pos.mpr htH) x).comp t
      ((hasDerivAt_id t).const_sub H)
    convert hd using 1 <;> first | rfl | (simp only [mul_neg,mul_one];rfl)

namespace ReverseBurgers
variable {r : ℝ → ℝ → ℝ} {H : ℝ} (hr : ReverseBurgers r H)
include hr

lemma jet_continuous (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (r p.1) p.2) (Icc (0:ℝ) H ×ˢ univ) :=
  hr.family.continuousOn_iteratedDeriv hr.continuous n

lemma ratio_continuous {s : ℝ → ℝ → ℝ} (hs : SmoothForward s) :
    ContinuousOn (fun p : ℝ × ℝ => ratioWronskian r s p.1 p.2) (Icc (0:ℝ) H ×ˢ univ) := by
  have hv : ContinuousOn (fun p : ℝ × ℝ => deriv (r p.1) p.2) (Icc (0:ℝ) H ×ˢ univ) := by
    simpa only [iteratedDeriv_one] using hr.jet_continuous 1
  exact (hr.continuous.mul hs.family.deriv.continuous.continuousOn).sub
    (hs.family.continuous.continuousOn.mul hv)

lemma ratio_time {s : ℝ → ℝ → ℝ} (hs : SmoothForward s) {t : ℝ} (ht : 0 < t) (htH : t < H) (x : ℝ) :
    HasDerivAt (fun u => ratioWronskian r s u x) (ratioWronskianRate r s t x) t := by
  apply ratioWronskian_time hs ht x
  · simpa only [iteratedDeriv_zero] using hr.time_derivative 0 t ht htH x
  · simpa only [iteratedDeriv_one] using hr.time_derivative 1 t ht htH x

end ReverseBurgers
end ZeroTemperatureSK.Heat

end
end

end OAI
