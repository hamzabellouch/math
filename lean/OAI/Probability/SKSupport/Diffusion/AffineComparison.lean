import Mathlib
import OAI.Probability.SKSupport.Parabolic.FullLineComparison

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma AffineSmoothFamily.drift_bound {β : ℝ → ℝ → ℝ} (hβ : AffineSmoothFamily β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t x, β t x*x ≤ K*(1+x^2) := by
  obtain ⟨C,hC,hb⟩ := hβ.bound
  refine ⟨2*C,by positivity,fun t x => ?_⟩
  have hh : β t x*x ≤ C*(1+|x|)*|x| := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb t x) (abs_nonneg x)
  have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have hmul := mul_le_mul_of_nonneg_left hx hC
  have he : |x| * |x| = x*x := by nlinarith [sq_abs x]
  nlinarith [mul_nonneg hC (sq_nonneg x)]

lemma affineDrift_nonnegative_full {F β Ft c : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : BoundedSmoothFamily F) (hβ : AffineSmoothFamily β)
    (hcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (htime : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (hc : ∀ t, 0 < t → ∀ x, c t x ≤ C)
    (hpde : ∀ t, 0 < t → ∀ x,
      Ft t x=(1/2:ℝ)*iteratedDeriv 2 (F t) x+β t x*deriv (F t) x+c t x*F t x)
    (hinit : ∀ x, 0 ≤ F 0 x) : ∀ t, 0 ≤ t → ∀ x, 0 ≤ F t x := by
  obtain ⟨K,hK,hβb⟩ := hβ.drift_bound
  obtain ⟨M,hM⟩ := hF.bound
  intro T hT x
  apply Parabolic.nonnegative_fullLine_bounded (u := F) (ut := Ft)
    (ux := fun t => deriv (F t)) (uxx := fun t => iteratedDeriv 2 (F t))
    (β := β) (c := c) (C := C) (K := K) (M := (M:ℝ)) hK M.coe_nonneg
    hcont.continuousOn (fun t _ => (hF.regular t).smooth.continuous)
    (fun t ht x => (htime t ht.1 x).hasDerivWithinAt)
    (fun t _ x => ((hF.regular t).smooth.differentiable (by simp) x).hasDerivAt)
    (fun t _ x => by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet (hF.regular t).smooth 1 x)
    (fun t _ x => hβb t x) (fun t ht x => hc t ht.1 x)
    (fun t ht x => by rw [hpde t ht.1 x];ring_nf;exact le_rfl)
    (fun t _ x => (neg_le_neg (hM t x)).trans (neg_abs_le _)) hinit T ⟨hT,le_rfl⟩ x

lemma affineDrift_nonnegative_half {F β Ft c : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : BoundedSmoothFamily F) (hβ : AffineSmoothFamily β)
    (hcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (htime : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (hc : ∀ t, 0 < t → ∀ x, 0 < x → c t x ≤ C)
    (hpde : ∀ t, 0 < t → ∀ x, 0 < x →
      Ft t x=(1/2:ℝ)*iteratedDeriv 2 (F t) x+β t x*deriv (F t) x+c t x*F t x)
    (hzero : ∀ t, 0 ≤ t → 0 ≤ F t 0)
    (hinit : ∀ x, 0 ≤ x → 0 ≤ F 0 x) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → 0 ≤ F t x := by
  obtain ⟨K,hK,hβb⟩ := hβ.drift_bound
  obtain ⟨M,hM⟩ := hF.bound
  intro T hT x hx
  apply Parabolic.nonnegative_halfLine_bounded (u := F) (ut := Ft)
    (ux := fun t => deriv (F t)) (uxx := fun t => iteratedDeriv 2 (F t))
    (β := β) (c := c) (C := C) (K := K) (M := (M:ℝ)) hK M.coe_nonneg
    hcont.continuousOn (fun t _ => (hF.regular t).smooth.continuous)
    (fun t ht x _ => (htime t ht.1 x).hasDerivWithinAt)
    (fun t _ x _ => ((hF.regular t).smooth.differentiable (by simp) x).hasDerivAt)
    (fun t _ x _ => by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet (hF.regular t).smooth 1 x)
    (fun t _ x _ => hβb t x) (fun t ht x hx => hc t ht.1 x hx)
    (fun t ht x hx => by rw [hpde t ht.1 x hx];ring_nf;exact le_rfl)
    (fun t _ x _ => (neg_le_neg (hM t x)).trans (neg_abs_le _)) hinit
    (fun t ht => hzero t ht.1) T ⟨hT,le_rfl⟩ x hx

end ZeroTemperatureSK.Heat

end
end

end OAI
