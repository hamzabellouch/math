import OAI.Analysis.AncientFlat.Evolution.SourceStep

namespace OAI
noncomputable section
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (T : ℝ → E →L[ℂ] E)
  (hc : ∀ v : E, ContinuousOn (fun t => T t v) (Ici (0:ℝ)))
  (ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s+t)=(T s).comp (T t))
include hc in
lemma integrand_integrable_le (f : ℝ →ᵇ E) (H τ a b : ℝ) (hab : a≤b) (hbH : b≤H) :
    IntervalIntegrable (fun s => T (H-s) (f (τ+s))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply (continuousOn_action T hc).comp
    ((continuous_const.sub continuous_id).prodMk (f.continuous.comp (continuous_const.add continuous_id))).continuousOn
  intro s hs
  exact ⟨show 0≤H-s from sub_nonneg.mpr (hs.2.trans hbH),mem_univ _⟩
include hc ha in
lemma duhamel_cocycle (f : ℝ →ᵇ E) {h k : ℝ} (hh : 0≤h) (hk : 0≤k) (τ : ℝ) :
    duhamel T f (h+k) τ=T k (duhamel T f h τ)+duhamel T f k (τ+h) := by
  have hib := integrand_integrable_le T hc f (h+k) τ 0 h hh (by linarith)
  have hic := integrand_integrable_le T hc f (h+k) τ h (h+k) (by linarith) le_rfl
  have hfirst : (∫ s in (0:ℝ)..h, T (h+k-s) (f (τ+s)))=T k (duhamel T f h τ) := by
    rw [duhamel,←(T k).intervalIntegral_comp_comm (integrand_integrable T hc f hh τ)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hh] at hs
    have he : h+k-s=k+(h-s) := by ring
    dsimp only
    rw [he,ha k (h-s) hk (sub_nonneg.mpr hs.2),ContinuousLinearMap.comp_apply]
  have hsecond : (∫ s in h..(h+k), T (h+k-s) (f (τ+s)))=duhamel T f k (τ+h) := by
    have he := intervalIntegral.integral_comp_add_left
      (fun s => T (h+k-s) (f (τ+s))) (a := (0:ℝ)) (b := k) h
    rw [add_zero] at he
    rw [←he,duhamel]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    congr 2 <;> ring
  rw [duhamel,←intervalIntegral.integral_add_adjacent_intervals hib hic,hfirst,hsecond]
include hc ha in
lemma duhamel_commutator (f : ℝ →ᵇ E) {h : ℝ} (hh : 0≤h) (τ : ℝ) :
    duhamel T f 1 (τ+h)-T h (duhamel T f 1 τ)=
      duhamel T f h (τ+1)-T 1 (duhamel T f h τ) := by
  have h1 := duhamel_cocycle T hc ha f hh zero_le_one τ
  have h2 := duhamel_cocycle T hc ha f zero_le_one hh τ
  rw [add_comm h 1] at h1
  rw [h1] at h2
  apply sub_eq_iff_eq_add.mpr
  calc
    duhamel T f 1 (τ+h)=(T 1 (duhamel T f h τ)+duhamel T f 1 (τ+h))-T 1 (duhamel T f h τ) := by abel
    _=(T h (duhamel T f 1 τ)+duhamel T f h (τ+1))-T 1 (duhamel T f h τ) := by rw [h2]
    _=_ := by abel
end AncientMild

end

end OAI
