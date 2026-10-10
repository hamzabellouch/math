import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTowerBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma outerBarrier_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (B : ℝ) (x : TFSpace) :
    Tendsto (fun i => outerBarrier B (a i) x) l (𝓝 (B/‖x‖^4)) := by
  have ht := (((tendsto_const_nhds (x := (1:ℝ))).sub (ha.div_const (8*‖x‖))).const_mul (B/‖x‖^4))
  simpa only [outerBarrier,zero_div,sub_zero,mul_one] using ht

theorem positive_limit_of_eventual_barrier_transfer {ι : Type*} {l : Filter ι} [NeBot l]
    {U F : ι → TFSpace → ℝ} {L : ℝ → ι → TFSpace → ℝ}
    {a : ι → ℝ} {B C : ℝ} {F_lim : TFSpace → ℝ} (hC : 0 ≤ C)
    (ha : Tendsto a l (𝓝 0))
    (hlo : ∀ i x, a i ≤ ‖x‖ → outerBarrier B (a i) x ≤ U i x)
    (hup : ∀ i x, a i ≤ ‖x‖ → U i x ≤ C/‖x‖^4)
    (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn F F_lim l (sphere (0:TFSpace) S))
    (hL : ∀ S : ℝ, 0 < S → ∀ x : TFSpace, x ≠ 0 →
      Tendsto (fun i => L S i x) l (𝓝 0))
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε)
    (htransfer : ∀ (S : ℝ), 0 < S → ∀ᶠ i in l, ∀ c : ℝ, 0 ≤ c →
      (∀ x : TFSpace, ‖x‖ = S → U i x-F i x ≤ c) →
      ∀ x ∈ closedBall (0:TFSpace) S, U i x ≤ F i x+L S i x+c) :
    ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x := by
  intro x hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,hdec⟩ := hdecay (ε/4) (by positivity)
  let S : ℝ := max R (max (‖x‖+1) (max 1 (4*C/ε)))
  have hRS : R ≤ S := le_max_left _ _
  have hxS : ‖x‖+1 ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have h1S : 1 ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCS : 4*C/ε ≤ S := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hS : 0 < S := hR.trans_le hRS
  have hpow : S ≤ S^4 := by
    have hh : 1 ≤ S^3 := one_le_pow₀ h1S
    nlinarith
  have hsmallC : C/S^4 ≤ ε/4 := calc
    _ ≤ C/S := div_le_div_of_nonneg_left hC hS hpow
    _ ≤ _ := (div_le_iff₀ hS).mpr (by
      have hh := (div_le_iff₀ hε).mp hCS
      nlinarith)
  have ha' : ∀ᶠ i in l, a i < ‖x‖ := ha.eventually (Iio_mem_nhds hxpos)
  have he := Metric.tendstoUniformlyOn_iff.mp (hconv S hS) (ε/4) (by positivity)
  have hb : ∀ᶠ i in l, ∀ y : TFSpace, ‖y‖ = S → U i y-F i y ≤ ε := by
    filter_upwards [ha',he] with i hai hei
    intro y hy
    have hUi := hup i y (by rw [hy]; linarith)
    have hFi := hei y (by simpa only [mem_sphere,dist_zero_right] using hy)
    rw [Real.dist_eq] at hFi
    have hyR : R ≤ ‖y‖ := hy ▸ hRS
    have hFy := hdec y hyR
    rw [hy] at hUi
    have hab1 := (abs_lt.mp hFi).2
    have hab2 := (abs_lt.mp hFy).1
    linarith
  have hFi : Tendsto (fun i => F i x) l (𝓝 (F_lim x)) :=
    (hconv ‖x‖ hxpos).tendsto_at (by simp only [mem_sphere,dist_zero_right])
  have hright := (hFi.add (hL S hS x hx)).add_const ε
  simp only [add_zero] at hright
  apply le_of_tendsto_of_tendsto (outerBarrier_tendsto ha B x) hright
  filter_upwards [ha',hb,htransfer S hS] with i hai hbi hti
  exact (hlo i x hai.le).trans (hti ε hε.le hbi x
    (mem_closedBall_zero_iff.mpr (by linarith)))

theorem positive_limit_of_barrier_transfer {ι : Type*} {l : Filter ι} [NeBot l]
    {U F : ι → TFSpace → ℝ} {L : ℝ → ι → TFSpace → ℝ}
    {a : ι → ℝ} {B C : ℝ} {F_lim : TFSpace → ℝ} (hC : 0 ≤ C)
    (ha : Tendsto a l (𝓝 0))
    (hlo : ∀ i x, a i ≤ ‖x‖ → outerBarrier B (a i) x ≤ U i x)
    (hup : ∀ i x, a i ≤ ‖x‖ → U i x ≤ C/‖x‖^4)
    (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn F F_lim l (sphere (0:TFSpace) S))
    (hL : ∀ S : ℝ, 0 < S → ∀ x : TFSpace, x ≠ 0 →
      Tendsto (fun i => L S i x) l (𝓝 0))
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε)
    (htransfer : ∀ (i : ι) (S c : ℝ), 0 < S → 0 ≤ c →
      (∀ x : TFSpace, ‖x‖ = S → U i x-F i x ≤ c) →
      ∀ x ∈ closedBall (0:TFSpace) S, U i x ≤ F i x+L S i x+c) :
    ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x :=
  positive_limit_of_eventual_barrier_transfer hC ha hlo hup hconv hL hdecay
    (fun S hS => Eventually.of_forall fun i c hc hb => htransfer i S c hS hc hb)

end CoulombBarrier

end

end OAI
