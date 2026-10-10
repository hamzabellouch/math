import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMap

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile84
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

lemma slopeApprox_quotient_le {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (n : ℕ) {x y : X} (hy : dist x y < 1/(n+1:ℝ)) :
    |f x-f y| ≤ (slopeApprox f n x).toReal*dist x y := by
  have hfin : slopeApprox f n x ≠ ∞ := ne_of_lt ((slopeApprox_le_lipschitz hf n x).trans_lt ENNReal.coe_lt_top)
  have H : ENNReal.ofReal (|f y-f x|/dist y x) ≤ slopeApprox f n x :=
    le_iSup_of_le y (le_iSup_of_le (by simpa only [dist_comm] using hy) le_rfl)
  have H' := ENNReal.toReal_mono hfin H
  rw [ENNReal.toReal_ofReal (by positivity)] at H'
  by_cases hxy : x = y
  · simp [hxy]
  · have hp : 0 < dist y x := dist_pos.mpr (Ne.symm hxy)
    simpa only [abs_sub_comm,dist_comm] using (div_le_iff₀ hp).mp H'

lemma hopf_initial_slopeApprox_bound [ProperSpace X] (f : X →ᵇ ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : X) {s : ℝ} (hs : 0 < s)
    (hsmall : 2*s*(L:ℝ) < 1/(n+1:ℝ)) :
    (f x-hopfLax f s x)/s ≤ (slopeApprox f n x).toReal^2/2 := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (fun z => (boundedContinuous_bounds f z).1) hs x
  have hd := hopf_minimizer_distance_lipschitz hf (fun z => (boundedContinuous_bounds f z).1) hs hy
  have hb := (abs_le.mp (slopeApprox_quotient_le hf n (hd.trans_lt hsmall))).2
  rw [← hy]
  dsimp only [hopfObjective]
  apply (div_le_iff₀ hs).mpr
  have hq : (slopeApprox f n x).toReal*dist x y-s*(slopeApprox f n x).toReal^2/2 ≤ dist x y^2/(2*s) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*s)).mpr
    nlinarith [sq_nonneg (dist x y-s*(slopeApprox f n x).toReal)]
  linarith

lemma hopf_initial_quotient_nonneg (f : X →ᵇ ℝ) {s : ℝ} (hs : 0 < s) (x : X) :
    0 ≤ (f x-hopfLax f s x)/s :=
  div_nonneg (sub_nonneg.mpr (hopfLax_le_self (fun z => (boundedContinuous_bounds f z).1) hs x)) hs.le

lemma hopf_initial_quotient_le (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {s : ℝ} (hs : 0 < s) (x : X) : (f x-hopfLax f s x)/s ≤ (L:ℝ)^2/2 := by
  apply (div_le_iff₀ hs).mpr
  linarith [hopfLax_ge_lipschitz hf hs x]

lemma tendsto_slopeApprox_toReal {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : X) :
    Tendsto (fun n : ℕ => (slopeApprox f n x).toReal) atTop (𝓝 (localSlope f x).toReal) := by
  have hlfin : localSlope f x ≠ ∞ :=
    ne_of_lt ((localSlope_le_lipschitz hf x).trans_lt ENNReal.coe_lt_top)
  have hmono : Antitone (fun n : ℕ => slopeApprox f n x) := by
    intro n k hnk
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    have hrad : 1/(k+1:ℝ) ≤ 1/(n+1:ℝ) := by gcongr
    exact le_iSup_of_le y (le_iSup_of_le (hy.trans_le hrad) le_rfl)
  apply (ENNReal.tendsto_toReal hlfin).comp
  rw [localSlope_eq_iInf_slopeApprox]
  exact tendsto_atTop_ciInf hmono ⟨0,fun _ _ => bot_le⟩

lemma hopf_initial_eventually_lt [ProperSpace X] (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (x : X) {a : ℝ} (ha : (localSlope f x).toReal^2/2 < a) :
    ∀ᶠ s in 𝓝[>] (0:ℝ),(f x-hopfLax f s x)/s < a := by
  have hlim := tendsto_slopeApprox_toReal hf x
  have he := ((hlim.pow 2).div_const 2).eventually_lt_const ha
  obtain ⟨n,hn⟩ := he.exists
  have hid : Tendsto (fun s : ℝ => 2*s*(L:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (ht.const_mul 2).mul_const (L:ℝ)
  filter_upwards [hid.eventually_lt_const (by positivity : (0:ℝ) < 1/(n+1:ℝ)),self_mem_nhdsWithin] with s hs hs0
  exact (hopf_initial_slopeApprox_bound f hf n x hs0 hs).trans_lt hn
end WeakHessianTransport

end
end InlinedFile84

end OAI
