import OAI.Analysis.CircleDomains.Sobolev.DerivativeLipschitzPartition
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Antilipschitz

namespace OAI

/-! A strict derivative gives lower distance bounds on a small interval.
These bounds will supply the reverse arclength inequality. -/
open Set Function Filter Topology
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma real_clm_eq_toSpanSingleton (d : ℝ →L[ℝ] ℂ) :
    d = ContinuousLinearMap.toSpanSingleton ℝ (d 1) := by
  apply ContinuousLinearMap.ext
  intro t
  change d t = t • d 1
  simpa using d.map_smul t (1 : ℝ)

lemma norm_real_clm_apply (d : ℝ →L[ℝ] ℂ) (t : ℝ) :
    ‖d t‖ = ‖d‖ * |t| := by
  have hn := congrArg norm (real_clm_eq_toSpanSingleton d)
  rw [ContinuousLinearMap.norm_toSpanSingleton] at hn
  have ht : d t = t • d 1 := by simpa using d.map_smul t (1 : ℝ)
  rw [ht, norm_smul, Real.norm_eq_abs, ← hn, mul_comm]

lemma local_curve_lower_distance
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {x : ℝ} (hx : x ∈ D) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      (∀ y ∈ U, ‖d y‖ ≤ ‖d x‖ + δ) ∧
      ∀ a ∈ U, ∀ b ∈ U, (‖d x‖ - δ) * dist a b ≤ dist (γ a) (γ b) := by
  have hR := (hd x hx).sub (d x).hasStrictFDerivAt
  let K : ℝ≥0 := ⟨δ, hδ.le⟩
  obtain ⟨V, hV, hLip⟩ := hR.exists_lipschitzOnWith_of_nnnorm_lt K (by simpa [K])
  have hn : {y : ℝ | ‖d y‖ < ‖d x‖ + δ} ∈ 𝓝 x :=
    (hc.continuousAt (hD.mem_nhds hx)).norm.preimage_mem_nhds
      (Iio_mem_nhds (by linarith))
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp (inter_mem hV (inter_mem (hD.mem_nhds hx) hn))
  refine ⟨U, hUo, hxU, (fun y hy => (hUsub hy).2.1),
    (fun y hy => (hUsub hy).2.2.le), ?_⟩
  intro a ha b hb
  have hr := lipschitzOnWith_iff_norm_sub_le.mp hLip (hUsub ha).1 (hUsub hb).1
  have hre : (γ a - d x a) - (γ b - d x b) = (γ a - γ b) - d x (a - b) := by
    rw [map_sub]
    abel
  simp only [Pi.sub_apply] at hr
  rw [hre] at hr
  have ht : ‖d x (a - b)‖ ≤ ‖γ a - γ b‖ + ‖(γ a - γ b) - d x (a - b)‖ := by
    have he : d x (a - b) = (γ a - γ b) - ((γ a - γ b) - d x (a - b)) := by abel
    nth_rw 1 [he]
    exact norm_sub_le _ _
  rw [norm_real_clm_apply] at ht
  change ‖(γ a - γ b) - d x (a - b)‖ ≤ δ * ‖a - b‖ at hr
  rw [Real.norm_eq_abs] at hr
  rw [Real.dist_eq, dist_eq_norm]
  nlinarith

end CircleDomainRigidity

end

end OAI
