import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedNormalCoordinates

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function Filter Topology

theorem exists_isometric_frame_subsequence {n d : ℕ}
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
      Tendsto (fun j => (L (ρ j)).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) := by
  let A : ℕ → Ambient n →L[ℝ] Ambient d := fun j => (L j).toContinuousLinearMap
  have hbound : ∀ j, A j ∈ closedBall 0 1 := by
    intro j
    rw [mem_closedBall, dist_zero_right]
    apply ContinuousLinearMap.opNorm_le_bound (A j) zero_le_one
    intro x
    simpa only [A, LinearIsometry.coe_toContinuousLinearMap, (L j).norm_map, one_mul]
      using! (le_rfl : ‖x‖ ≤ ‖x‖)
  obtain ⟨T, _hT, ρ, hρ, hlim⟩ := (isCompact_closedBall (0 : Ambient n →L[ℝ] Ambient d) 1).tendsto_subseq hbound
  have hnorm : ∀ x, ‖T x‖ = ‖x‖ := by
    intro x
    have heval : Continuous (fun B : Ambient n →L[ℝ] Ambient d => B x) := by fun_prop
    have ht : Tendsto (fun j => ‖A (ρ j) x‖) atTop (𝓝 ‖T x‖) :=
      ((heval.tendsto T).comp hlim).norm
    have ht' : Tendsto (fun j => ‖A (ρ j) x‖) atTop (𝓝 ‖x‖) := by
      simpa only [A, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map] using!
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))
    exact tendsto_nhds_unique ht ht'
  let Llim : Ambient n →ₗᵢ[ℝ] Ambient d := { toLinearMap := T.toLinearMap, norm_map' := hnorm }
  refine ⟨ρ, hρ, Llim, ?_⟩
  convert! hlim using 1

theorem tangentPlaneProjection_tendsto {n d : ℕ}
    (a : ℕ → Ambient d) (alim : Ambient d) (ha : Tendsto a atTop (𝓝 alim))
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (Llim : Ambient n →ₗᵢ[ℝ] Ambient d)
    (hL : Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap))
    (x : Ambient d) :
    Tendsto (fun j => tangentPlaneProjection (a j) (L j) x) atTop
      (𝓝 (tangentPlaneProjection alim Llim x)) := by
  let P : (Ambient d × (Ambient n →L[ℝ] Ambient d)) → Ambient d :=
    fun p => p.1 + p.2 (p.2.adjoint (x - p.1))
  have hc : Continuous P := by
    apply continuous_fst.add
    apply continuous_snd.clm_apply
    exact (ContinuousLinearMap.adjoint.continuous.comp continuous_snd).clm_apply
      (continuous_const.sub continuous_fst)
  exact (hc.tendsto (alim, Llim.toContinuousLinearMap)).comp (ha.prodMk_nhds hL)

end

end RieszRectifiability

end OAI
