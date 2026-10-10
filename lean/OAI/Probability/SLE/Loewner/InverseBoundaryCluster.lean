import OAI.Probability.SLE.Loewner.InverseBoundaryBound

namespace OAI

/-! Finite inverse-chart cluster points above the real axis lie on the
 physical domain boundary. No boundary extension is assumed. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma inverse_limit_mem_frontier {D : Set ℂ} (hD : IsOpen D)
    {g f : ℂ → ℂ} (hg : ContinuousOn g D)
    (hgH : MapsTo g D upperHalfPlane) (hfD : MapsTo f upperHalfPlane D)
    (hinv : ∀ w∈upperHalfPlane, g (f w)=w)
    {w : ℕ → ℂ} (hw : ∀ n, w n∈upperHalfPlane) {x : ℝ}
    (hlim : Tendsto w atTop (𝓝 (x:ℂ))) {z : ℂ}
    (hz : Tendsto (fun n => f (w n)) atTop (𝓝 z)) : z∈frontier D := by
  have hcl : z∈closure D := mem_closure_of_tendsto hz (Eventually.of_forall fun n => hfD (hw n))
  have hnot : z∉D := by
    intro hzin
    have hg' := ((hg z hzin).continuousAt (hD.mem_nhds hzin)).tendsto.comp hz
    have he : Tendsto w atTop (𝓝 (g z)) := by
      convert hg' using 1
      funext n
      exact (hinv (w n) (hw n)).symm
    have heq : g z=(x:ℂ) := tendsto_nhds_unique he hlim
    have him := hgH hzin
    rw [heq] at him
    change 0 < (x:ℂ).im at him
    norm_num at him
  exact ⟨hcl,by simpa only [hD.interior_eq] using hnot⟩

lemma IsCapacityTwoWitness.inverse_boundary_subsequence
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0)
    (w : ℕ → ℂ) (hw : ∀ n, w n∈upperHalfPlane) (x : ℝ)
    (hlim : Tendsto w atTop (𝓝 (x:ℂ))) :
    ∃ (φ : ℕ → ℕ) (z : ℂ), StrictMono φ ∧ z∈frontier (survivingDomain γ t) ∧
      Tendsto (fun n => F t (w (φ n))) atTop (𝓝 z) := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_range_of_tendsto w hlim).exists_norm_le
  obtain ⟨M,hM⟩ := h.inverse_bounded_over_ball t R
  obtain ⟨z,_,φ,hφ,hconv⟩ := (isCompact_closedBall (0:ℂ) M).tendsto_subseq (fun n => by
    rw [mem_closedBall,dist_zero_right]
    exact hM (w n) (hw n) (hR _ (mem_range_self n)))
  refine ⟨φ,z,hφ,?_,hconv⟩
  exact inverse_limit_mem_frontier (isOpen_survivingDomain h.1 t)
    ((h.2.2.2.1 t).continuousOn) (h.2.2.2.2.2.1 t) (h.2.2.2.2.2.2.1 t)
    (h.2.2.2.2.2.2.2.2.1 t) (fun n => hw (φ n)) (hlim.comp hφ.tendsto_atTop) hconv

end SLEExactGauge

end

end OAI
