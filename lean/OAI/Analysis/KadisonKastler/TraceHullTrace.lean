import OAI.Analysis.KadisonKastler.BoundaryDiagonal

namespace OAI

/-! # The trace is constant on trace-closed convex orbit hulls -/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- A trace value shared by every generator is shared by every algebra
element in the trace Hilbert closure of their convex hull. -/
theorem trace_eq_of_mem_traceHull (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    {S : Set (Algebra M)} {c : ℂ} (hS : ∀ x ∈ S, τ.toLinearMap x = c)
    {b : Algebra M} (hb : J b ∈ diagonalTraceHull J S) : τ.toLinearMap b = c := by
  have hconv : ∀ x ∈ convexHull ℝ S, τ.toLinearMap x = c := by
    have hc : Convex ℝ {x : Algebra M | τ.toLinearMap x = c} :=
      (convex_singleton c).linear_preimage (τ.toLinearMap.restrictScalars ℝ)
    exact convexHull_min hS hc
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hb
  choose x hxmem hx using hv
  have htrace (n : ℕ) : τ.toLinearMap (x n) = c := hconv _ (hxmem n)
  have hbound (n : ℕ) : ‖τ.toLinearMap (x n) - τ.toLinearMap b‖ ≤ ‖v n - J b‖ := by
    calc
      _ = ‖τ.toLinearMap (x n - b)‖ := by rw [map_sub]
      _ ≤ traceTwoNorm τ (x n - b) := τ.norm_apply_le_traceTwoNorm _
      _ = ‖J (x n - b)‖ := (hJ _).symm
      _ = _ := by rw [map_sub, hx]
  have hlim : Tendsto (fun n => ‖τ.toLinearMap (x n) - τ.toLinearMap b‖)
      atTop (𝓝 0) := by
    have ht := (hvlim.sub_const (J b)).norm
    simp only [sub_self, norm_zero] at ht
    exact squeeze_zero (fun n => norm_nonneg _) hbound ht
  have he : ‖c - τ.toLinearMap b‖ = 0 := by
    have hconst : Tendsto (fun _ : ℕ => ‖c - τ.toLinearMap b‖) atTop (𝓝 0) := by
      simpa only [htrace] using hlim
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

end

end KadisonKastler

end OAI
