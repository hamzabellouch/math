import OAI.Analysis.TriangularHilbert.ContinuumMesh

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter MatrixEnergy
open scoped Topology BigOperators
noncomputable section

lemma continuum_moment_le_box (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3)) := by
  classical
  let δ : ℝ := min 1 (Finset.univ.inf' Finset.univ_nonempty r)
  have hδ : 0 < δ := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr (fun k _ => hr k))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδr (k : κ) : δ ≤ r k := (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ k))
  let h : ℕ → ℝ := fun n => δ/((n:ℝ)+1)
  have hh (n : ℕ) : 0 < h n := div_pos hδ (by positivity)
  have hhδ (n : ℕ) : h n ≤ δ := (div_le_self hδ.le (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hh1 (n : ℕ) : h n ≤ 1 := (hhδ n).trans hδ1
  have ht : Tendsto h atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using (tendsto_const_nhds (x := δ)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs := sampled_moment_tendsto B C hB hC hsB hsC hCB hCC (show 0 ≤ 1/δ by positivity) hb hc
    hh hh1 ht (fun k => hardKernel (r k) (R k)) (fun k => measurable_hardKernel _ _)
    (fun k t => (abs_hardKernel_le (hr k) (hR k) t).trans (one_div_le_one_div_of_le hδ (hδr k)))
    (fun k z => ae_continuousAt_hardKernel (r k) (R k) (z.1+z.2))
  have hsB' := sampled_cubic_tendsto B hB hsB hCB hb hh hh1 ht
  have hsC' := sampled_cubic_tendsto C hC hsC hCC hc hh hh1 ht
  exact le_of_tendsto_of_tendsto hs (tendsto_const_nhds.mul (hsB'.add hsC'))
    (Filter.Eventually.of_forall (fun n => sampled_moment_le B C (hh n) hsB hsC r R
      (fun k => (hhδ n).trans (hδr k)) hR))

lemma continuum_moment_le_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) ≤
      momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3)) := by
  obtain ⟨MB,hMB,hb⟩ := compactSupport_box B hsB
  obtain ⟨MC,hMC,hc⟩ := compactSupport_box C hsC
  obtain ⟨CB,hCB⟩ := hB.bounded_above_of_compact_support hsB
  obtain ⟨CC,hCC⟩ := hC.bounded_above_of_compact_support hsC
  have hCB0 : 0 ≤ CB := (norm_nonneg (B 0)).trans (hCB 0)
  have hCC0 : 0 ≤ CC := (norm_nonneg (C 0)).trans (hCC 0)
  exact continuum_moment_le_box B C hB hC
    (M := max MB MC) (fun z hz => ⟨(hb z hz).1.trans (le_max_left _ _),(hb z hz).2.trans (le_max_left _ _)⟩)
    (fun z hz => ⟨(hc z hz).1.trans (le_max_right _ _),(hc z hz).2.trans (le_max_right _ _)⟩)
    hCB0 hCC0 hCB hCC r R hr hR
end
end TriangularHilbert.Heat
end

end OAI
