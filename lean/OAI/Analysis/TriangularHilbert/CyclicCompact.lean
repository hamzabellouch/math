import OAI.Analysis.TriangularHilbert.CyclicMeasurable

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma integrable_cyclic_moment_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    Integrable (fun z : ℝ×ℝ => finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z)) := by
  classical
  obtain ⟨MB,_,hb⟩ := compactSupport_box B hsB
  obtain ⟨MC,_,hc⟩ := compactSupport_box C hsC
  obtain ⟨CB,hCB⟩ := hB.bounded_above_of_compact_support hsB
  obtain ⟨CC,hCC⟩ := hC.bounded_above_of_compact_support hsC
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun k _ => hr k)
  have hδr (k : κ) : δ ≤ r k := Finset.inf'_le _ (Finset.mem_univ k)
  apply integrable_cyclic_moment_box B C hB.measurable hC.measurable
    (M := max MB MC) (fun z hz => ⟨(hb z hz).1.trans (le_max_left _ _),(hb z hz).2.trans (le_max_left _ _)⟩)
    (fun z hz => ⟨(hc z hz).1.trans (le_max_right _ _),(hc z hz).2.trans (le_max_right _ _)⟩)
    ((norm_nonneg (B 0)).trans (hCB 0)) ((norm_nonneg (C 0)).trans (hCC 0))
    (show 0 ≤ 1/δ by positivity) hCB hCC (fun k => hardKernel (r k) (R k))
    (fun k => measurable_hardKernel _ _)
  exact fun k t => (abs_hardKernel_le (hr k) (hR k) t).trans (one_div_le_one_div_of_le hδ (hδr k))

lemma lintegral_cyclic_moment_le_compact (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    (hsB : HasCompactSupport B) (hsC : HasCompactSupport C)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cyclic_moment_compact B C hB hC hsB hsC r R hr hR)
    (Eventually.of_forall (fun z => finiteMoment_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (continuum_moment_le_compact B C hB hC hsB hsC r R hr hR)
end
end TriangularHilbert.Heat
end

end OAI
