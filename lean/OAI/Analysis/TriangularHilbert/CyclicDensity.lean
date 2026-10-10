import OAI.Analysis.TriangularHilbert.CubicLimit

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclic_hard (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : AEMeasurable (cyclicKernelOutput B C (hardKernel r R)) volume := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_cyclicKernelOutput (F n) (G n) (hF n).1.measurable (hG n).1.measurable _
      (measurable_hardKernel r R)).aemeasurable)
  filter_upwards [ht] with z hz
  exact hz r R hr hR

lemma lintegral_cyclic_moment_le (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ) (hr : ∀ k, 0 < r k) (hR : ∀ k, r k ≤ R k) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput B C (hardKernel (r k) (R k)) z))) ≤
      ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖B z‖^3)+(∫ z : ℝ×ℝ, ‖C z‖^3))) := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply lintegral_le_of_ae_tendsto
    (F := fun n z => ENNReal.ofReal (finiteMoment (fun k => cyclicKernelOutput (F n) (G n) (hardKernel (r k) (R k)) z)))
    (b := fun n => ENNReal.ofReal (momentConstant*((∫ z : ℝ×ℝ, ‖F n z‖^3)+(∫ z : ℝ×ℝ, ‖G n z‖^3))))
  · intro n
    exact (ENNReal.continuous_ofReal.comp continuous_finiteMoment).measurable.comp
      (Measurable.of_eval (fun k => measurable_cyclicKernelOutput (F n) (G n)
        (hF n).1.measurable (hG n).1.measurable _ (measurable_hardKernel _ _))) |>.aemeasurable
  · filter_upwards [ht] with z hz
    exact (ENNReal.continuous_ofReal.comp continuous_finiteMoment).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun k => hz (r k) (R k) (hr k) (hR k)))
  · intro n
    exact lintegral_cyclic_moment_le_compact (F n) (G n) (hF n).1 (hG n).1 (hF n).2.1 (hG n).2.1 r R hr hR
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((tendsto_integral_cubes B F (fun n => (hF n).1) hD hb).add
        (tendsto_integral_cubes C G (fun n => (hG n).1) hE hc)))
end
end TriangularHilbert.Heat
end

end OAI
