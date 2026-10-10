import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CompactUpdateLp

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def smoothVoltageGradients (μ : Measure Coord3) (U : Set Coord3) :
    Set (Lp FieldVector 2 (μ.restrict U)) :=
  {z | ∃ (v : Coord3 → Fin 2 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
    ∃ (hg : MemLp (voltageGradient v) 2 (μ.restrict U)), z = hg.toLp _}

def allVoltageGradients (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (Lp FieldVector 2 (μ.restrict U)) :=
  (Submodule.span ℝ (smoothVoltageGradients μ U)).topologicalClosure

lemma CompactGlobalUpdate.fluxCorrection_pairing
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hvg : MemLp (voltageGradient v) 2 (μ.restrict U)) :
    inner ℝ (hvg.toLp _) ((R.memLp_flux_correction μ).toLp _) = 0 := by
  rw [L2.inner_def]
  have he : (∫ x, inner ℝ ((hvg.toLp _) x) (((R.memLp_flux_correction μ).toLp _) x) ∂μ.restrict U) =
      ∫ x, inner ℝ (voltageGradient v x) (fieldVector (R.dF x)) ∂μ.restrict U := by
    apply integral_congr_ae
    filter_upwards [hvg.coeFn_toLp,(R.memLp_flux_correction μ).coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [he,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp_rw [voltageGradient_pairing v (hv.differentiable (by simp))]
    have hvc : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => v x j) :=
      fun j => (contDiff_apply ℝ ℝ j).comp hv
    have hint : ∀ j, Integrable (fun x => fderiv ℝ (fun y => v y j) x ((R.dF x).col j)) μ := by
      intro j
      apply smooth_flux_integrable_pairing μ _
        ((continuous_pi (fun i => (continuous_apply j).comp (continuous_apply i))).comp R.smooth_dF.continuous)
        (R.compact_dF.comp_left (g := fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j) rfl)
        _ (hvc j)
    rw [integral_finsetSum _ (fun j _ => hint j)]
    simp only [R.cauchy_dF _ _ (hvc _),Finset.sum_const_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (R.support_dF hs))]
    simp only [show fieldVector 0 = 0 from map_zero fieldVectorCLM,inner_zero_right]

lemma CompactGlobalUpdate.fluxCorrection_mem_orthogonal
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (R.memLp_flux_correction μ).toLp _ ∈ (allVoltageGradients μ U)ᗮ := by
  let F := (R.memLp_flux_correction μ).toLp _
  let L : Lp FieldVector 2 (μ.restrict U) →L[ℝ] ℝ := innerSL ℝ F
  have hker : allVoltageGradients μ U ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨v,hv,hvg,rfl⟩
      change inner ℝ F (hvg.toLp _) = 0
      rw [real_inner_comm]
      exact R.fluxCorrection_pairing μ hv hvg
    · exact L.isClosed_ker
  intro z hz
  rw [real_inner_comm]
  exact hker hz

end ScalarConductivity

end
end

end OAI
