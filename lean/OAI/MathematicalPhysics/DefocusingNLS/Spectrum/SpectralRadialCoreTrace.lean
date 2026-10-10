import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialUniformEvaluation
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! The vanishing-volume core condition also gives zero trace at its positive boundary. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralRadialVolume_absolutelyContinuous (R : ℝ) :
    volume.restrict (Icc (0 : ℝ) R) ≪ radialPressureMeasure R := by
  unfold radialPressureMeasure
  apply withDensity_absolutelyContinuous' (by fun_prop)
  have hn : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by simp only [ae_iff]; simp
  filter_upwards [ae_restrict_mem measurableSet_Icc,hn.filter_mono ae_restrict_le] with r hr hn
  rw [max_eq_left hr.1]
  exact (ENNReal.ofReal_pos.mpr (pow_pos (lt_of_le_of_ne hr.1 (Ne.symm hn)) 11)).ne'

theorem spectralRadialCore_point_zero (R l : ℝ) (hR : 0 < R) (hl : 0 < l) (hlR : l ≤ R)
    (u : SpectralRadialEnergy R)
    (hu : (fun r => spectralRadialValue R u r) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0) :
    spectralRadialPointValue R hR l hl u=0 := by
  have hu' : ∀ᵐ r ∂radialPressureMeasure R, r ≤ l → spectralRadialValue R u r=0 := by
    simpa only [mem_Iic,Pi.zero_apply] using (ae_restrict_iff' measurableSet_Iic).mp hu
  have hrep : ∀ᵐ r ∂radialPressureMeasure R,
      r ≤ l → spectralRadialRepresentative R hR u r=0 := by
    filter_upwards [spectralRadialRepresentative_ae R hR u,hu'] with r hr hz hrl
    exact hr.trans (hz hrl)
  have hbase := (spectralRadialVolume_absolutelyContinuous R).ae_le hrep
  have hsub : Icc (l/2) l ⊆ Icc (0 : ℝ) R := by
    intro r hr
    exact ⟨(by linarith : 0 ≤ l/2).trans hr.1,hr.2.trans hlR⟩
  have hle : volume.restrict (Icc (l/2) l) ≤ volume.restrict (Icc (0 : ℝ) R) :=
    Measure.restrict_mono hsub le_rfl
  have hlocal := (Measure.absolutelyContinuous_of_le hle).ae_le hbase
  have hae : spectralRadialRepresentative R hR u =ᵐ[volume.restrict (Icc (l/2) l)] 0 := by
    filter_upwards [hlocal,ae_restrict_mem measurableSet_Icc] with r hr hm
    exact hr hm.2
  have hcont : ContinuousOn (spectralRadialRepresentative R hR u) (Icc (l/2) l) :=
    (spectralRadialRepresentative_continuousOn R (l/2) hR (by linarith) u).mono
      (fun _ hr => ⟨hr.1,hr.2.trans hlR⟩)
  have he := Measure.eqOn_Icc_of_ae_eq volume (show l/2 ≠ l by linarith)
    hae hcont continuousOn_const (show l ∈ Icc (l/2) l from ⟨by linarith,le_rfl⟩)
  simpa only [spectralRadialRepresentative,dite_eq_left hl,Pi.zero_apply] using he

end DefocusingNLS

end OAI
