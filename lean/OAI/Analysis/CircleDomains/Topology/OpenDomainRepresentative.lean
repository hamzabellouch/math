import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientEnergy

namespace OAI

/-! A globally measurable representative of a smooth function on an open
physical plane domain, preserving its actual derivatives there. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

def openZeroExtension (D : Set EuclideanPlane) (w : EuclideanPlane → ℝ) : EuclideanPlane → ℝ := by
  classical
  exact D.piecewise w (fun _ => 0)

theorem openZeroExtension_eq {D : Set EuclideanPlane} {w : EuclideanPlane → ℝ}
    {x : EuclideanPlane} (hx : x ∈ D) : openZeroExtension D w x = w x := by
  classical
  exact piecewise_eq_of_mem D w (fun _ => 0) hx

theorem openZeroExtension_measurable {D : Set EuclideanPlane} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ} (hw : ContinuousOn w D) : Measurable (openZeroExtension D w) := by
  classical
  exact hw.measurable_piecewise continuousOn_const hD.measurableSet

theorem openZeroExtension_contDiffOn {D : Set EuclideanPlane}
    {w : EuclideanPlane → ℝ} (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D) :
    ContDiffOn ℝ (⊤ : ℕ∞) (openZeroExtension D w) D :=
  hw.congr (fun _ hx => openZeroExtension_eq hx)

theorem openZeroExtension_fderiv {D : Set EuclideanPlane} (hD : IsOpen D)
    (w : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ D) :
    fderiv ℝ (openZeroExtension D w) x = fderiv ℝ w x := by
  have he : openZeroExtension D w =ᶠ[𝓝 x] w := by
    filter_upwards [hD.mem_nhds hx] with y hy
    exact openZeroExtension_eq hy
  exact he.fderiv_eq

theorem openZeroExtension_mem_Icc {D : Set EuclideanPlane} {w : EuclideanPlane → ℝ}
    (hw : ∀x ∈ D, w x ∈ Icc 0 1) : ∀x, openZeroExtension D w x ∈ Icc 0 1 := by
  classical
  intro x
  by_cases hx : x ∈ D
  · rw [openZeroExtension_eq hx]
    exact hw x hx
  · change D.piecewise w (fun _ => 0) x ∈ Icc 0 1
    rw [piecewise_eq_of_notMem D w (fun _ => 0) hx]
    exact ⟨le_rfl, zero_le_one⟩

theorem openZeroExtension_gradient_memLp {D : Set EuclideanPlane} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict D)) :
    MemLp (fun x => (fderiv ℝ (openZeroExtension D w) x) (EuclideanSpace.single i 1))
      2 (volume.restrict D) := by
  apply hw.ae_eq
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  rw [openZeroExtension_fderiv hD w hx]

end CircleDomainRigidity

end

end OAI
