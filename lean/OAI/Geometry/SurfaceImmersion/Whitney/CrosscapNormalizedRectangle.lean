import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedTwoZeroAxis

namespace OAI

/-! The normalized rectangle is constructed from the actual crosscap strip. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.normalized_defect_rectangle (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (d : ℝ → Base) (r : ℝ) (O : Set Base),
      ContDiff ℝ ∞ d ∧ 0 < r ∧ IsOpen O ∧ O ⊆ S.domain ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (A.arc.start-r) (A.arc.finish+r), (![x,t] : Base) ∈ O) ∧
      ContDiffOn ℝ ∞ (axisNormalizedDefect d (normalDefect S.model a)) O ∧
      (∀ t, crosscapAxis t ∈ O →
        axisNormalizedDefect d (normalDefect S.model a) (crosscapAxis t) =
          ![(t-A.arc.start)*(t-A.arc.finish),0]) ∧
      (∀ x ∈ O, axisNormalizedDefect d (normalDefect S.model a) x = 0 ↔
        x = crosscapAxis A.arc.start ∨ x = crosscapAxis A.arc.finish) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.start)) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.finish)) ∧
      (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.start) (![1,0] : Base)) 1 ≠ 0 ∧
      (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.finish) (![1,0] : Base)) 1 ≠ 0 := by
  obtain ⟨a,δ,U,hδ,hU,hUD,hrect,hN,hz,hDp,hDq⟩ := S.nondegenerate_normal_defect hf
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ U := by
    intro t ht
    rw [crosscapAxis_apply]
    apply hrect 0 (by constructor <;> linarith) t
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨d,V,W,hd,hV,hVU,hW,hKW,hWa,hGV,hGa,hGz,hDpG,hDqG,hvp,hvq⟩ :=
    normalized_two_zero_axis hU hN A.arc.start_lt_finish haxis
      (by simpa only [crosscapAxis_apply] using hz)
      (by simpa only [crosscapAxis_apply] using hDp)
      (by simpa only [crosscapAxis_apply] using hDq)
  let O := V ∩ {x : Base | x 1 ∈ W}
  have hO : IsOpen O := hV.inter (hW.preimage (continuous_apply 1))
  have hKO : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ O := by
    intro t ht
    refine ⟨hWa t (hKW ht),?_⟩
    simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using hKW ht
  obtain ⟨r,hr,hrrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hO
    (by simpa only [crosscapAxis_apply] using hKO)
  refine ⟨a,d,r,O,hd,hr,hO,inter_subset_left.trans (hVU.trans hUD),hrrect,
    hGV.mono inter_subset_left,?_,fun x hx => hGz x hx.1,hDpG,hDqG,hvp,hvq⟩
  intro t ht
  apply hGa t
  simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using ht.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
