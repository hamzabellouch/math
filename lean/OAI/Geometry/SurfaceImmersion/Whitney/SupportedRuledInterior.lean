import OAI.Geometry.SurfaceImmersion.Whitney.InteriorRulingSupport
import OAI.Geometry.SurfaceImmersion.Whitney.NarrowedRulingBounds
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedRegularChange
import OAI.Geometry.SurfaceImmersion.Whitney.NarrowedRulingJets

namespace OAI

/-! An actual compactly supported ruled replacement on a regular inner
part of the joining arc, with no change to the singular set. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.supported_ruled_interior (S : CrosscapCoordinateStrip A)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo A.arc.start A.arc.finish) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Base → ProjectionTarget 3, ContDiff ℝ ∞ Q ∧ HasCompactSupport Q ∧
      tsupport Q ⊆ S.domain ∧
      (∀ x, ‖Q x‖ < ε ∧ ‖fderiv ℝ Q x‖ < ε) ∧
      (∀ t, Q (crosscapAxis t) = 0 ∧ fderiv ℝ Q (crosscapAxis t) = 0) ∧
      (∀ x, Function.Injective (fderiv ℝ (S.model+Q) x) ↔
        Function.Injective (fderiv ℝ S.model x)) ∧
      (∀ t, η =ᶠ[𝓝 t] 1 → S.model+Q =ᶠ[𝓝 (crosscapAxis t)] transverseRuling S.model) ∧
      ∀ t, t ∉ tsupport η → S.model+Q =ᶠ[𝓝 (crosscapAxis t)] S.model := by
  obtain ⟨δ,K,hδ,hK,hKD,hKI,hKQ⟩ := S.interior_ruling_support hc hs
  obtain ⟨τ,hτ,hstable⟩ := supported_regular_change S.model_smooth hK hKI
  obtain ⟨r,hr,hrδ,_hr1,hsmall⟩ := narrowedRuling_small S.model_smooth hη hc (lt_min hε hτ) hδ
  let Q := narrowedRuling S.model η r
  have hQ : ContDiff ℝ ∞ Q := narrowedRuling_smooth S.model_smooth hη r
  have hQK : tsupport Q ⊆ K := hKQ r hr hrδ
  refine ⟨Q,hQ,narrowedRuling_compact S.model hc hr,hQK.trans hKD,?_,?_,?_,?_,?_⟩
  · intro x
    exact ⟨(hsmall x).1.trans_le (min_le_left _ _),(hsmall x).2.trans_le (min_le_left _ _)⟩
  · intro t
    exact ⟨narrowedRuling_axis S.model η r t,narrowedRuling_first_jet S.model_smooth hη r t⟩
  · exact hstable Q hQ hQK (fun x => (hsmall x).2.trans_le (min_le_right _ _))
  · intro t ht
    have heta : (fun x : Base => η (x 1)) =ᶠ[𝓝 (crosscapAxis t)] 1 := by
      have hpr : Tendsto (fun x : Base => x 1) (𝓝 (crosscapAxis t)) (𝓝 t) := by
        simpa [crosscapAxis_apply, Matrix.cons_val_one, Matrix.cons_val_zero] using (continuous_apply (1 : Fin 2)).continuousAt.tendsto (x := crosscapAxis t)
      exact ht.comp_tendsto hpr
    filter_upwards [transverseCutoff_axis_germ r t,heta] with x hx hy
    change S.model x+transverseCutoff r x • (η (x 1) • (transverseRuling S.model x-S.model x)) = _
    simp only [Pi.one_apply] at hx hy
    rw [hx,hy,one_smul,one_smul]
    abel
  · intro t ht
    have heta : (fun x : Base => η (x 1)) =ᶠ[𝓝 (crosscapAxis t)] 0 := by
      have hpr : Tendsto (fun x : Base => x 1) (𝓝 (crosscapAxis t)) (𝓝 t) := by
        simpa [crosscapAxis_apply, Matrix.cons_val_one, Matrix.cons_val_zero] using (continuous_apply (1 : Fin 2)).continuousAt.tendsto (x := crosscapAxis t)
      exact (notMem_tsupport_iff_eventuallyEq.mp ht).comp_tendsto hpr
    filter_upwards [heta] with x hx
    change S.model x+transverseCutoff r x • (η (x 1) • (transverseRuling S.model x-S.model x)) = _
    simp only [Pi.zero_apply] at hx
    rw [hx,zero_smul,smul_zero,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
