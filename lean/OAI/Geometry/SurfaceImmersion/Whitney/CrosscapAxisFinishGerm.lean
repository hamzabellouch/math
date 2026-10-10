import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisStartGerm
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcReverse

namespace OAI

/-! The terminal exterior germ can likewise be made an exact kernel-axis
germ while preserving the closed trace and the initial germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {q : M}

theorem crosscap_axis_finish_germ (c : SurfaceCrosscapCoordinates f q)
    (P : SmoothCompactArc planeModel M) (hPf : P.curve P.finish = q)
    {V : Set M} (hV : IsOpen V) (hqV : q ∈ V)
    (haxis : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ c.source.source ∧ c.source (P.curve u) 0 = 0) :
    ∃ (R : SmoothCompactArc planeModel M) (e : ℝ ≃ₜ ℝ),
      R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ e P.finish = 0 ∧
      R.curve =ᶠ[𝓝 P.finish] c.axisCurve ∘ e ∧
      R.curve =ᶠ[𝓝 P.start] P.curve := by
  obtain ⟨S,hSs,hSf,_,hSc,_⟩ := P.reverse_arc
  have hSstart : S.curve S.start = q := by rw [hSc,hSs]; simpa using hPf
  have hSaxis : ∀ u ∈ Icc S.start S.finish, S.curve u ∈ V →
      S.curve u ∈ c.source.source ∧ c.source (S.curve u) 0 = 0 := by
    intro u hu hUV
    rw [hSs,hSf] at hu
    rw [hSc] at hUV ⊢
    exact haxis (-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩ hUV
  obtain ⟨T,e,hTs,hTf,hTS,hes,hei,he0,hTe,hTSf⟩ :=
    crosscap_axis_start_germ c S hSstart hV hqV hSaxis
  obtain ⟨R,hRs,hRf,_,hRc,_⟩ := T.reverse_arc
  let E := (Homeomorph.neg ℝ).trans e
  have hEs : ContDiff ℝ ∞ E := hes.comp contDiff_neg
  have hEi : ContDiff ℝ ∞ E.symm := contDiff_neg.comp hei
  have hEs0 : E P.finish = 0 := by
    change e (-P.finish) = 0
    rwa [hSs] at he0
  have hRS : R.start = P.start := by rw [hRs,hTf,hSf,neg_neg]
  have hRF : R.finish = P.finish := by rw [hRf,hTs,hSs,neg_neg]
  have hRP : EqOn R.curve P.curve (Icc P.start P.finish) := by
    intro u hu
    have hneg : -u ∈ Icc S.start S.finish := by rw [hSs,hSf]; constructor <;> linarith [hu.1,hu.2]
    rw [hRc]
    dsimp only
    rw [hTS hneg,hSc]
    simp only [neg_neg]
  have hnFinish : Tendsto (fun u : ℝ => -u) (𝓝 P.finish) (𝓝 S.start) := by
    rw [hSs]
    exact continuous_neg.continuousAt
  have hnStart : Tendsto (fun u : ℝ => -u) (𝓝 P.start) (𝓝 S.finish) := by
    rw [hSf]
    exact continuous_neg.continuousAt
  have hRgerm : R.curve =ᶠ[𝓝 P.finish] c.axisCurve ∘ E := by
    filter_upwards [hnFinish.eventually hTe] with u hu
    rw [hRc]
    exact hu
  have hRold : R.curve =ᶠ[𝓝 P.start] P.curve := by
    filter_upwards [hnStart.eventually hTSf] with u hu
    rw [hRc]
    dsimp only
    rw [hu,hSc]
    simp only [neg_neg]
  exact ⟨R,E,hRS,hRF,hRP,hEs,hEi,hEs0,hRgerm,hRold⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
