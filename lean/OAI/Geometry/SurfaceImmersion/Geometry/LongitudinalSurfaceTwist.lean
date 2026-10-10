import OAI.Geometry.SurfaceImmersion.Whitney.ActualRuledTwist
import OAI.Geometry.SurfaceImmersion.Primitive.LocalizedTwistAngle
import OAI.Geometry.SurfaceImmersion.Geometry.TwistedAxisDerivative

namespace OAI

/-! Every smooth compact longitudinal angle is realized by an actual
 supported surface twist, with the same singular set and exact axis germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}
variable {S : CrosscapCoordinateStrip A} {c d : ℝ}

theorem ActualRuledRectangle.longitudinal_twist (R : ActualRuledRectangle S c d)
    (hac : A.arc.start < c) (hcd : c ≤ d) (hdb : d < A.arc.finish) :
    ∃ T : Base × ℝ → Fin 3 → ℝ, ContDiff ℝ ∞ T ∧
      ∀ α : ℝ → ℝ, ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo c d →
      ∃ (g : M → ProjectionTarget 3) (K : Set M),
        ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧ IsCompact K ∧ K ⊆ S.chart.source ∧
        (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
        (∀ x ∉ K, g =ᶠ[𝓝 x] R.replacement) ∧
        ∀ t ∈ Ioo c d, g =ᶠ[𝓝 (A.arc.curve t)]
          (twistedTubeSurface T (fun x => α (x 1))) ∘ S.chart := by
  obtain ⟨T,ε,hT,hε,htwist⟩ := R.twist_family hac hcd hdb
  refine ⟨T,hT,?_⟩
  intro α hα hc hs
  let θ := localizedTwistAngle (ε/2) α
  have hθ : ContDiff ℝ ∞ θ := localizedTwistAngle_smooth _ hα
  have hθc : HasCompactSupport θ := localizedTwistAngle_compact (half_pos hε) hc
  have hθs : tsupport θ ⊆ {x | |x 0| < ε ∧ x 1 ∈ Ioo c d} := by
    intro x hx
    obtain ⟨h0,h1⟩ := localizedTwistAngle_support (half_pos hε) α hx
    exact ⟨h0.trans_lt (half_lt_self hε),hs h1⟩
  obtain ⟨g,K,hg,hK,hKS,hreg,hout,hin⟩ := htwist θ hθ hθc hθs
  refine ⟨g,K,hg,hK,hKS,hreg,hout,?_⟩
  intro t ht
  have htab : t ∈ Icc A.arc.start A.arc.finish :=
    ⟨hac.le.trans ht.1.le,ht.2.le.trans hdb.le⟩
  have hsource := (S.axis t htab).1
  have hcoord : S.chart (A.arc.curve t) = crosscapAxis t :=
    (S.axis t htab).2.trans (crosscapAxis_apply t).symm
  have h0 : |S.chart (A.arc.curve t) 0| < ε := by
    simpa [hcoord,crosscapAxis_apply] using hε
  have h1 : S.chart (A.arc.curve t) 1 ∈ Ioo c d := by
    simpa [hcoord,crosscapAxis_apply] using ht
  have he : twistedTubeSurface T θ =ᶠ[𝓝 (crosscapAxis t)]
      twistedTubeSurface T (fun x => α (x 1)) := by
    filter_upwards [localizedTwistAngle_germ (ε/2) t α] with x hx
    simp only [twistedTubeSurface,Function.comp_apply,twistedRuledCoordinates]
    change θ x = α (x 1) at hx
    rw [hx]
  rw [← hcoord] at he
  exact (hin _ hsource h0 h1).trans (coordinate_replacement_germ S.chart hsource he)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
