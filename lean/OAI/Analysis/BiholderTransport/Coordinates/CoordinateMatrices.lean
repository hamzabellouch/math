import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.CoordinatePole
import OAI.Analysis.BiholderTransport.Coordinates.GraphCoordinates

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateCenterMatrix (a : M) (t : ℝ) (G : M → ℝ) (b p : Model n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+
    fderiv ℝ (fderiv ℝ (fun q=>G (movingPrefix a t b q))) p

omit [Nonempty M] in
lemma coordinatePoleMatrix_chart {a c : M} {t : ℝ} {v : M → ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinatePoleMatrix a t v b p=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p-
      fderiv ℝ (fderiv ℝ (fun q=>hopfLax t (cTransform v)
        ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))) p := by
  exact congrArg (fun B=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p-B)
    (((movingPrefix_chart_pullback hb hc _).fderiv (𝕜 := ℝ)).fderiv_eq.symm)

omit [Nonempty M] in
lemma coordinateCenterMatrix_chart {a c : M} {t : ℝ} {G : M → ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinateCenterMatrix a t G b p=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+
      fderiv ℝ (fderiv ℝ (fun q=>G
        ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))) p := by
  exact congrArg (fun B=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+B)
    (((movingPrefix_chart_pullback hb hc _).fderiv (𝕜 := ℝ)).fderiv_eq.symm)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma graphCoordinate_normalSubdifferential {a : M} {u : M → ℝ}
    (q : subgradientGraph (n := n) u)
    (hq : q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    chartFiberInverse a (graphBaseCoordinate a q.1) (graphVelocityCoordinate a q.1)∈
      normalSubdifferential (n := n) u
        ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q.1)) := by
  exact (congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>z.2∈normalSubdifferential u z.1)
    (graph_coordinate_reconstruction hq)).mpr q.2

lemma WeakMTW.graphCoordinate_prefix_regular (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a : M} (q : subgradientGraph (n := n) (cTransform v))
    (hq : q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    t • chartFiberInverse a (graphBaseCoordinate a q.1) (graphVelocityCoordinate a q.1)∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q.1)) := by
  exact (congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>t • z.2∈injectivityDomain z.1)
    (graph_coordinate_reconstruction hq)).mpr (hmtw.active_hull_precut hv ht ht1 _ _
      (normalSubdifferential_subset_active_hull hv _ q.2))

end WeakMTWTransport

end

end OAI
