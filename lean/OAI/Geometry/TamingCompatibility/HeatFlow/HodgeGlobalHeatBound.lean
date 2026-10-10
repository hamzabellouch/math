import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgePushedHeatBound
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricDistance

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

lemma actual_pushedHeatKernel_bound {B : Type*} [NormedRing B] [SecondCountableTopology B]
    (p : X) (Q : Set (Space × Space)) (hQ : IsCompact Q)
    (hQt : Q ⊆ (extChartAt Model p).target ×ˢ (extChartAt Model p).target)
    (K : ℝ → Space × Space → B) (hsupp : ∀ t, Function.support (K t) ⊆ Q)
    (hKc : ∀ t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z))
    (n : ℕ) (T : ℝ) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hK : ∀ t, 0 < t → ∀ q y, ‖K t (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (pushedHeatKernel p K) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let L := Prod.fst '' Q ∪ Prod.snd '' Q
  have hL : IsCompact L := (hQ.image continuous_fst).union (hQ.image continuous_snd)
  have hLt : L ⊆ (extChartAt Model p).target := by
    rintro z (⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩)
    · exact (hQt hw).1
    · exact (hQt hw).2
  have hQL : Q ⊆ L ×ˢ L := fun z hz =>
    ⟨Or.inl ⟨z,hz,rfl⟩,Or.inr ⟨z,hz,rfl⟩⟩
  obtain ⟨C,hC⟩ := chartInverse_compact_lipschitz J α hs ht p L hL hLt
  obtain ⟨D,hD,hDb⟩ := chart_density_compact_bound J α hs ht p L hL hLt
  exact pushedHeatKernel_bound J α hs ht A p L hL hLt C hC D hD hDb K
    (fun t => (hsupp t).trans hQL) hKc n T ha hM hK

variable (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

lemma assemble_heatBound
    (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (hsupp : ∀ p t, Function.support (K p t) ⊆ (D p).physicalCompact)
    (hcont : ∀ p t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K p v.1 v.2) (t,z))
    (hgauss : ∀ p, ∃ M a : ℝ, 0 ≤ M ∧ 0 < a ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖K p t (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (n : ℕ) (T : ℝ) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (assemble A K) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  have hh (p : A.centers) : ∃ H : ℝ,
      VolterraKernel.HeatBound (geometricVolume A J α) n T H (pushedHeatKernel p.val (K p)) := by
    obtain ⟨M,a,hM,ha,hb⟩ := hgauss p
    exact actual_pushedHeatKernel_bound J α hs ht A p.val (D p).physicalCompact
      (D p).physicalCompact_compact (physicalCompact_target J α ht A D p)
      (K p) (hsupp p) (hcont p) n T ha hM hb
  choose H hH using hh
  have hb := VolterraKernel.HeatBound.finset_sum (geometricVolume A J α) Finset.univ n T H
    (fun p => pushedHeatKernel p.val (K p)) (fun p _ => hH p)
  have he : (fun t x y => ∑ p : A.centers, pushedHeatKernel p.val (K p) t x y) = assemble A K := by
    funext t x y
    by_cases h : 0 < t
    · simp only [pushedHeatKernel,assemble,ite_eq_left h]
    · simp only [pushedHeatKernel,assemble,ite_eq_right h,Finset.sum_const_zero]
  exact ⟨∑ p : A.centers, H p,he ▸ hb⟩

include hD in
lemma globalLeading_heatBound (n : ℕ) (T : ℝ) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (globalLeading J α ht A D) :=
  assemble_heatBound J α hs ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (leadingMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)
    (leadingMatrix_gaussian J α ht A D hD hs) n T

include hD in
lemma globalResidual_heatBound (n : ℕ) (T : ℝ) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (globalResidual J α ht A D) :=
  assemble_heatBound J α hs ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (residualMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)
    (residualFrameMatrix_gaussian J α ht A D hD hs) n T

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
