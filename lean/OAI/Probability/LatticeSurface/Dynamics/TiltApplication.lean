import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedLattice
import OAI.Probability.LatticeSurface.Dynamics.TiltConsequences

namespace OAI

namespace BoundedLattice

open SparseBlocks MacroscopicAverages

def admissibleAverage (c C : ℝ) (V : Finset Vertex) (R : ℝ) (lo hi : Vertex) (q : Vertex →₀ ℝ) : Prop :=
  1≤R ∧ q.support ⊆ coordinateBox lo hi ∧
  (∀ x∈coordinateBox lo hi,∀ y∈coordinateBox lo hi,latticeDist x y≤C*R) ∧
  q.sum (fun _ t => |t|)≤C ∧ (∀ x,|q x|≤C*R^(-2:ℤ)) ∧
  ((q.sum (fun _ t => t))=0 ∨ ∃ P : Finset Vertex,
    P⊆coordinateBox lo hi ∧ Disjoint P V ∧
    (TriangularLipschitz.latticeGraph.induce (P:Set Vertex)).Connected ∧
    ∃ x∈P,∃ y∈P,c*R≤latticeDist x y)

end BoundedLattice

namespace BoundedLattice

open Set MeasureTheory SparseBlocks MacroscopicAverages SmallTilts

open scoped NNReal ENNReal

theorem macroscopic_linear_tilts (c C B : ℝ) (hc : 0<c) (hC : 0<C) :
    ∃ a : ℝ,0<a ∧ ∃ M : ℝ≥0,∀ (D V : Finset Vertex), V⊆D →
    (∀ x∈V,∀ y,Adj x y → y∈D) → ∀ (b : Vertex → ℝ),
    (∀ x∉V,|b x|≤B) → 0<volume (finiteDomainBody D V b) →
    ∀ (R : ℝ) (lo hi : Vertex) (q : Vertex →₀ ℝ),admissibleAverage c C V R lo hi q →
    ∀ t : ℝ,2*|t|≤a →
    let μ := finiteDomainLaw D V b
    let Y := fun h => t*statistic V b q h
    IsProbabilityMeasure (SmallTilts.tilted μ Y) ∧ (∫⁻ h,(density μ Y h)^2 ∂μ)≤(M:ENNReal)^3 ∧
    (∀ s : Set (V → ℝ),MeasurableSet s → SmallTilts.tilted μ Y s≤(M:ENNReal)^(3/2:ℝ)*(μ s)^(1/2:ℝ)) ∧
    ∀ (R' : ℝ) (lo' hi' : Vertex) (q' : Vertex →₀ ℝ),admissibleAverage c C V R' lo' hi' q' →
    ∀ k : ℕ,(∫⁻ h,ENNReal.ofReal (|statistic V b q' h|^k) ∂SmallTilts.tilted μ Y)≤
      (M:ENNReal)^(3/2:ℝ)*(ENNReal.ofReal (((2*k).factorial:ℝ)/a^(2*k))*(M:ENNReal))^(1/2:ℝ) := by
  obtain ⟨a,ha,M,hM⟩ := macroscopic_exponential_moments c C B hc hC
  refine ⟨a,ha,M,?_⟩
  intro D V hVD hcollar b hb hpos R lo hi q hq t ht
  dsimp only
  have hpos' : 0<volume (body V b) := by rwa [finiteDomainBody_eq D V hVD hcollar b hpos] at hpos
  obtain ⟨π,hπ,hfst,_⟩ := one_sample_bounded_data V b (max B 0) (le_max_right _ _) (fun x hx => (hb x hx).trans (le_max_left _ _)) hpos'
  let := hπ
  have hprob : IsProbabilityMeasure (finiteDomainLaw D V b) := by
    rw [finiteDomainLaw_eq D V hVD hcollar b hpos,← hfst]
    infer_instance
  have hm (R : ℝ) (lo hi : Vertex) (q : Vertex →₀ ℝ) (hq : admissibleAverage c C V R lo hi q) :
      (∫⁻ h,ENNReal.ofReal (Real.exp (a*|statistic V b q h|)) ∂finiteDomainLaw D V b)≤M :=
    hM D V hVD hcollar b hb hpos R hq.1 lo hi q hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
  have hY : Measurable (fun h => t*statistic V b q h) := measurable_const.mul (continuous_statistic V b q).measurable
  have hYmoment := small_multiple_bound (finiteDomainLaw D V b) (statistic V b q) a t ht M (hm R lo hi q hq)
  have htilt := small_linear_tilt (finiteDomainLaw D V b) _ hY M hYmoment
  refine ⟨htilt.1,htilt.2.1,fun s hs => event_bound _ _ hY M hYmoment s hs,?_⟩
  intro R' lo' hi' q' hq' k
  exact tilted_moment_bound (finiteDomainLaw D V b) _ _ hY (continuous_statistic V b q').measurable
    M M a ha k hYmoment (hm R' lo' hi' q' hq')

end BoundedLattice

end OAI
