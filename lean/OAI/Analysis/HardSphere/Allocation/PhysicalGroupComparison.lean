import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalObservedMass
import OAI.Analysis.HardSphere.Comparison.SumMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}

def physicalGroupReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (ψ : Jet (N+1) L) (g : Fin G) (m : ℕ) (t r R C S s₀ : ℝ) (u : Time) (b : Bool) :=
  ∑flags,∑a : GridAllocation (N+1) K (G*M),
    physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u (branchParticles g a) b
      (physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g flags a m r R C S s₀ (2*t) u)

theorem physical_group_common_comparison {N M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} {r : ℝ} (hψ : IsGroundVector (N+1) L r ψ)
    (g : Fin G) (m : ℕ) (t R C S s₀ h : ℝ) (u : Time) (hs : PhysicalScaleBounds m t r R C S s₀ h u)
    (hxy : x≠y) (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1)
    (hM : 0<M) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1 ≤ B) (hCpath : 0 ≤ Cpath)
    (hBt : routeDensityBound t ≤ ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ ≤ κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*datumCollisionBound t r h R C) ≤ 1)
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d
      ∂physicalDatumLaw g ψ m r R C S s₀ (2*t) u) ≤ ENNReal.ofReal Cpath) :
    ∃σ : Measure (Torus L×Torus L×Configuration N L), IsFiniteMeasure σ ∧
      σ univ=(physicalDatumLaw g ψ m r R C S s₀ (2*t) u) E ∧
      ∀b,
        let P := physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b
        IsFiniteMeasure P ∧ σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
          (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ B*Cpath := by
  classical
  let I := (Fin (N+1)→Bool)×GridAllocation (N+1) K (G*M)
  let μ : I→Measure (PhysicalDatum (N+1) K M G L) := fun i ↦
    physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g i.1 i.2 m r R C S s₀ (2*t) u
  have hT : 0 ≤ 2*t := by linarith [hs.time_pos]
  let (i : I) : IsFiniteMeasure (μ i) :=
    physicalBranchLaw_finite hL hK hψ g i.1 i.2 m R C S s₀ (2*t) hT u
  let σ : I→Measure (Torus L×Torus L×Configuration N L) := fun i ↦
    physicalCommonObserved hL g m t r R C S u (branchParticles g i.2) hxy ν (μ i) E
  let P : Bool→I→Measure (Torus L×Torus L×Configuration N L) := fun b i ↦
    physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u (branchParticles g i.2) b (μ i)
  have hsum : (∑i,μ i)=physicalDatumLaw g ψ m r R C S s₀ (2*t) u := by
    rw [Fintype.sum_prod_type]
    exact physicalBranchLaw_sum hL hK ψ g m r R C S s₀ (2*t) u
  let F := E.indicator (fun d ↦ ∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d)
  let e : I→ℝ≥0∞ := fun i ↦ ∫⁻d,F d ∂μ i
  have hesum : ∑i,e i ≤ ENNReal.ofReal Cpath := by
    rw [←lintegral_finsetSum_measure,hsum]
    simpa only [F,lintegral_indicator hE] using henc
  have hei (i : I) : e i≠⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)).trans hesum
  have hbranch (i : I) :
      σ i univ=μ i E ∧ ∀b,(σ i≪P b i ∧
        Integrable (fun z ↦ ((σ i).rnDeriv (P b i) z).toReal^2) (P b i) ∧
        (∫z,((σ i).rnDeriv (P b i) z).toReal^2 ∂P b i) ≤ B*(e i).toReal) := by
    apply physical_common_observed_estimates hL g m t r R C S hs.time_pos hs.radius_le u
      (branchParticles g i.2) hxy ν (μ i) E hE hM (datumCollisionBound t r h R C)
      δ B κ (e i).toReal hδ hB ENNReal.toReal_nonneg hBt hκ hsmall
    · exact physical_branch_moment_data hL hK h50 (endpointWeightedBase ψ (2*t)) g i.1 i.2
        m t r R C S s₀ h u hs E hE ν hgood
    · exact ae_restrict_of_ae (physicalBranchLaw_primary hL hK h50 (endpointWeightedBase ψ (2*t))
        m r R C S s₀ t u g i.1 i.2 (siteIndex y))
    · rw [ENNReal.ofReal_toReal (hei i)]
      exact le_of_eq (lintegral_indicator hE _).symm
  let (i : I) : IsFiniteMeasure (σ i) := by dsimp only [σ]; infer_instance
  let (b : Bool) (i : I) : IsFiniteMeasure (P b i) := by dsimp only [P]; infer_instance
  refine ⟨∑i,σ i,inferInstance,?_,?_⟩
  · rw [Measure.finsetSum_apply]
    simp_rw [fun i ↦ (hbranch i).1]
    rw [←Measure.finsetSum_apply,hsum]
  · intro b
    have hp : physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b=∑i,P b i := by
      rw [Fintype.sum_prod_type]; rfl
    dsimp only
    rw [hp]
    refine ⟨inferInstance,?_,?_⟩
    · have H : Measure.sum σ≪∑i,P b i := Measure.absolutelyContinuous_sum_left (fun i ↦
        ((hbranch i).2 b).1.trans (Measure.absolutelyContinuous_of_le
          (Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i))))
      simpa only [Measure.sum_fintype] using H
    · have H := finite_sum_second_moment (P b) σ (fun i ↦ ((hbranch i).2 b).1)
        (fun i ↦ ((hbranch i).2 b).2.1)
      refine ⟨H.1,H.2.trans ?_⟩
      calc
        _ ≤ ∑i,B*(e i).toReal := Finset.sum_le_sum (fun i _ ↦ ((hbranch i).2 b).2.2)
        _ = B*(∑i,e i).toReal := by rw [←Finset.mul_sum,ENNReal.toReal_sum (fun i _ ↦ hei i)]
        _ ≤ B*Cpath := mul_le_mul_of_nonneg_left
          (by simpa only [ENNReal.toReal_ofReal hCpath] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hesum)
          (by linarith)

end HardSphere.Groups
end
end

end OAI
