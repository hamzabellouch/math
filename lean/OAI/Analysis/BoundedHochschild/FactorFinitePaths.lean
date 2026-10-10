import Mathlib
import OAI.Analysis.BoundedHochschild.FreeHaarFamilies

namespace OAI

/-! Simultaneous fresh-path tests in diffuse finite factors. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open BoundedHochschild HochschildRigidity HochschildPatching HochschildComparison
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
 

theorem finitePathTests_of_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) : HochschildRare.FinitePathTests τ := by
  classical
  intro C D T _ _ _ hD v r n w q hq hletters ε hε
  let ω : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨u,hu⟩ := exists_finite_graded_family e τ hτ h1 htr hfaith hfactor hdiff ω hω v (Finset.univ : Finset D)
  have hd : gradedDegree (C := C) (Finset.univ : Finset D)=HochschildPaths.freshProjection := by
    apply FreeGroup.ext_hom
    intro x
    cases x <;> simp [gradedDegree,HochschildPaths.freshProjection]
  have ht (t : T) : Tendsto
      (fun j => τ (FreeGroup.lift (HochschildRare.pathValue (Sum.elim v (u j)) (w t)) (q t) : M))
      (ω : Filter ℕ) (nhds 0) := by
    obtain ⟨s,a,hpos,huniq⟩ := hletters t
    have hne := HochschildPaths.freshProjection_pathHom_ne_one (w t) s a hpos huniq (q t) (hq t)
    have hz := hu (HochschildPaths.pathHom (w t) (q t)) (by rwa [hd])
    have hc := tendsto_sequenceTrace τ h1 ω
      (boundedHom (fun j => mixedFamily v (u j)) (HochschildPaths.pathHom (w t) (q t)))
    change Tendsto (fun j => τ (FreeGroup.lift (Sum.elim v (u j)) (HochschildPaths.pathHom (w t) (q t)) : M))
      (ω : Filter ℕ) (nhds (quotientTrace τ h1 ω htr
        (quotientFamily τ h1 ω htr (fun j => mixedFamily v (u j)) (HochschildPaths.pathHom (w t) (q t))))) at hc
    rw [hz] at hc
    simpa only [HochschildPaths.lift_pathValue_formal] using hc
  have he : ∀ᶠ j in (ω : Filter ℕ), ∀ t,
      ‖τ (FreeGroup.lift (HochschildRare.pathValue (Sum.elim v (u j)) (w t)) (q t) : M)‖ < ε := by
    apply eventually_all.mpr
    intro t
    have hh := (ht t).eventually (Metric.ball_mem_nhds (0:ℂ) hε)
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  obtain ⟨j,hj⟩ := he.exists
  exact ⟨u j,hj⟩

end HochschildUltrapower
end

end OAI
