import Mathlib
import OAI.Analysis.HardSphere.Allocation.SpatialSeparatedCloseJoint

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

variable {n : ℕ} [Nontrivial (Fin n)]

attribute [local irreducible] torusDistance nearestParticleDistance

lemma localCloseLabels_measurable (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun X : Configuration n L ↦ ((localCloseLabels L s v X).card:ℝ)) := by
  classical
  simp only [localCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun X : Configuration n L ↦ torusDistance L (X i) v) :=
    (torusDistance_continuous_pair L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration n L ↦ v)))
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter
    (measurableSet_le (nearestParticleDistance_continuous L i).measurable measurable_const))
    measurable_const measurable_const

theorem spatial_separated_close_probability : ∃ C c G : ℝ, 0<C ∧ 0<c ∧ 0<G ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r b D h : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0<r → 0<b → 0<h →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 → (C+1)*D≤c/b^3*(h/4) →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), (∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w) →
      groundPositionLaw n L g {X | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) v X).card:ℝ)}≤
        ENNReal.ofReal ((G/(h*(spatialCloseScale D b)^2)/((D*r)*D))^A.card) := by
  obtain ⟨C,c,G,hC,hc,hG,hjoint⟩ := spatial_separated_close_joint
  refine ⟨C,c,G,hC,hc,hG,?_⟩
  intro n K _ L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg A hA
  have hs := spatialCloseScale_pos (zero_lt_one.trans_le hD) hb
  obtain ⟨φ,hφ,hφe⟩ := exists_close_mollifier (n:=n) (spatialCloseScale D b) h hs hh
  let T : Set (Configuration n L) := {X | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) v X).card:ℝ)}
  have hT : MeasurableSet T := by
    simpa only [T,Set.ofPred_forall] using Finset.measurableSet_biInter A (fun v _ ↦
      measurableSet_le (show Measurable (fun _ : Configuration n L ↦ 8*h) from measurable_const)
        (localCloseLabels_measurable L (spatialCloseScale D b) v))
  have ht := groundPositionLaw_le_closeJoint L hs (by linarith only [hs1]) hh φ hφe A g T hT (fun _ hX ↦ hX)
  exact ht.trans (ENNReal.ofReal_le_ofReal (hjoint n K L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg φ hφ hφe A hA))

end HardSphere

end

end OAI
