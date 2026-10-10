import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Recursion.PrefixDepth
import OAI.MeasureTheory.FalconerCompletion.Recursion.TensorCapCompact
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixParallelMem

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ContDiff
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma prefixPhased_global_bound (z : PrefixAssignment n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ξ x w, ‖e.prefixPhasedLeft z ξ x w‖ ≤ D ∧
      ‖e.prefixPhasedRight z ξ x w‖ ≤ D := by
  obtain ⟨D,hD,hbound⟩ := e.prefixInverse_global_bound z
  refine ⟨D,hD,?_⟩
  intro ξ x w
  simpa only [prefixPhasedLeft,prefixPhasedRight,norm_mul,
    Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_norm,one_mul] using hbound x w

lemma prefixGraphChildMax_nonneg (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : ∀ r, 0 ≤ Ψ r)
    (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    0 ≤ e.prefixGraphChildMax v Ψ z ξ := by
  unfold prefixGraphChildMax _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax
  split
  · exact _root_.OAI.Attempt4Near.graphChildMaxND_nonneg _ _ _ _ _ hΨ _ _ _ _ _
  · exact le_rfl

lemma prefixGraphChildMax_global_bound [IsProbabilityMeasure e.ρ]
    (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (hpos : ∀ r, 0 ≤ Ψ r) (z : PrefixAssignment n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, e.prefixGraphChildMax v Ψ z ξ ≤ C := by
  obtain ⟨D,hD,hbound⟩ := e.prefixPhased_global_bound z
  let M : ℝ := ((2:ℝ)^e.N)^(-e.mass e.sourcePrefixDepth)
  let B : ℝ := |M⁻¹| *D
  have hB : 0 ≤ B := mul_nonneg (abs_nonneg _) hD
  let μ := _root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
  let A : ℝ := (2:ℝ)^(((n+1:ℕ):ℝ)*(v-e.sourcePrefixDepth))*((2:ℝ)^v)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := A*((∫ r, Ψ (r/(2:ℝ)^v))*(B^2*μ.real univ)^2)
  have hC : 0 ≤ C := mul_nonneg hA (mul_nonneg
    (integral_nonneg (fun r => hpos _)) (sq_nonneg _))
  have hb (P : _root_.OAI.CurrentFalconer.TreeND.CellPath (n+1)) (ξ : EuclideanSpace ℝ (Fin (n+1)))
      (r : ℝ) (w : EuclideanSpace ℝ (Fin (n+1))) :
      ‖_root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
        (_root_.OAI.CurrentFalconer.TreeND.treeCell P) M (e.prefixPhasedLeft z ξ) r w‖ ≤ B ∧
      ‖_root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
        (_root_.OAI.CurrentFalconer.TreeND.treeCell P) M (e.prefixPhasedRight z ξ) r w‖ ≤ B := by
    have hm : |M⁻¹| *(e.ρ (_root_.OAI.CurrentFalconer.TreeND.treeCell P)).toReal*D ≤ B := by
      change |M⁻¹| *e.ρ.real (_root_.OAI.CurrentFalconer.TreeND.treeCell P)*D ≤ |M⁻¹| *D
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (measureReal_le_one (μ:=e.ρ)) (abs_nonneg _)) hD).trans_eq
          (by ring)
    exact ⟨(_root_.OAI.CurrentFalconer.sourceAngularTransformND_norm_le _ _ _ _ _ _
      (fun x => (hbound ξ x w).1)).trans hm,
      (_root_.OAI.CurrentFalconer.sourceAngularTransformND_norm_le _ _ _ _ _ _
      (fun x => (hbound ξ x w).2)).trans hm⟩
  refine ⟨C,hC,?_⟩
  intro ξ
  have hleft := _root_.OAI.CurrentFalconer.sourceAngularTransformND_measurable e.ρ
  have hleftm := e.prefixPhasedLeft_measurable z ξ
  have hrightm := e.prefixPhasedRight_measurable z ξ
  have hchild (P Q : _root_.OAI.CurrentFalconer.TreeND.CellPath (n+1)) :
      _root_.OAI.Attempt4Near.sourceAngularHND (n+1) μ e.sourcePrefixDepth v Ψ
        (fun u => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
          (_root_.OAI.CurrentFalconer.TreeND.treeCell P) M (e.prefixPhasedLeft z ξ) u.1 u.2)
        (fun u => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
          (_root_.OAI.CurrentFalconer.TreeND.treeCell Q) M (e.prefixPhasedRight z ξ) u.1 u.2) ≤ C := by
    let U := fun u : ℝ × EuclideanSpace ℝ (Fin (n+1)) =>
      _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
        (_root_.OAI.CurrentFalconer.TreeND.treeCell P) M (e.prefixPhasedLeft z ξ) u.1 u.2
    let W := fun u : ℝ × EuclideanSpace ℝ (Fin (n+1)) =>
      _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
        (_root_.OAI.CurrentFalconer.TreeND.treeCell Q) M (e.prefixPhasedRight z ξ) u.1 u.2
    have hu : Measurable U := hleft _ _ hleftm
    have hw : Measurable W := hleft _ _ hrightm
    have hbu : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ B := fun r =>
      Filter.Eventually.of_forall (fun w => (hb P ξ r w).1)
    have hbw : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖ ≤ B := fun r =>
      Filter.Eventually.of_forall (fun w => (hb Q ξ r w).2)
    have hi := _root_.OAI.Attempt4Near.graph_weighted_moments_integrableND μ hu hw hbu hbw hΨ
    change A*(∫ r, Ψ (r/(2:ℝ)^v)*_root_.OAI.Attempt4Near.sourceAngularMomentND μ U r*
      _root_.OAI.Attempt4Near.sourceAngularMomentND μ W r) ≤ C
    apply mul_le_mul_of_nonneg_left _ hA
    rw [← integral_mul_const]
    apply integral_mono hi (hΨ.mul_const _)
    intro r
    dsimp only
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [pow_two] using mul_le_mul
          (_root_.OAI.Attempt4Near.sourceAngularMomentND_bound μ U r (hbu r))
          (_root_.OAI.Attempt4Near.sourceAngularMomentND_bound μ W r (hbw r))
          (_root_.OAI.Attempt4Near.sourceAngularMomentND_nonneg μ W r) (by positivity)) (hpos _)
  unfold prefixGraphChildMax _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax
  split
  · apply Finset.sup'_le
    intro PQ _
    exact hchild PQ.1 PQ.2
  · exact hC

lemma prefixHighChildValues_bddAbove [IsProbabilityMeasure e.ρ]
    (Order : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hpos : ∀ r, 0 ≤ Ψ r) :
    BddAbove (e.prefixHighChildValues Order v Ψ) := by
  classical
  have h := fun z : PrefixAssignment n => e.prefixGraphChildMax_global_bound v Ψ hΨ hpos z
  choose C hC hbound using h
  let S : Finset (PrefixAssignment n) := (Finset.range (Order+1)).biUnion fun j =>
    (Attempt4PrefixShell.inverseAngularTermsND j
      (e.prefixDescriptors.disjSum e.prefixDescriptors)).toFinset
  refine ⟨∑ z ∈ S, C z,?_⟩
  intro r hr
  rcases hr with hr | ⟨j,hj,z,hz,ξ,rfl⟩
  · subst r
    exact Finset.sum_nonneg (fun z _ => hC z)
  · have hzS : z ∈ S := Finset.mem_biUnion.mpr
      ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),List.mem_toFinset.mpr hz⟩
    exact (hbound z ξ).trans (Finset.single_le_sum (fun z _ => hC z) hzS)

lemma prefixHighChildSup_nonneg [IsProbabilityMeasure e.ρ]
    (Order : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hpos : ∀ r, 0 ≤ Ψ r) :
    0 ≤ e.prefixHighChildSup Order v Ψ :=
  le_csSup (e.prefixHighChildValues_bddAbove Order v Ψ hΨ hpos) (Set.mem_insert _ _)

lemma prefixGraphChildMax_le_sup [IsProbabilityMeasure e.ρ]
    (Order : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hpos : ∀ r, 0 ≤ Ψ r)
    {j : ℕ} (hj : j ≤ Order) {z : PrefixAssignment n}
    (hz : z ∈ Attempt4PrefixShell.inverseAngularTermsND j
      (e.prefixDescriptors.disjSum e.prefixDescriptors)) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixGraphChildMax v Ψ z ξ ≤ e.prefixHighChildSup Order v Ψ :=
  le_csSup (e.prefixHighChildValues_bddAbove Order v Ψ hΨ hpos)
    (Set.mem_insert_of_mem _ ⟨j,hj,z,hz,ξ,rfl⟩)

end PositiveDistanceState
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
