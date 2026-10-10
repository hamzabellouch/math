import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularWordOperatorBound

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical
variable {d : ℕ}
noncomputable def actualDescriptorSmooth (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (P : CellPath d) (b : PolicyDescriptor) :
    SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  ⟨fun w => (actualDescriptorMask ρ m N sig C J i P b w : ℂ),
    Complex.ofRealCLM.contDiff.comp (actualDescriptorMask_smooth ρ m N sig C J i P b)⟩

lemma actualEndpointSmooth_of_mem (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    {P : CellPath d} (hP : P ∈ dyadicPaths (descriptorAnchor b))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell P) :
    actualEndpointSmooth ρ m N sig C J i b x=actualDescriptorSmooth ρ m N sig C J i P b := by
  apply Subtype.ext
  funext w
  exact congrArg Complex.ofReal (congrFun (actualEndpointMask_of_mem ρ m N sig C J i b hP hx) w)

lemma actualEndpointSmooth_of_absent (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : ∀ P ∈ dyadicPaths (descriptorAnchor b), x ∉ treeCell P) :
    actualEndpointSmooth ρ m N sig C J i b x=0 := by
  apply Subtype.ext
  funext w
  change (actualEndpointMask ρ m N sig C J i b x w : ℂ)=0
  rw [actualEndpointMask_of_absent ρ m N sig C J i b hx]
  rfl

lemma actualEndpointAngular_partition
    (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : EuclideanSpace ℝ (Fin d)) :
    actualEndpointAngular L ρ m N sig C J i b x=
      ∑ P ∈ dyadicPaths (descriptorAnchor b),
        if x ∈ treeCell P then
          normalizedAngularWordND (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig) L
            (actualDescriptorSmooth ρ m N sig C J i P b) else 0 := by
  classical
  by_cases hx : ∃ P ∈ dyadicPaths (descriptorAnchor b), x ∈ treeCell P
  · obtain ⟨P,hP,hx⟩ := hx
    unfold actualEndpointAngular
    rw [actualEndpointSmooth_of_mem ρ m N sig C J i b hP hx,Finset.sum_eq_single P]
    · simp only [hx,ite_true]
    · intro Q hQ hQP
      have hnot : x ∉ treeCell Q := fun hxQ =>
        Set.disjoint_left.mp (treeCell_disjoint
          (((mem_dyadicPaths _ _).mp hQ).trans ((mem_dyadicPaths _ _).mp hP).symm) hQP) hxQ hx
      simp only [hnot,ite_false]
    · exact fun h => (h hP).elim
  · have hx' : ∀ P ∈ dyadicPaths (descriptorAnchor b), x ∉ treeCell P := by
      simpa only [not_exists,not_and] using hx
    unfold actualEndpointAngular normalizedAngularWordND
    rw [actualEndpointSmooth_of_absent ρ m N sig C J i b hx',map_zero,smul_zero]
    exact (Finset.sum_eq_zero fun P hP => ite_eq_right (hx' P hP)).symm

lemma actualEndpointAngular_measurable
    (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (actualEndpointAngular L ρ m N sig C J i b z.1).1 z.2) := by
  classical
  have he : (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (actualEndpointAngular L ρ m N sig C J i b z.1).1 z.2)=
      fun z => ∑ P ∈ dyadicPaths (descriptorAnchor b), if z.1 ∈ treeCell P then
        (normalizedAngularWordND (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig) L
          (actualDescriptorSmooth ρ m N sig C J i P b)).1 z.2 else 0 := by
    funext z
    rw [actualEndpointAngular_partition]
    simp only [Submodule.coe_sum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro P _hP
    split_ifs <;> rfl
  rw [he]
  apply Finset.measurable_sum
  intro P _hP
  exact Measurable.ite ((measurableSet_treeCell P).preimage measurable_fst)
    ((smoothFunctionND_contDiff _).continuous.measurable.comp measurable_snd) measurable_const

lemma actualEndpointSmooth_even (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x : EuclideanSpace ℝ (Fin d)) : Function.Even (actualEndpointSmooth ρ m N sig C J i b x).1 := by
  classical
  intro w
  change (actualEndpointMask ρ m N sig C J i b x (-w):ℂ)=_
  unfold actualEndpointMask
  congr 1
  apply Finset.sum_congr rfl
  intro P _hP
  split_ifs
  · exact actualDescriptorMask_even ρ m N sig C J i P b w
  · rfl

lemma actualEndpointAngular_even
    (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : EuclideanSpace ℝ (Fin d)) :
    Function.Even (actualEndpointAngular L ρ m N sig C J i b x).1 :=
  normalizedAngularWordND_even _ L _ (actualEndpointSmooth_even ρ m N sig C J i b x)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
