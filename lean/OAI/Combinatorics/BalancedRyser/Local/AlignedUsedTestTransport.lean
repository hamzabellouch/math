import OAI.Combinatorics.BalancedRyser.Local.AlignedUsedObservable
import OAI.Combinatorics.BalancedRyser.Local.LocalUsedEventUnion

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedUnused AlignedGlobal RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def usedGeometricGuards (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  Aligned P a bits p M ∧ Function.Injective (prescribedPoint P a bits M) ∧
    (∀ ij, prescribedPoint P a bits M ij ≠ p) ∧
    (∀ i c s, lineThrough (a.1 i) p ≠ constituent M (a.2 c) s)

theorem admissible_usedGeometricGuards (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (h : Admissible P a bits p M) :
    usedGeometricGuards P a bits p M := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro i c s heq
  apply h.2.2.2.1 i
  rw [heq]
  exact Finset.mem_image.mpr ⟨(a.2 c,s), Finset.mem_univ _, rfl⟩

omit [Fintype F] in
theorem usedGeometricGuards_agree (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M N : MergedPairs F)
    (hMN : ∀ d ∈ usedDirections P a, M d = N d) :
    usedGeometricGuards P a bits p M ↔ usedGeometricGuards P a bits p N := by
  have hp : prescribedPoint P a bits M = prescribedPoint P a bits N := by
    funext ij
    exact UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement (P := P) (bits := bits) M N hMN ij
  have hc (c : Fin (4*b-κ)) : M (a.2 c) = N (a.2 c) :=
    hMN _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  simp only [usedGeometricGuards, Aligned, hp, constituent, hc]

def geometricUsedTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (M : MergedPairs F) : Prop :=
  usedGeometricGuards P a bits p M ∧ (∀ j, P.classOf ij.1 j ≠ c) ∧
    OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s)

def geometricCollinearTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M : MergedPairs F) : Prop :=
  usedGeometricGuards P a bits p M ∧
    i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
    prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
    OnLine (prescribedPoint P a bits M k)
      (joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j)) ∧
    (∀ t, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      lineThrough (a.1 t) p) ∧
    (∀ c s, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      constituent M (a.2 c) s)

theorem usedConstituentTest_implies_geometric (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) (M : MergedPairs F)
    (h : usedConstituentTest P a bits p c ij s M) :
    geometricUsedTest P a bits p c ij s M :=
  ⟨admissible_usedGeometricGuards P a bits p M h.1, h.2⟩

theorem collinearTest_implies_geometric (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M : MergedPairs F)
    (h : collinearTest P a bits p i j k M) :
    geometricCollinearTest P a bits p i j k M :=
  ⟨admissible_usedGeometricGuards P a bits p M h.1, h.2⟩

omit [Fintype F] in
theorem geometricUsedTest_agree (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (M N : MergedPairs F) (hMN : ∀ d ∈ usedDirections P a, M d = N d) :
    geometricUsedTest P a bits p c ij s M ↔ geometricUsedTest P a bits p c ij s N := by
  have hp := UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement (P := P) (bits := bits) M N hMN ij
  have hc := hMN _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  simp only [geometricUsedTest, usedGeometricGuards_agree P a bits p M N hMN,
    hp, constituent, hc]

omit [Fintype F] in
theorem geometricCollinearTest_agree (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M N : MergedPairs F)
    (hMN : ∀ d ∈ usedDirections P a, M d = N d) :
    geometricCollinearTest P a bits p i j k M ↔
      geometricCollinearTest P a bits p i j k N := by
  have hp := UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement (P := P) (bits := bits) M N hMN
  have hc (c : Fin (4*b-κ)) : M (a.2 c) = N (a.2 c) :=
    hMN _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  simp only [geometricCollinearTest, usedGeometricGuards_agree P a bits p M N hMN,
    hp, constituent, hc]

theorem conditioned_usedTest_le_uniform_free (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) :
    conditionedOffsetProbability (Aligned P a bits p)
      (usedConstituentTest P a bits p c ij s) ≤
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | geometricUsedTest P a bits p c ij s
          (generatedZero P hκ R hD a ha bits p x)}).toReal := by
  exact (UnusedOffsetProbability.conditionedOffsetProbability_mono (Aligned P a bits p)
    (usedConstituentTest_implies_geometric P a bits p c ij s)).trans_eq
      (conditioned_probability_eq_uniform_free P hκ R hD a ha bits p _
        (geometricUsedTest_agree P a bits p c ij s))

theorem conditioned_collinearTest_le_uniform_free (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (i j k : Fin b × Fin 4) :
    conditionedOffsetProbability (Aligned P a bits p)
      (collinearTest P a bits p i j k) ≤
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | geometricCollinearTest P a bits p i j k
          (generatedZero P hκ R hD a ha bits p x)}).toReal := by
  exact (UnusedOffsetProbability.conditionedOffsetProbability_mono (Aligned P a bits p)
    (collinearTest_implies_geometric P a bits p i j k)).trans_eq
      (conditioned_probability_eq_uniform_free P hκ R hD a ha bits p _
        (geometricCollinearTest_agree P a bits p i j k))

end
end Balanced.Local.UsedEventUnion

end OAI
