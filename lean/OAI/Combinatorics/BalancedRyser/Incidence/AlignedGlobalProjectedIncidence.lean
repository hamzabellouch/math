import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalCurrentTuple
import OAI.Combinatorics.BalancedRyser.Local.AlignedHistoryKernel
import OAI.Combinatorics.BalancedRyser.Local.AlignedProjectedMean

namespace OAI

namespace Balanced.Local.AlignedGlobal
open RootChildPartition PartialAlignment TokenExposure InjectionExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev ProjectionData (P : EqualityPattern b κ) (R S : Finset (Fin b)) :=
  (FreeIndex P R → F) × PrefixData F P S

def projectionOffsets (P : EqualityPattern b κ) (R S : Finset (Fin b))
    (i : Fin b) (z : ProjectionData (F := F) P R S) (j : Fin 4) (s : Bool) : F :=
  if h : P.classOf i j ∈ S.biUnion P.classSet then (z.2.2 ⟨P.classOf i j,h⟩ s).2 else 0

def projectionFree (P : EqualityPattern b κ) (R S : Finset (Fin b))
    (i : Fin b) (z : ProjectionData (F := F) P R S)
    (j : {j : Fin 4 // j ∈ freePositions (currentOldIndices P R i)}) : F :=
  z.1 (currentFreeIndex P R i j)

def projectionObservation (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (x : FreeIndex P R → F) : ProjectionData (F := F) P R S :=
  let a := tokenInjectionEquiv F b κ e
  (x,prefixObservation P S a.1 bits
    (generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p x))

theorem projection_point_eq (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (x : FreeIndex P R → F) (j : Fin 4) :
    pointOutput P bits p i (currentOldIndices P R i) hJ
      (projectionOffsets P R S i) (projectionFree P R S i) e
      (projectionObservation P hκ R S hD bits p e x) j =
    prescribedPoint P (tokenInjectionEquiv F b κ e).1 bits
      (generatedZero P hκ R hD (tokenInjectionEquiv F b κ e).1
        (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p x) (i,j) := by
  apply pointOutput_eq_global P hκ R hD bits p e i hJ (x,fun _ _ => 0)
  · intro k hk
    funext s
    simp only [projectionOffsets, hOld k hk, dite_true, projectionObservation,
      prefixObservation, constituent, generatedZero, tokenInjectionEquiv]
    rfl
  · rfl

variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem projection_joint_law (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) :
    (PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) × (FreeIndex P R → F))).map
      (fun ex => (ex.1,projectionObservation P hκ R S hD bits p ex.1 ex.2)) =
    (PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (prefixNoise P hκ R S hD bits p e).map (fun z => (e,z))) := by
  rw [UniformConditionalProduct.uniform_product_eq_bind, PMF.map_bind]
  congr 1
  funext e
  simp only [prefixNoise, PMF.map_comp]
  rfl

theorem global_projected_left_probability_le_two_div
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hj : j ∈ currentOldIndices P R i)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (m : ProjectionData (F := F) P R S → Line F)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) × (FreeIndex P R → F))).toOuterMeasure
      {ex | let a := tokenInjectionEquiv F b κ ex.1
            let M := generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p ex.2
            let z := projectionObservation P hκ R S hD bits p ex.1 ex.2
            constituent M (ex.1 (Sum.inr (P.classOf i j))) (bits i j) ≠ m z ∧
              prescribedPoint P a.1 bits M (i,j) ≠ p ∧
              OnLine (prescribedPoint P a.1 bits M (i,j)) (m z)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  have h := original_projected_left_probability_le_two_div P bits p i
    (currentOldIndices P R i) hJ j hj K htarget (hKg _ (hOld j hj))
    (prefixNoise P hκ R S hD bits p)
    (prefixNoise_dependsOnExposed P hκ R S hD hS bits p K hKt hKg)
    (projectionOffsets P R S i) (projectionFree P R S i) m hK hb
  rw [← projection_joint_law P hκ R S hD bits p, PMF.toOuterMeasure_map_apply] at h
  convert h using 1
  congr 2
  ext ex
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, projection_point_eq P hκ R S hD bits p ex.1 i hJ hOld ex.2 j]
  simp only [projectionOffsets, hOld j hj, dite_true, projectionObservation,
    prefixObservation, tupleDirections, constituent, tokenInjectionEquiv]
  rfl

theorem global_projected_right_probability_le_two_div
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hj : j+1 ∈ currentOldIndices P R i)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (m : ProjectionData (F := F) P R S → Line F)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) × (FreeIndex P R → F))).toOuterMeasure
      {ex | let a := tokenInjectionEquiv F b κ ex.1
            let M := generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p ex.2
            let z := projectionObservation P hκ R S hD bits p ex.1 ex.2
            constituent M (ex.1 (Sum.inr (P.classOf i (j+1)))) (!(bits i (j+1))) ≠ m z ∧
              prescribedPoint P a.1 bits M (i,j) ≠ p ∧
              OnLine (prescribedPoint P a.1 bits M (i,j)) (m z)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  have h := original_projected_right_probability_le_two_div P bits p i
    (currentOldIndices P R i) hJ j hj K htarget (hKg _ (hOld (j+1) hj))
    (prefixNoise P hκ R S hD bits p)
    (prefixNoise_dependsOnExposed P hκ R S hD hS bits p K hKt hKg)
    (projectionOffsets P R S i) (projectionFree P R S i) m hK hb
  rw [← projection_joint_law P hκ R S hD bits p, PMF.toOuterMeasure_map_apply] at h
  convert h using 1
  congr 2
  ext ex
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, projection_point_eq P hκ R S hD bits p ex.1 i hJ hOld ex.2 j]
  simp only [projectionOffsets, hOld (j+1) hj, dite_true, projectionObservation,
    prefixObservation, tupleDirections, constituent, tokenInjectionEquiv]
  rfl

end
end Balanced.Local.AlignedGlobal

end OAI
