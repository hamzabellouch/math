import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalProduct
import OAI.Combinatorics.BalancedRyser.Local.LocalUnusedOffsetProbability

namespace OAI

namespace Balanced.Local.AlignedGlobal

open AlignedUnused TupleAlignment RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def refreshUnused (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (M : MergedPairs F) (u : UnusedArray P a) : MergedPairs F :=
  (split P a).symm ((split P a M).1, u)

omit [Field F] [Fintype F] in
theorem refreshUnused_used (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (M : MergedPairs F) (u : UnusedArray P a)
    (d : Direction F) (hd : d ∈ usedDirections P a) :
    refreshUnused P a M u d = M d := by
  exact congrFun (congrArg Prod.fst
    ((split P a).apply_symm_apply ((split P a M).1, u))) ⟨d, hd⟩

omit [Field F] [Fintype F] in
theorem refreshUnused_unused (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (M : MergedPairs F) (u : UnusedArray P a)
    (d : {d : Direction F // d ∉ usedDirections P a}) :
    refreshUnused P a M u d.1 = u d := by
  exact congrFun (congrArg Prod.snd
    ((split P a).apply_symm_apply ((split P a M).1, u))) d

def refreshAligned (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : AlignedOffsets P a bits p)
    (u : UnusedArray P a) : AlignedOffsets P a bits p :=
  ⟨refreshUnused P a M.1 u,
    (aligned_agree P a bits p M.1 (refreshUnused P a M.1 u)
      (fun d hd => (refreshUnused_used P a M.1 u d hd).symm)).mp M.2⟩

omit [Fintype F] in
theorem coordinates_refreshAligned (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : AlignedOffsets P a bits p)
    (u : UnusedArray P a) :
    coordinates P R a bits p (refreshAligned P a bits p M u) =
      ((coordinates P R a bits p M).1, u) := by
  apply Prod.ext
  · funext ij
    apply congrArg (linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p))
    apply Subtype.ext
    exact UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement
      _ _ (refreshUnused_used P a M.1 u) ij.1
  · funext d
    exact refreshUnused_unused P a M.1 u d

theorem generated_refresh (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u v : UnusedArray P a) :
    refreshAligned P a bits p
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)) v =
      (coordinateEquiv P hκ R hD a ha bits p).symm (x,v) := by
  apply (coordinateEquiv P hκ R hD a ha bits p).injective
  rw [coordinateEquiv_apply, coordinates_refreshAligned]
  change ((coordinateEquiv P hκ R hD a ha bits p
    ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u))).1, v) = _
  simp only [Equiv.apply_symm_apply]

theorem generated_used_agree (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u v : UnusedArray P a) (d : Direction F) (hd : d ∈ usedDirections P a) :
    ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)).1 d =
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,v)).1 d := by
  rw [← generated_refresh P hκ R hD a ha bits p x u v]
  exact (refreshUnused_used P a _ v d hd).symm

def generatedZero (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F) : MergedPairs F :=
  ((coordinateEquiv P hκ R hD a ha bits p).symm (x, fun _ _ => 0)).1

theorem alignedLaw_map_used {O : Type*}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (obs : MergedPairs F → O)
    (hobs : ∀ M N, (∀ d ∈ usedDirections P a, M d = N d) → obs M = obs N) :
    (alignedLaw P hκ a ha bits p).map obs =
      (PMF.uniformOfFintype (FreeIndex P R → F)).map
        (fun x => obs (generatedZero P hκ R hD a ha bits p x)) := by
  rw [alignedLaw_eq_uniform_coordinates P hκ R hD a ha bits p, PMF.map_comp]
  have hf : (obs ∘ (fun z =>
      ((coordinateEquiv P hκ R hD a ha bits p).symm z).1)) =
      (fun x => obs (generatedZero P hκ R hD a ha bits p x)) ∘ Prod.fst := by
    funext z
    apply hobs
    intro d hd
    exact generated_used_agree P hκ R hD a ha bits p z.1 z.2 (fun _ _ => 0) d hd
  rw [hf, ← PMF.map_comp, uniform_map_fst]

theorem conditioned_probability_eq_uniform_free
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ usedDirections P a, M d = N d) → (E M ↔ E N)) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
        {x | E (generatedZero P hκ R hD a ha bits p x)}).toReal := by
  rw [conditioned_probability_eq_uniform_coordinates P hκ R hD a ha bits p E]
  have heq : {z | E ((coordinateEquiv P hκ R hD a ha bits p).symm z).1} =
      Prod.fst ⁻¹' {x | E (generatedZero P hκ R hD a ha bits p x)} := by
    ext z
    exact hE _ _ (generated_used_agree P hκ R hD a ha bits p z.1 z.2 (fun _ _ => 0))
  rw [heq]
  have hm := congrArg (fun μ : PMF (FreeIndex P R → F) =>
      (μ.toOuterMeasure {x | E (generatedZero P hκ R hD a ha bits p x)}).toReal)
    (uniform_map_fst (α := FreeIndex P R → F) (β := UnusedArray P a))
  simpa only [PMF.toOuterMeasure_map_apply] using hm

end
end Balanced.Local.AlignedGlobal

end OAI
