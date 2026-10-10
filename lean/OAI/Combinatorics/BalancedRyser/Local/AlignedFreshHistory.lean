import OAI.Combinatorics.BalancedRyser.Local.AlignedFreshCoordinate
import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalHistory
import OAI.Combinatorics.BalancedRyser.Local.AlignedUsedTestTransport

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedGlobal RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem conditioned_fresh_usedTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool) :
    conditionedOffsetProbability (Aligned P a bits p)
      (usedConstituentTest P a bits p c v.1 s) ≤ 1 / (Fintype.card F : ℝ) := by
  let M := generatedZero P hκ R hD a ha bits p
  let l : (FreeIndex P R → F) → Line F := fun x => constituent (M x) (a.2 c) s
  have hl : ∀ x t, l (Function.update x v t) = l x := by
    intro x t
    have h := (generated_history_update P hκ R S hD hS a ha bits p x
      (fun _ _ => 0) v hv t).2 c hc
    change M x (a.2 c) = M (Function.update x v t) (a.2 c) at h
    change (a.2 c, M (Function.update x v t) (a.2 c) s) = (a.2 c, M x (a.2 c) s)
    rw [← h]
  have hb := generatedZero_fresh_incidence_le P hκ R hD a ha bits p v l hl
  apply (conditioned_usedTest_le_uniform_free P hκ R hD a ha bits p c v.1 s).trans
  apply le_trans _ hb
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply (PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure.mono
    intro x hx
    exact ⟨(hx.1.2.2.2 v.1.1 c s).symm, hx.2.2⟩

theorem conditioned_fresh_collinearTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (i j : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S) :
    conditionedOffsetProbability (Aligned P a bits p)
      (collinearTest P a bits p i j v.1) ≤ 1 / (Fintype.card F : ℝ) := by
  let M := generatedZero P hκ R hD a ha bits p
  let l : (FreeIndex P R → F) → Line F := fun x =>
    joiningLine (prescribedPoint P a bits (M x) i) (prescribedPoint P a bits (M x) j)
  have hl : ∀ x t, l (Function.update x v t) = l x := by
    intro x t
    have h := (generated_history_update P hκ R S hD hS a ha bits p x
      (fun _ _ => 0) v hv t).1
    have hi' := h i.1 hi i.2
    have hj' := h j.1 hj j.2
    change prescribedPoint P a bits (M x) i =
      prescribedPoint P a bits (M (Function.update x v t)) i at hi'
    change prescribedPoint P a bits (M x) j =
      prescribedPoint P a bits (M (Function.update x v t)) j at hj'
    exact congrArg₂ joiningLine hi'.symm hj'.symm
  have hb := generatedZero_fresh_incidence_le P hκ R hD a ha bits p v l hl
  apply (conditioned_collinearTest_le_uniform_free P hκ R hD a ha bits p i j v.1).trans
  apply le_trans _ hb
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply (PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure.mono
    intro x hx
    obtain ⟨hA, hij, hiv, hjv, hxy, hxv, hyv, hhit, htarget, hconst⟩ := hx
    exact ⟨htarget v.1.1, hhit⟩

end
end Balanced.Local.UsedEventUnion

end OAI
