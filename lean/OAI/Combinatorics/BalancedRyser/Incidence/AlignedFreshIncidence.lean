import OAI.Combinatorics.BalancedRyser.Incidence.UnusedOffsetIncidence
import OAI.Combinatorics.BalancedRyser.Local.AlignedPointExposure
import OAI.Combinatorics.BalancedRyser.Local.LocalFiberBounds

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem generatedPointLaw_free_marginal (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (i : {i : Fin 4 // i ∈ freePositions J}) :
    (generatedPointLaw d hd σ g hg c J hJ a).map (fun y => y i.1) =
      (PMF.uniformOfFintype F).map (fun t => ((linePointEquiv g c).symm t).1) := by
  unfold generatedPointLaw
  rw [PMF.map_comp]
  have hf : (fun x => generatedPositions d hd σ g hg c J hJ a x i.1) =
      (fun x => ((linePointEquiv g c).symm (x i)).1) := by
    funext x
    exact generatedPositions_free d hd σ g hg c J hJ a x i
  change (PMF.uniformOfFintype ({j : Fin 4 // j ∈ freePositions J} → F)).map
    (fun x => generatedPositions d hd σ g hg c J hJ a x i.1) = _
  rw [hf]
  have h := congrArg (fun μ : PMF F =>
      μ.map (fun t => ((linePointEquiv g c).symm t).1))
    (UnusedOffsetIncidence.uniform_map_eval (A := F) i)
  simpa only [PMF.map_comp, Function.comp_def] using h

theorem generatedPointLaw_fresh_incidence_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (i : {i : Fin 4 // i ∈ freePositions J}) (l : Line F) :
    ((generatedPointLaw d hd σ g hg c J hJ a).toOuterMeasure
      {y | l ≠ (g,c) ∧ OnLine (y i.1) l}).toReal ≤
      1 / (Fintype.card F : ℝ) := by
  let f : F → Point F := fun t => ((linePointEquiv g c).symm t).1
  have hf : Function.Injective f := by
    intro t u h
    exact (linePointEquiv g c).symm.injective (Subtype.ext h)
  have hp : ∀ t, OnLine (f t) (g,c) := fun t => ((linePointEquiv g c).symm t).2
  have hb := LocalFiberBounds.nonTarget_line_union_probability_le (g,c) {l} f hf hp
  have heq : ((generatedPointLaw d hd σ g hg c J hJ a).toOuterMeasure
      {y | l ≠ (g,c) ∧ OnLine (y i.1) l}).toReal =
      ((PMF.uniformOfFintype F).toOuterMeasure
        {t | l ≠ (g,c) ∧ OnLine (f t) l}).toReal := by
    have h := congrArg (fun μ : PMF (Point F) =>
      (μ.toOuterMeasure {z | l ≠ (g,c) ∧ OnLine z l}).toReal)
      (generatedPointLaw_free_marginal d hd σ g hg c J hJ a i)
    simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, f] using h
  rw [heq]
  simpa only [Finset.mem_singleton, exists_eq_left, Finset.card_singleton,
    Nat.cast_one] using hb

end
end Balanced.AlignedListProbability

end OAI
