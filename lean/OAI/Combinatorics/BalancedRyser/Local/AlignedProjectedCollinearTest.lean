import OAI.Combinatorics.BalancedRyser.Incidence.AlignedGlobalProjectedIncidence
import OAI.Combinatorics.BalancedRyser.Local.LocalInjectionFreeLaw

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition UsedEventUnion
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem dependent_currentOld_cases (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (k : Fin b × Fin 4)
    (hk : k ∈ dependentOccurrences P R) :
    k.2 ∈ currentOldIndices P R k.1 ∨
      k.2 + 1 ∈ currentOldIndices P R k.1 := by
  rcases (mem_dependentOccurrences P R k).mp hk with ⟨hn, hl | hr⟩
  · exact Or.inl (by simpa [currentOldIndices, hn, rootGeneratorIndices] using hl)
  · exact Or.inr (by simpa [currentOldIndices, hn, rootGeneratorIndices] using hr)

theorem geometricCollinearTest_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S)
    (hdep : k ∈ dependentOccurrences P R)
    (hJ : (currentOldIndices P R k.1).card ≤ 1)
    (hOld : ∀ t ∈ currentOldIndices P R k.1,
      P.classOf k.1 t ∈ S.biUnion P.classSet)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl k.1 ∉ K)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F)
    [Nonempty (DirectionToken b κ ↪ Direction F)] :
    injectionFreeProbability P R (fun e x =>
      geometricCollinearTest P (tokenInjectionEquiv F b κ e).1 bits p i j k
        (injectedGenerated P hκ R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ) := by
  let m : ProjectionData (F := F) P R S → Line F := fun z =>
    joiningLine (z.2.1 ⟨i.1,hi⟩ i.2) (z.2.1 ⟨j.1,hj⟩ j.2)
  have hmono (c : Fin (4*b-κ)) (s : Bool) :
      injectionFreeProbability P R (fun e x =>
        geometricCollinearTest P (tokenInjectionEquiv F b κ e).1 bits p i j k
          (injectedGenerated P hκ R hD bits p e x)) ≤
      ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
          (FreeIndex P R → F))).toOuterMeasure
        {ex | let a := tokenInjectionEquiv F b κ ex.1
              let M := generatedZero P hκ R hD a.1
                (allTokensDistinct_eligible P a.1 a.2) bits p ex.2
              let z := projectionObservation P hκ R S hD bits p ex.1 ex.2
              constituent M (ex.1 (Sum.inr c)) s ≠ m z ∧
                prescribedPoint P a.1 bits M k ≠ p ∧
                OnLine (prescribedPoint P a.1 bits M k) (m z)}).toReal := by
    unfold injectionFreeProbability
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _
    · apply (PMF.uniformOfFintype _).toOuterMeasure.mono
      intro ex hex
      rcases hex with ⟨hg, hij, hik, hjk, hxy, hxz, hyz, hinc, ht, hu⟩
      refine ⟨?_, hg.2.2.1 k, ?_⟩
      · exact (hu c s).symm
      · exact hinc
  rcases dependent_currentOld_cases P R k hdep with hl | hr
  · exact (hmono (P.classOf k.1 k.2) (bits k.1 k.2)).trans
      (global_projected_left_probability_le_two_div P hκ R S hD hS bits p
        k.1 hJ hOld k.2 hl K hKt hKg htarget m hK hb)
  · exact (hmono (P.classOf k.1 (k.2+1)) (!(bits k.1 (k.2+1)))).trans
      (global_projected_right_probability_le_two_div P hκ R S hD hS bits p
        k.1 hJ hOld k.2 hr K hKt hKg htarget m hK hb)

theorem collinearTest_injectionAverage_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S)
    (hdep : k ∈ dependentOccurrences P R)
    (hJ : (currentOldIndices P R k.1).card ≤ 1)
    (hOld : ∀ t ∈ currentOldIndices P R k.1,
      P.classOf k.1 t ∈ S.biUnion P.classSet)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl k.1 ∉ K)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F)
    [Nonempty (DirectionToken b κ ↪ Direction F)] :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      2 / (Fintype.card F : ℝ) :=
  (collinearTest_injectionAverage_le_free P hκ R hD bits p i j k).trans
    (geometricCollinearTest_projected_le P hκ R S hD hS bits p i j k hi hj
      hdep hJ hOld K hKt hKg htarget hK hb)

end
end Balanced.Local.AlignedGlobal

end OAI
