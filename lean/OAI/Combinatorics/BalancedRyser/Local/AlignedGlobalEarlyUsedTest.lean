import OAI.Combinatorics.BalancedRyser.Incidence.AlignedGlobalProjectedIncidence
import OAI.Combinatorics.BalancedRyser.Local.LocalInjectionFreeLaw

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition UsedEventUnion
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in

theorem geometricUsedTest_constituent_ne
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (e : DirectionToken b κ ↪ Direction F) (M : MergedPairs F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (h : geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p c ij s M)
    (j : Fin 4) (t : Bool) :
    constituent M (e (Sum.inr (P.classOf ij.1 j))) t ≠
      constituent M ((tokenInjectionEquiv F b κ e).1.2 c) s := by
  intro heq
  have hd : e (Sum.inr (P.classOf ij.1 j)) = e (Sum.inr c) :=
    congrArg Prod.fst heq
  exact h.2.1 j (Sum.inr.inj (e.injective hd))

variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem geometricUsedTest_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hdep : (i,j) ∈ dependentOccurrences P R)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionFreeProbability P R (fun e x =>
      geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p c (i,j) s
        (injectedGenerated P hκ R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ) := by
  let m : ProjectionData (F := F) P R S → Line F := fun z => z.2.2 ⟨c,hc⟩ s
  have hdep' := (mem_dependentOccurrences P R (i,j)).mp hdep
  rcases hdep'.2 with hl | hr
  · have hj : j ∈ currentOldIndices P R i := by
      simp only [currentOldIndices, ite_eq_right hdep'.1, rootGeneratorIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hl
    have hbound := global_projected_left_probability_le_two_div P hκ R S hD hS
      bits p i hJ hOld j hj K hKt hKg htarget m hK hb
    apply le_trans _ hbound
    unfold injectionFreeProbability
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _
    · apply (PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
        (FreeIndex P R → F))).toOuterMeasure.mono
      intro ex hx
      change geometricUsedTest P (tokenInjectionEquiv F b κ ex.1).1 bits p c (i,j) s
        (injectedGenerated P hκ R hD bits p ex.1 ex.2) at hx
      exact ⟨geometricUsedTest_constituent_ne P bits p ex.1 _ c (i,j) s hx j (bits i j),
        hx.1.2.2.1 (i,j), hx.2.2⟩
  · have hj : j+1 ∈ currentOldIndices P R i := by
      simp only [currentOldIndices, ite_eq_right hdep'.1, rootGeneratorIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hr
    have hbound := global_projected_right_probability_le_two_div P hκ R S hD hS
      bits p i hJ hOld j hj K hKt hKg htarget m hK hb
    apply le_trans _ hbound
    unfold injectionFreeProbability
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _
    · apply (PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
        (FreeIndex P R → F))).toOuterMeasure.mono
      intro ex hx
      change geometricUsedTest P (tokenInjectionEquiv F b κ ex.1).1 bits p c (i,j) s
        (injectedGenerated P hκ R hD bits p ex.1 ex.2) at hx
      exact ⟨geometricUsedTest_constituent_ne P bits p ex.1 _ c (i,j) s hx
          (j+1) (!(bits i (j+1))), hx.1.2.2.1 (i,j), hx.2.2⟩

theorem usedTest_injectionAverage_projected_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (i : Fin b) (hJ : (currentOldIndices P R i).card ≤ 1)
    (hOld : ∀ j ∈ currentOldIndices P R i, P.classOf i j ∈ S.biUnion P.classSet)
    (j : Fin 4) (hdep : (i,j) ∈ dependentOccurrences P R)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (htarget : Sum.inl i ∉ K)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c (i,j) s) ≤
      2 / (Fintype.card F : ℝ) :=
  (usedTest_injectionAverage_le_free P hκ R hD bits p c (i,j) s).trans
    (geometricUsedTest_projected_le P hκ R S hD hS bits p i hJ hOld j hdep
      K hKt hKg htarget c hc s hK hb)

end
end Balanced.Local.AlignedGlobal

end OAI
