import OAI.Combinatorics.BalancedRyser.Incidence.AlignedGeneratorIncidence
import OAI.Combinatorics.BalancedRyser.Local.AlignedHistoryKernel
import OAI.Combinatorics.BalancedRyser.Local.InjectionExposureMixture
import OAI.Combinatorics.BalancedRyser.Local.LocalInjectionFreeLaw
import OAI.Combinatorics.BalancedRyser.Local.LocalPrescribedGeometry

namespace OAI

namespace Balanced.Local.AlignedGlobal
open RootChildPartition InjectionExposure TokenExposure UsedEventUnion
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in

theorem constituent_eq_purposeful_line (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (M : MergedPairs F) (i : Fin b) (j : Fin 4) (s : Bool) :
    constituent M (a.2 (P.classOf i j)) s =
      lineThrough (a.2 (P.classOf i j))
        (prescribedPoint P a bits M (i,purposefulIndex (bits i) j s)) := by
  apply line_eq_lineThrough
  unfold purposefulIndex
  split_ifs with hs
  · simpa only [hs] using PrescribedGeometry.prescribedPoint_on_left (M := M) ha i j
  · have hs' : s = !(bits i j) := by
      cases s <;> cases h : bits i j <;> simp_all
    have hj : j - 1 + 1 = j := by fin_cases j <;> decide
    simpa only [hj, hs'] using
      PrescribedGeometry.prescribedPoint_on_right (M := M) ha i (j-1)

variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem global_later_generator_probability_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F) (i : Fin b)
    (hphase : i ∈ R ∨ R ⊆ S)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (hi : Sum.inl i ∈ K) (j : Fin 4)
    (hnew : Sum.inr (P.classOf i j) ∉ K) (s : Bool)
    (r : {r : Fin b // r ∈ S}) (t : Fin 4)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionFreeProbability P R (fun e x =>
      let a := (tokenInjectionEquiv F b κ e).1
      let M := injectedGenerated P hκ R hD bits p e x
      prescribedPoint P a bits M (i,purposefulIndex (bits i) j s) ≠
        prescribedPoint P a bits M (r.1,t) ∧
      OnLine (prescribedPoint P a bits M (r.1,t))
        (constituent M (a.2 (P.classOf i j)) s)) ≤
      2 / (Fintype.card F : ℝ) := by
  let noise := currentNoise P hκ R S hD bits p i
  let endpoint := fun z : (FreeIndex P R → F) ×
      (PrefixData F P S × (Fin 4 → Point F)) =>
      z.2.2 (purposefulIndex (bits i) j s)
  let previous := fun z : (FreeIndex P R → F) ×
      (PrefixData F P S × (Fin 4 → Point F)) => z.2.1.1 r t
  let E : Set ((DirectionToken b κ ↪ Direction F) ×
      ((FreeIndex P R → F) × (PrefixData F P S × (Fin 4 → Point F)))) :=
    {ez | endpoint ez.2 ≠ previous ez.2 ∧
      OnLine (previous ez.2) (lineThrough (ez.1 (Sum.inr (P.classOf i j))) (endpoint ez.2))}
  have hbound : (((PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure E).toReal ≤
      2 / (Fintype.card F : ℝ) := by
    apply original_probability_le_of_auxiliary K noise E
    intro base
    exact (auxiliary_guarded_joining_probability_le K base
      (Sum.inr (P.classOf i j)) hnew noise
      (currentNoise_dependsOnExposed P hκ R S hD hS bits p i hphase K hKt hKg hi)
      endpoint previous).trans
      (inverse_remaining_le_two_div (Fintype.card F) K.card b Fintype.card_pos hK hb)
  have hevent : (fun e x =>
      let a := (tokenInjectionEquiv F b κ e).1
      let M := injectedGenerated P hκ R hD bits p e x
      prescribedPoint P a bits M (i,purposefulIndex (bits i) j s) ≠
        prescribedPoint P a bits M (r.1,t) ∧
      OnLine (prescribedPoint P a bits M (r.1,t))
        (constituent M (a.2 (P.classOf i j)) s)) =
    (fun e x =>
      let a := (tokenInjectionEquiv F b κ e).1
      let M := injectedGenerated P hκ R hD bits p e x
      prescribedPoint P a bits M (i,purposefulIndex (bits i) j s) ≠
        prescribedPoint P a bits M (r.1,t) ∧
      OnLine (prescribedPoint P a bits M (r.1,t))
        (lineThrough (e (Sum.inr (P.classOf i j)))
          (prescribedPoint P a bits M (i,purposefulIndex (bits i) j s)))) := by
    funext e x
    dsimp only
    rw [constituent_eq_purposeful_line P _
      (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2)]
    rfl
  rw [hevent]
  unfold injectionFreeProbability
  rw [UniformConditionalProduct.uniform_product_eq_bind]
  simpa only [noise, currentNoise, E, endpoint, previous, PMF.map_comp,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    Set.preimage_ofPred_eq, prefixObservation, injectedGenerated, Function.comp_apply] using hbound

theorem geometricUsedTest_later_generator_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F) (i : Fin b)
    (hphase : i ∈ R ∨ R ⊆ S)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (hi : Sum.inl i ∈ K) (j : Fin 4)
    (hnew : Sum.inr (P.classOf i j) ∉ K) (s : Bool)
    (r : {r : Fin b // r ∈ S}) (t : Fin 4)
    (hK : K.card ≤ 5*b) (hb : 10*b ≤ Fintype.card F) :
    injectionFreeProbability P R (fun e x =>
      geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p
        (P.classOf i j) (r.1,t) s (injectedGenerated P hκ R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ) := by
  apply le_trans _ (global_later_generator_probability_le P hκ R S hD hS bits p i
    hphase K hKt hKg hi j hnew s r t hK hb)
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro ex hx
    refine ⟨?_, hx.1.2.2⟩
    intro heq
    have hip := hx.1.1.2.1 heq
    have hir : i = r.1 := congrArg Prod.fst hip
    exact hx.1.2.1 j (by simp only [hir])

end
end Balanced.Local.AlignedGlobal

end OAI
