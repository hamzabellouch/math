import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalHistory
import OAI.Combinatorics.BalancedRyser.Local.AlignedUsedObservable
import OAI.Combinatorics.BalancedRyser.Local.InjectionAuxiliaryExposure
import OAI.Combinatorics.BalancedRyser.Local.LocalDirectionAssignments

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition InjectionExposure
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev PrefixData (F : Type*) {b κ : ℕ} (P : EqualityPattern b κ)
    (S : Finset (Fin b)) :=
  ({i : Fin b // i ∈ S} → Fin 4 → Point F) ×
    ({c : Fin (4*b-κ) // c ∈ S.biUnion P.classSet} → Bool → Line F)

def prefixObservation (P : EqualityPattern b κ) (S : Finset (Fin b))
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    PrefixData F P S :=
  ((fun i j => prescribedPoint P a bits M (i.1,j)),
    fun c s => constituent M (a.2 c.1) s)

theorem generated_prefixObservation_eq (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    prefixObservation P S a bits (generatedZero P hκ R hD a ha bits p x) =
      prefixObservation P S a' bits (generatedZero P hκ R hD a' ha' bits p x) := by
  have h := generated_history_agree P hκ R S hD hS a a' ha ha' bits p x
    (fun _ _ => 0) (fun _ _ => 0) ht hd
  apply Prod.ext
  · funext i j
    exact h.1 i.1 i.2 j
  · funext c s
    apply Prod.ext
    · exact hd c.1 c.2
    · exact congrFun (h.2 c.1 c.2) s

def prefixNoise (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F) :
    PMF ((FreeIndex P R → F) × PrefixData F P S) :=
  let a := tokenInjectionEquiv F b κ e
  (PMF.uniformOfFintype (FreeIndex P R → F)).map fun x =>
    (x, prefixObservation P S a.1 bits
      (generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p x))

theorem prefixNoise_dependsOnExposed (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ i ∈ S, Sum.inl i ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K) :
    DependsOnExposed K (prefixNoise P hκ R S hD bits p) := by
  intro e f hef
  dsimp only [prefixNoise]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  apply generated_prefixObservation_eq P hκ R S hD hS
  · intro i hi
    exact hef _ (hKt i hi)
  · intro c hc
    exact hef _ (hKg c hc)

def currentNoise (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (i : Fin b)
    (e : DirectionToken b κ ↪ Direction F) :
    PMF ((FreeIndex P R → F) × (PrefixData F P S × (Fin 4 → Point F))) :=
  let a := tokenInjectionEquiv F b κ e
  (PMF.uniformOfFintype (FreeIndex P R → F)).map fun x =>
    let M := generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p x
    (x, prefixObservation P S a.1 bits M, fun j => prescribedPoint P a.1 bits M (i,j))

theorem currentNoise_dependsOnExposed (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F) (i : Fin b)
    (hphase : i ∈ R ∨ R ⊆ S)
    (K : Finset (DirectionToken b κ))
    (hKt : ∀ r ∈ S, Sum.inl r ∈ K)
    (hKg : ∀ c ∈ S.biUnion P.classSet, Sum.inr c ∈ K)
    (hi : Sum.inl i ∈ K) :
    DependsOnExposed K (currentNoise P hκ R S hD bits p i) := by
  intro e f hef
  let a := tokenInjectionEquiv F b κ e
  let a' := tokenInjectionEquiv F b κ f
  let ha := allTokensDistinct_eligible P a.1 a.2
  let ha' := allTokensDistinct_eligible P a'.1 a'.2
  have ht : ∀ r ∈ S, a.1.1 r = a'.1.1 r := fun r hr => hef _ (hKt r hr)
  have hd : ∀ c ∈ S.biUnion P.classSet, a.1.2 c = a'.1.2 c :=
    fun c hc => hef _ (hKg c hc)
  have hti : a.1.1 i = a'.1.1 i := hef _ hi
  dsimp only [currentNoise]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact generated_prefixObservation_eq P hκ R S hD hS a.1 a'.1 ha ha'
      bits p x ht hd
  · funext j
    rcases hphase with hir | hRS
    · apply free_point_eq_of_coordinate_eq P R a.1 a'.1 bits p
        ((coordinateEquiv P hκ R hD a.1 ha bits p).symm (x,fun _ _ => 0))
        ((coordinateEquiv P hκ R hD a'.1 ha' bits p).symm (x,fun _ _ => 0))
        (inverse_coordinates_fst_eq P hκ R hD a.1 a'.1 ha ha' bits p x
          (fun _ _ => 0) (fun _ _ => 0)) ⟨(i,j), ?_⟩ hti
      simp only [mem_dependentOccurrences, not_and]
      exact fun hn => (hn hir).elim
    · apply generated_point_eq_of_root_history P hκ R hD a.1 a'.1 ha ha'
        bits p x (fun _ _ => 0) (fun _ _ => 0)
        (fun r hr => ht r (hRS hr)) ?_ (i,j) hti
      intro c hc
      apply hd c
      obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨r, hRS hr, hcr⟩

end
end Balanced.Local.AlignedGlobal

end OAI
