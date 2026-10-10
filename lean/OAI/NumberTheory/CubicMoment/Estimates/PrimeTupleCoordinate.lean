import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeSelection
import OAI.NumberTheory.CubicMoment.Estimates.StructuredConvolution

namespace OAI

/-! Removing one distinguished coordinate is an exact finite bijection.
On squarefree prime tuples the largest-prime coordinate is unique. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateComplementTuples (S : ι → Finset Eisenstein) (i : ι) : Finset (ι → Eisenstein) :=
  Fintype.piFinset (Function.update S i {1})

lemma coordinateComplement_mem (S : ι → Finset Eisenstein) (i : ι) (g : ι → Eisenstein) :
    g ∈ coordinateComplementTuples S i ↔ g i = 1 ∧ ∀ j, j ≠ i → g j ∈ S j := by
  simp only [coordinateComplementTuples,Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · simpa only [Function.update_self,Finset.mem_singleton] using h i
    · intro j hj
      simpa only [Function.update_of_ne hj] using h j
  · rintro ⟨hi,h⟩ j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self,Finset.mem_singleton] using hi
    · simpa only [Function.update_of_ne hj] using h j hj

theorem primeTuple_coordinate_reindex (S : ι → Finset Eisenstein) (i : ι)
    (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ Fintype.piFinset S, F f) =
      ∑ p ∈ S i, ∑ g ∈ coordinateComplementTuples S i, F (Function.update g i p) := by
  rw [←Finset.sum_product (S i) (coordinateComplementTuples S i)
    (fun t : Eisenstein × (ι → Eisenstein) => F (Function.update t.2 i t.1))]
  apply Finset.sum_bij (fun f _ => (f i,Function.update f i 1))
  · intro f hf
    refine Finset.mem_product.mpr ⟨(Fintype.mem_piFinset.mp hf) i,?_⟩
    apply (coordinateComplement_mem S i _).mpr
    refine ⟨Function.update_self _ _ _,?_⟩
    intro j hj
    simpa only [Function.update_of_ne hj] using (Fintype.mem_piFinset.mp hf) j
  · intro f hf g hg he
    have hp := congrArg Prod.fst he
    have hc := congrArg Prod.snd he
    dsimp only [Prod.fst] at hp
    dsimp only [Prod.snd] at hc
    calc
      f = Function.update (Function.update f i 1) i (f i) := by simp
      _ = Function.update (Function.update g i 1) i (g i) := by rw [hp,hc]
      _ = g := by simp
  · intro t ht
    obtain ⟨hp,hg⟩ := Finset.mem_product.mp ht
    obtain ⟨hgi,hgj⟩ := (coordinateComplement_mem S i t.2).mp hg
    refine ⟨Function.update t.2 i t.1,?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hp
      · simpa only [Function.update_of_ne hji] using hgj j hji
    · apply Prod.ext
      · exact Function.update_self _ _ _
      · rw [Function.update_idem,←hgi,Function.update_eq_self]
  · intro f hf
    simp only [Function.update_idem,Function.update_eq_self]

lemma primeTuple_update_product (f : ι → Eisenstein) (i : ι) (p : Eisenstein) :
    (∏ j, Function.update f i p j) = p*(∏ j ∈ Finset.univ.erase i, f j) := by
  rw [←Finset.mul_prod_erase Finset.univ (Function.update f i p) (Finset.mem_univ i),
    Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact Function.update_of_ne (Finset.mem_erase.mp hj).1 p f

omit [DecidableEq ι] in
lemma unique_largest_prime_coordinate [Nonempty ι] (f : ι → Eisenstein)
    (hi : Function.Injective f) (z : ℂ) :
    (∑ i, if largestPrimePredicate primeTieCode ((Finset.univ.image f).erase (f i)) (f i)
      then z else 0) = z := by
  have he : (Finset.univ.image f).Nonempty :=
    Finset.univ_nonempty.image f
  calc
    _ = ∑ p ∈ Finset.univ.image f,
        if largestPrimePredicate primeTieCode ((Finset.univ.image f).erase p) p then z else 0 :=
      (Finset.sum_image (fun a _ b _ hab => hi hab)).symm
    _ = ∑ p ∈ Finset.univ.image f with
        largestPrimePredicate primeTieCode ((Finset.univ.image f).erase p) p, z :=
      (Finset.sum_filter _ _).symm
    _ = z := sum_largestPrime_selected _ he (fun _ => z)

theorem squarefree_primeTuple_largest_split [Nonempty ι] (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ (Fintype.piFinset S).filter (fun f => Squarefree (∏ i, f i)), F f) =
      ∑ i, ∑ f ∈ (Fintype.piFinset S).filter (fun f => Squarefree (∏ i, f i)),
        if largestPrimePredicate primeTieCode ((Finset.univ.image f).erase (f i)) (f i)
          then F f else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  obtain ⟨hf,hs⟩ := Finset.mem_filter.mp hf
  exact (unique_largest_prime_coordinate f
    ((squarefree_prime_tuple_iff f (fun i => hS i (f i) ((Fintype.mem_piFinset.mp hf) i))).mp hs)
    (F f)).symm

end CubicFirstMoment

end

end OAI
