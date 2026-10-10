import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleCoordinate
import OAI.NumberTheory.CubicMoment.Estimates.SelectedPrimeCanonical

namespace OAI

/-! The distinguished largest-prime role splits into the actual tuple
coordinates with multiplicity one, even in the presence of the selected
divisor. No ordering of its prime factors is introduced. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma prime_tuple_divisor_indicator (f : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hi : Function.Injective f)
    {p : Eisenstein} (hp : primaryPrime p) (z : ℂ) :
    (if p ∣ ∏ i, f i then z else 0) = ∑ i, if p = f i then z else 0 := by
  by_cases hdiv : p ∣ ∏ i, f i
  · obtain ⟨i,_,hpi⟩ := (hp.2.dvd_finsetProd_iff f).mp hdiv
    have he : p = f i := primary_associated_eq hp.1 (hf i).1
      ((hp.2.dvd_prime_iff_associated (hf i).2).mp hpi)
    rw [ite_eq_left hdiv]
    symm
    calc
      _ = (if p = f i then z else 0) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hne : ¬p = f j := fun hpj => hji (hi (hpj.symm.trans he))
          exact ite_eq_right hne
        · intro hnot
          exact (hnot (Finset.mem_univ i)).elim
      _ = z := ite_eq_left he
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro he
    apply hdiv
    rw [he]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

/-- A squarefree full product has exactly one distinguished coordinate
when its canonical largest prime lies on the distinguished side. -/
theorem distinguished_largest_coordinate_roles [Nonempty ι]
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i))
    {d : Eisenstein} (hd : primary d) (hs : Squarefree ((∏ i, f i)*d)) (z : ℂ) :
    (if largestPrimeChoice ((∏ i, f i)*d) ∣ ∏ i, f i then z else 0) =
      ∑ i, if largestPrimeChoice ((∏ i, f i)*d) = f i then z else 0 := by
  have hr : primary (∏ i, f i) :=
    primary_finset_prod Finset.univ f (fun i _ => (hf i).1)
  have hi := (squarefree_prime_tuple_iff f hf).mp (squarefree_mul_iff.mp hs).2.1
  let i : ι := Classical.arbitrary ι
  have him : f i ∈ primaryPrimeFactors ((∏ j, f j)*d) :=
    (primaryPrime_mem_factors_iff (primary_mul hr hd)).mpr
      ⟨hf i,(Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans (dvd_mul_right _ _)⟩
  have hne : (primaryPrimeFactors ((∏ j, f j)*d)).Nonempty := ⟨f i,him⟩
  exact prime_tuple_divisor_indicator f hf hi
    (primaryPrimeFactor_spec (primary_mul hr hd) (largestPrimeChoice_spec hne).1).1 z

end CubicFirstMoment

end

end OAI
