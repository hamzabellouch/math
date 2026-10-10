import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedCoefficients
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedProductPairs

namespace OAI

/-! The literal independent prime-tuple fibre over a squarefree primary
product is exactly its set of orderings. This connects the subset detector
to the fixed-arity coefficients used in the analytic estimates. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreePrimeTupleEquiv {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i)) (hprod : (∏ i, f i) = n) :
    ι ≃ primaryPrimeFactors n :=
  Equiv.ofBijective (fun i => ⟨f i,(primaryPrime_mem_factors_iff hn).mpr
    ⟨hf i,hprod ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)⟩⟩) (by
      constructor
      · intro i j hij
        have hinj := (squarefree_prime_tuple_iff f hf).mp (hprod.symm ▸ hs)
        exact hinj (congrArg Subtype.val hij)
      · intro p
        have hp := primaryPrimeFactor_spec hn p.property
        have hd : (p:Eisenstein) ∣ ∏ i, f i := hprod.symm ▸ hp.2
        obtain ⟨i,_,hi⟩ := (hp.1.2.dvd_finsetProd_iff f).mp hd
        have he : (p:Eisenstein) = f i := primary_associated_eq hp.1.1 (hf i).1
          ((hp.1.2.dvd_prime_iff_associated (hf i).2).mp hi)
        exact ⟨i,Subtype.ext he.symm⟩)

lemma squarefreePrimeTuple_card {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i)) (hprod : (∏ i, f i) = n) :
    Fintype.card ι = (primaryPrimeFactors n).card := by
  simpa using Fintype.card_congr (squarefreePrimeTupleEquiv hn hs f hf hprod)

theorem orderedConvolution_prime_fiber {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {B : ℝ} (hB : norm n ≤ B) (v : Eisenstein → ℂ) :
    orderedConvolution (fun _ : ι => primeCutoff B) (fun _ => v) n =
      ∑ e : ι ≃ primaryPrimeFactors n, ∏ i, v (e i) := by
  unfold orderedConvolution
  symm
  apply Finset.sum_bij (fun (e : ι ≃ primaryPrimeFactors n) _ i => (e i:Eisenstein))
  · intro e _
    have he : (∏ i, (e i:Eisenstein)) = n := by
      calc
        _ = ∏ p ∈ primaryPrimeFactors n, p :=
          (e.prod_comp (fun p : primaryPrimeFactors n => (p:Eisenstein))).trans
            (Finset.prod_coe_sort (primaryPrimeFactors n) (fun p : Eisenstein => p))
        _ = n := primaryPrimeFactors_prod hn hs
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_),he⟩
    have hp := primaryPrimeFactor_spec hn (e i).property
    exact mem_primeCutoff.mpr ⟨hp.1,(norm_le_of_dvd (primary_ne_zero hn) hp.2).trans hB⟩
  · intro e _ d _ hed
    apply Equiv.ext
    intro i
    exact Subtype.ext (congrFun hed i)
  · intro f hfin
    obtain ⟨hfin,hprod⟩ := Finset.mem_filter.mp hfin
    have hp (i : ι) : primaryPrime (f i) :=
      (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hfin i)).1
    exact ⟨squarefreePrimeTupleEquiv hn hs f hp hprod,Finset.mem_univ _,rfl⟩
  · intro e _
    rfl

theorem distinguishedSubsetWeight_as_tuple {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hB : norm n ≤ B) (ψ : ℝ → ℝ) (w z : ℝ) :
    distinguishedSubsetWeight ψ w z n =
      distinguishedTupleCoefficient (fun _ : Fin (primaryPrimeFactors n).card => primeCutoff B)
        (fun _ _ => 1) ψ w z n := by
  unfold distinguishedTupleCoefficient
  simp only [Fintype.card_fin,one_mul]
  rw [orderedConvolution_prime_fiber hn hs hB]
  symm
  exact ordered_subset_product (primaryPrimeFactors n) (distinguishedPrimeWeight ψ w z)

theorem distinguishedTupleCoefficient_zero_of_card_ne {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) {B : ℝ}
    (hcard : Fintype.card ι ≠ (primaryPrimeFactors n).card)
    (ψ : ℝ → ℝ) (w z : ℝ) :
    distinguishedTupleCoefficient (fun _ : ι => primeCutoff B) (fun _ _ => 1) ψ w z n = 0 := by
  unfold distinguishedTupleCoefficient orderedConvolution
  suffices hempty : (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
      (fun f => (∏ i, f i) = n) = ∅ by rw [hempty,Finset.sum_empty,mul_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hf,hprod⟩ := Finset.mem_filter.mp hf
  exact hcard (squarefreePrimeTuple_card hn hs f
    (fun i => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf i)).1) hprod)

end CubicFirstMoment

end

end OAI
