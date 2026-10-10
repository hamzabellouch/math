import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleFiber
import OAI.NumberTheory.CubicMoment.Estimates.RoughPrimeTuples

namespace OAI

/-! The actual rough remainder is a finite sum of independent prime
convolutions. The factorial weight, literal product and roughness cutoff
are retained. This is the second arity expansion needed for the large rows. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def roughTupleCoefficient (k : ℕ) (B : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (n : Eisenstein) : ℂ :=
  (k.factorial:ℂ)⁻¹ * orderedConvolution (fun _ : Fin k => primeCutoff B)
    (fun _ p => 1-(ψ (norm p/w):ℂ)) n

lemma roughProduct_as_tuple {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {B : ℝ} (hB : norm n ≤ B) (ψ : ℝ → ℝ) (w : ℝ) :
    (roughProduct ψ w n:ℂ) =
      roughTupleCoefficient (primaryPrimeFactors n).card B ψ w n := by
  unfold roughTupleCoefficient
  rw [orderedConvolution_prime_fiber hn hs hB]
  exact roughProduct_ordered_primary_factors ψ w n

lemma roughTupleCoefficient_zero_of_card_ne {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) {B : ℝ} {k : ℕ}
    (hcard : k ≠ (primaryPrimeFactors n).card) (ψ : ℝ → ℝ) (w : ℝ) :
    roughTupleCoefficient k B ψ w n = 0 := by
  unfold roughTupleCoefficient orderedConvolution
  suffices hempty : (Fintype.piFinset (fun _ : Fin k => primeCutoff B)).filter
      (fun f => (∏ i, f i) = n) = ∅ by rw [hempty,Finset.sum_empty,mul_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hf,hprod⟩ := Finset.mem_filter.mp hf
  apply hcard
  simpa only [Fintype.card_fin] using squarefreePrimeTuple_card hn hs f
    (fun i => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf i)).1) hprod

lemma roughProduct_eq_sum_tuples {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hB : norm n ≤ B) (ψ : ℝ → ℝ)
    (w : ℝ) {k : ℕ}
    (hsize : roughProduct ψ w n ≠ 0 → (primaryPrimeFactors n).card < k) :
    (roughProduct ψ w n:ℂ) =
      ∑ i ∈ Finset.range k, roughTupleCoefficient i B ψ w n := by
  let m := (primaryPrimeFactors n).card
  have hother (i : ℕ) (hi : i ≠ m) : roughTupleCoefficient i B ψ w n = 0 :=
    roughTupleCoefficient_zero_of_card_ne hn hs hi ψ w
  by_cases hm : m < k
  · rw [Finset.sum_eq_single m]
    · exact roughProduct_as_tuple hn hs hB ψ w
    · intro i _hi him
      exact hother i him
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hm)).elim
  · have hz : roughProduct ψ w n = 0 := by
      by_contra hne
      exact hm (hsize hne)
    rw [hz,Complex.ofReal_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact hother i (fun he => hm (he ▸ Finset.mem_range.mp hi))

theorem eventually_rough_coefficient_tuples {ξ C : ℝ}
    (hξ : 0 < ξ) (hC : 0 < C) {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ n : Eisenstein,
      primary n → Squarefree n → norm n ≤ C*X →
      (roughProduct ψ (X^ξ) n:ℂ) =
        ∑ i ∈ Finset.range k, roughTupleCoefficient i (C*X) ψ (X^ξ) n := by
  obtain ⟨k,hbound⟩ := bounded_rough_primary_factors hξ hC hψ
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro n hn hs hnX
  exact roughProduct_eq_sum_tuples hn hs hnX ψ (X^ξ) (hX n hn hs hnX)

end CubicFirstMoment

end

end OAI
