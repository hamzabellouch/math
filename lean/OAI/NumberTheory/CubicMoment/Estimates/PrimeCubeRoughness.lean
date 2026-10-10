import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeRoughDivisor

namespace OAI

/-! The explicit reciprocal-prime error in the cube lattice saves a
power on every rough fixed-length prime convolution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeProduct_primeFactors_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) :
    (primaryPrimeFactors b).card ≤ Fintype.card ι := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hp (i : ι) : primaryPrime (f i) := hS i _ (Fintype.mem_piFinset.mp hf i)
  have hprim : primary (∏ i, f i) := primary_finset_prod _ _ (fun i _ => (hp i).1)
  have hsub : primaryPrimeFactors (∏ i, f i) ⊆ Finset.univ.image f := by
    intro p hmem
    have hpp := (primaryPrimeFactor_spec hprim hmem).1
    have hpd := (primaryPrimeFactor_spec hprim hmem).2
    obtain ⟨i,_,hi⟩ := (hpp.2.dvd_finsetProd_iff f).mp hpd
    have he : p = f i := primary_associated_eq hpp.1 (hp i).1
      ((hpp.2.dvd_prime_iff_associated (hp i).2).mp hi)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
  exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))

lemma fullPrime_pair_reciprocal_sum_le {R D : ℝ} (hD : 0 < D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) {a b : Eisenstein}
    (ha : a ∈ fullSquarefreePrimeSupport R W X e)
    (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤
      2*(Fintype.card ι:ℝ)/D := by
  have hp (z : Eisenstein) (hz : z ∈ fullSquarefreePrimeSupport R W X e)
      (p : Eisenstein) (hmem : p ∈ primaryPrimeFactors z) : D < norm p := by
    have hprim := (fullSquarefreePrimeSupport_primary R W X e hz).1
    have hpp := (primaryPrimeFactor_spec hprim hmem).1
    obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hpp
      (primaryPrimeFactor_spec hprim hmem).2 (Finset.mem_filter.mp hz).1
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
    have hn : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    exact (hrough i).trans_le (by simpa using (le_div_iff₀ (hX i)).mp hn)
  have hc (z : Eisenstein) (hz : z ∈ fullSquarefreePrimeSupport R W X e) :
      (primaryPrimeFactors z).card ≤ Fintype.card ι :=
    primeProduct_primeFactors_card _ (fullPrimeSupport_prime R W X) (Finset.mem_filter.mp hz).1
  have hcard : ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ) ≤ 2*(Fintype.card ι:ℝ) := by
    have hn := (Finset.card_union_le (primaryPrimeFactors a) (primaryPrimeFactors b)).trans
      (Nat.add_le_add (hc a ha) (hc b hb))
    exact_mod_cast (show (primaryPrimeFactors a ∪ primaryPrimeFactors b).card ≤ 2*Fintype.card ι by omega)
  calc
    _ ≤ ∑ _p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/D := by
      apply Finset.sum_le_sum
      intro p hmem
      have hn : D ≤ norm p := by
        rcases Finset.mem_union.mp hmem with h | h
        · exact (hp a ha p h).le
        · exact (hp b hb p h).le
      exact one_div_le_one_div_of_le hD hn
    _ = ((primaryPrimeFactors a ∪ primaryPrimeFactors b).card:ℝ)/D := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right hcard hD.le

end CubicFirstMoment

end

end OAI
