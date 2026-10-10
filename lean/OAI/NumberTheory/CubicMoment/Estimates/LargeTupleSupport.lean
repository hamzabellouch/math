import OAI.NumberTheory.CubicMoment.Estimates.LargeTuplePartition
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeRange

namespace OAI

/-! Actual support geometry of the large distinguished rows. Every prime
is rough, and the complementary primes inherit the X^(31/50) bound from
the original large distinguished product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTupleTerm_membership {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    (∏ a, q.1 a) ∈ (centralPrimaryFactors X).filter
        (fun r => ¬norm r < X^(38/100:ℝ)) ∧
      (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) := by
  unfold largePrimeTupleTerm at hne
  split_ifs at hne with hr hu
  · exact ⟨hr,hu⟩
  · exact (hne rfl).elim
  · exact (hne rfl).elim

lemma largePrimeTupleTerm_factors_ne_zero {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a)) ≠ 0 ∧
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ))) ≠ 0 ∧
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
        X X ((∏ a, q.1 a)*(∏ b, q.2 b)) ≠ 0 := by
  obtain ⟨hr,hu⟩ := largePrimeTupleTerm_membership hne
  simp only [largePrimeTupleTerm,hr,hu,ite_true] at hne
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2,(mul_ne_zero_iff.mp hne).2⟩

lemma largePrimeTupleTerm_product_range {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    (hX : 0 < X) {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    X/2 ≤ norm ((∏ a, q.1 a)*(∏ b, q.2 b)) ∧
      norm ((∏ a, q.1 a)*(∏ b, q.2 b)) ≤ 3*X :=
  semiprime_kernel_product_range ℓ H _ hX (largePrimeTupleTerm_factors_ne_zero hne).2.2

lemma largePrimeTupleNorm_rough_bound {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    (hX : 1 ≤ X) (hξ : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) (a : Fin i ⊕ Fin j) :
    X^ξ < largePrimeTupleNorm q a := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw := Real.rpow_pos_of_pos hXp ξ
  obtain ⟨hf,hg,_hk⟩ := largePrimeTupleTerm_factors_ne_zero hne
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    exact (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) hw
      (Real.rpow_le_rpow_of_exponent_le hX hξ)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).1
  · have hn := Finset.prod_ne_zero_iff.mp hg b (Finset.mem_univ b)
    change X^ξ < norm (q.2 b)
    by_contra hh
    apply hn
    rw [primeDetectorCutoff_one ((div_le_one hw).mpr (not_lt.mp hh))]
    simp

lemma largePrimeTupleNorm_upper_bound {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    (hX : 1 ≤ X) (hξ : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) (a : Fin i ⊕ Fin j) :
    largePrimeTupleNorm q a ≤ 3*X^(31/50:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨hf,_hg,_hk⟩ := largePrimeTupleTerm_factors_ne_zero hne
  obtain ⟨hr,hu⟩ := largePrimeTupleTerm_membership hne
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    have hh := (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) (Real.rpow_pos_of_pos hXp ξ)
      (Real.rpow_le_rpow_of_exponent_le hX hξ)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).2
    change norm (q.1 a) ≤ _
    have hp := Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (2/5:ℝ) ≤ 31/50)
    nlinarith [Real.rpow_pos_of_pos hXp (31/50:ℝ)]
  · have hup := (mem_primaryElementBall.mp (Finset.mem_filter.mp hu).1).1
    have hdiv : q.2 b ∣ ∏ b, q.2 b := Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b)
    have hnb := norm_le_of_dvd (primary_ne_zero hup) hdiv
    have hnr : X^(38/100:ℝ) ≤ norm (∏ a, q.1 a) :=
      le_of_not_gt (Finset.mem_filter.mp hr).2
    have hprod := (largePrimeTupleTerm_product_range hXp hne).2
    rw [norm_mul_eq] at hprod
    have hm : X^(38/100:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(38/100:ℝ)*(3*X^(31/50:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      norm_num
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (38/100:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm

end CubicFirstMoment

end

end OAI
