import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTuple

namespace OAI

/-! On the manuscript's scale-first high branch, every actual prime is
below X^(131/200) up to a fixed constant. This is still strictly below
the two-thirds barrier needed by the proved grouping alternative. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma uncutPrimeTupleTerm_factors_ne_zero {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : uncutPrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a)) ≠ 0 ∧
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ))) ≠ 0 ∧
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
        X X (largePrimeTupleProduct q) ≠ 0 := by
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2,(mul_ne_zero_iff.mp hne).2⟩

lemma uncutPrimeTupleTerm_product_range {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 0 < X)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : uncutPrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    X/2 ≤ norm (largePrimeTupleProduct q) ∧ norm (largePrimeTupleProduct q) ≤ 3*X :=
  semiprime_kernel_product_range ℓ H _ hX (uncutPrimeTupleTerm_factors_ne_zero hne).2.2

lemma uncutPrimeTupleNorm_rough {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : uncutPrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) (a : Fin i ⊕ Fin j) :
    X^ξ < largePrimeTupleNorm q a := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw := Real.rpow_pos_of_pos hXp ξ
  obtain ⟨hf,hg,_⟩ := uncutPrimeTupleTerm_factors_ne_zero hne
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    exact (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) hw
      (Real.rpow_le_rpow_of_exponent_le hX hξz)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).1
  · have hn := Finset.prod_ne_zero_iff.mp hg b (Finset.mem_univ b)
    change X^ξ < norm (q.2 b)
    by_contra hh
    apply hn
    rw [primeDetectorCutoff_one ((div_le_one hw).mpr (not_lt.mp hh))]
    simp

lemma uncutPrimeTupleNorm_high_upper {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : uncutPrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) : largePrimeTupleNorm q a ≤ 3*X^(131/200:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hf,_,_⟩ := uncutPrimeTupleTerm_factors_ne_zero ht
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    have hh := (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) (Real.rpow_pos_of_pos hXp ξ)
      (Real.rpow_le_rpow_of_exponent_le hX hξz)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).2
    change norm (q.1 a) ≤ _
    have hp := Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (2/5:ℝ) ≤ 131/200)
    nlinarith [Real.rpow_pos_of_pos hXp (131/200:ℝ)]
  · have hprim : primary (∏ b, q.2 b) := primary_finset_prod _ _
      (fun b _ => (mem_primeCutoff.mp
        (Fintype.mem_piFinset.mp (Finset.mem_product.mp hq).2 b)).1.1)
    have hnb := norm_le_of_dvd (primary_ne_zero hprim)
      (Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b))
    have hnr := hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1
    have hprod := (uncutPrimeTupleTerm_product_range hXp ht).2
    rw [largePrimeTupleProduct,norm_mul_eq] at hprod
    have hm : X^(69/200:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(69/200:ℝ)*(3*X^(131/200:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      norm_num
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (69/200:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm

lemma uncutPrimeTuple_high_exponents {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 1 ≤ X) (hlog : 2000 ≤ Real.log X)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : uncutPrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) :
    ξ/2 ≤ largePrimeTupleExponent q a ∧ largePrimeTupleExponent q a ≤ 33/50 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have ht := (mul_ne_zero_iff.mp hne).1
  have hnrange := uncutPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hnrange.1
  have hlower := Real.log_le_log (by positivity : (0:ℝ) < X/2) hnrange.1
  rw [Real.log_div hXp.ne' (by norm_num)] at hlower
  have hupper := Real.log_le_log hnp hnrange.2
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hupper
  have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  have hlog3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)).trans (by norm_num)
  have hlogn : 0 < Real.log (norm (largePrimeTupleProduct q)) := by linarith
  have hlogsmall := Real.log_le_log (Real.rpow_pos_of_pos hXp ξ)
    (uncutPrimeTupleNorm_rough hX hξz hq ht a).le
  rw [Real.log_rpow hXp] at hlogsmall
  have hloglarge := Real.log_le_log
    (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
    (uncutPrimeTupleNorm_high_upper hX hξz k hhigh hq hne a)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hXp (131/200:ℝ)).ne',Real.log_rpow hXp] at hloglarge
  unfold largePrimeTupleExponent
  constructor
  · apply (le_div_iff₀ hlogn).mpr
    have hntwo : Real.log (norm (largePrimeTupleProduct q)) ≤ 2*Real.log X := by linarith
    nlinarith
  · apply (div_le_iff₀ hlogn).mpr
    linarith

end CubicFirstMoment

end

end OAI
