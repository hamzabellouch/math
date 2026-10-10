import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstGeometry
import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductWindow

namespace OAI

/-! The actual prime-tuple Gauss kernel for upper height windows.
The high branch begins at X^(1/3-2κ), in the prime decomposition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def tailPrimeTupleTerm (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : ℂ :=
  (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
    productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (largePrimeTupleProduct q)

def tailPrimeTuplePiece (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q)

lemma tailPrimeTupleTerm_factors_ne_zero {i j : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q ≠ 0) :
    (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a)) ≠ 0 ∧
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ))) ≠ 0 ∧
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (largePrimeTupleProduct q) ≠ 0 := by
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2,(mul_ne_zero_iff.mp hne).2⟩

lemma tailPrimeTupleTerm_product_range {i j : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 0 < X) {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q ≠ 0) :
    X/2 ≤ norm (largePrimeTupleProduct q) ∧ norm (largePrimeTupleProduct q) ≤ 3*X := by
  have hk := (tailPrimeTupleTerm_factors_ne_zero hne).2.2
  have hw : primeProductEnvelope (norm (largePrimeTupleProduct q)/X) ≠ 0 := by
    intro hz
    apply hk
    simp only [productGaussHeightWindowKernel,hz,mul_zero,zero_mul]
  constructor
  · by_contra hn
    exact hw (primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith)))
  · by_contra hn
    exact hw (primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (by linarith)))

lemma tailPrimeTupleNorm_rough {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {H U X : ℝ} (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q ≠ 0) (a : Fin i ⊕ Fin j) :
    X^ξ < largePrimeTupleNorm q a := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw := Real.rpow_pos_of_pos hXp ξ
  obtain ⟨hf,hg,_⟩ := tailPrimeTupleTerm_factors_ne_zero hne
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

lemma tailPrimeTupleNorm_upper {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {H U X κ : ℝ} (hX : 1 ≤ X) (hκ : 0 ≤ κ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(1/3-2*κ:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) : largePrimeTupleNorm q a ≤ 3*X^(2/3+2*κ:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hf,_,_⟩ := tailPrimeTupleTerm_factors_ne_zero ht
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    have hh := (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) (Real.rpow_pos_of_pos hXp ξ)
      (Real.rpow_le_rpow_of_exponent_le hX hξz)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).2
    change norm (q.1 a) ≤ _
    have hp := Real.rpow_le_rpow_of_exponent_le hX
      (show (2/5:ℝ) ≤ 2/3+2*κ by linarith)
    nlinarith [Real.rpow_pos_of_pos hXp (2/3+2*κ:ℝ)]
  · have hprim : primary (∏ b, q.2 b) := primary_finset_prod _ _
      (fun b _ => (mem_primeCutoff.mp
        (Fintype.mem_piFinset.mp (Finset.mem_product.mp hq).2 b)).1.1)
    have hnb := norm_le_of_dvd (primary_ne_zero hprim)
      (Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b))
    have hnr := hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1
    have hprod := (tailPrimeTupleTerm_product_range hXp ht).2
    rw [largePrimeTupleProduct,norm_mul_eq] at hprod
    have hm : X^(1/3-2*κ:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(1/3-2*κ:ℝ)*(3*X^(2/3+2*κ:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      rw [show (1/3-2*κ:ℝ)+(2/3+2*κ)=1 by ring,Real.rpow_one]
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (1/3-2*κ:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm


end CubicFirstMoment

end

end OAI
