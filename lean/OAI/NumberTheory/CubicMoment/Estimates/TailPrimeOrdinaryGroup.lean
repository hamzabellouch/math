import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeTailGeometry

namespace OAI

/-! Ordinary high rows have a closed one-third grouping even at the
exceptional triple. Only support geometry is used here. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma tailPrimeTupleOrdinary_upper {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {H U X : ℝ} (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) : largePrimeTupleNorm q a ≤ 3*X^(131/200:ℝ) := by
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
      (show (2/5:ℝ) ≤ 131/200 by norm_num)
    nlinarith [Real.rpow_pos_of_pos hXp (131/200:ℝ)]
  · have hprim : primary (∏ b, q.2 b) := primary_finset_prod _ _
      (fun b _ => (mem_primeCutoff.mp
        (Fintype.mem_piFinset.mp (Finset.mem_product.mp hq).2 b)).1.1)
    have hnb := norm_le_of_dvd (primary_ne_zero hprim)
      (Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b))
    have hnr := hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1
    have hprod := (tailPrimeTupleTerm_product_range hXp ht).2
    rw [largePrimeTupleProduct,norm_mul_eq] at hprod
    have hm : X^(69/200:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(69/200:ℝ)*(3*X^(131/200:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      rw [show (69/200:ℝ)+(131/200)=1 by ring,Real.rpow_one]
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (69/200:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm


lemma tailPrimeTupleOrdinary_exponents {i j N : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 1 ≤ X) (hlog : 1000 ≤ Real.log X) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) :
    0 < largePrimeTupleExponent q a ∧ largePrimeTupleExponent q a ≤ 2/3 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have ht := (mul_ne_zero_iff.mp hne).1
  have hn := tailPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hn.1
  have hlo := Real.log_le_log (by positivity : (0:ℝ) < X/2) hn.1
  rw [Real.log_div hXp.ne' (by norm_num)] at hlo
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have hln : 0 < Real.log (norm (largePrimeTupleProduct q)) := by linarith
  have hr := Real.log_le_log (Real.rpow_pos_of_pos hXp ξ)
    (tailPrimeTupleNorm_rough hX hξz hq ht a).le
  rw [Real.log_rpow hXp] at hr
  have hu := Real.log_le_log (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
    (tailPrimeTupleOrdinary_upper hX hξz k hhigh hq hne a)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hXp (131/200:ℝ)).ne',Real.log_rpow hXp] at hu
  unfold largePrimeTupleExponent
  exact ⟨div_pos (lt_of_lt_of_le (mul_pos hξ (by linarith)) hr) hln,
    (div_le_iff₀ hln).mpr (by linarith)⟩

theorem tailPrimeTupleOrdinary_group {i j N : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 1 ≤ X) (hlog : 1000 ≤ Real.log X) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    ∃ s : Finset (Fin i ⊕ Fin j),
      ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤
        largeTupleSubsetScale (fun a => (k a).val) s ∧
      (largeTupleSubsetScale (fun a => (k a).val) s)^2 ≤ 3*X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hn := tailPrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hn.1
  have hln : 0 < Real.log (norm (largePrimeTupleProduct q)) := by
    have hh := Real.log_le_log (by positivity : (0:ℝ) < X/2) hn.1
    rw [Real.log_div hXp.ne' (by norm_num)] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  obtain ⟨s,_hs,hlo,hhi⟩ := prime_exponent_short_group Finset.univ
    (largePrimeTupleExponent q) (by norm_num : (0:ℝ) < 1/3) le_rfl
    (fun a _ => by
      have hh := tailPrimeTupleOrdinary_exponents hX hlog hξ hξz k hhigh hq hne a
      exact ⟨hh.1,by linarith [hh.2]⟩)
    (largePrimeTupleExponent_sum hq hln.ne')
  obtain ⟨hl,hu⟩ := largePrimeTuplePiece_group_scale k hq (mul_ne_zero_iff.mp hne).2 hnp hln s hlo hhi
  refine ⟨s,?_,?_⟩
  · have hcard : s.card ≤ i+j := by
      simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using s.card_le_univ
    calc
      _ = (X/2)^(1/3:ℝ)/2^(i+j) := by
        rw [show X/2 = (1/2:ℝ)*X by ring,Real.mul_rpow (by norm_num) hXp.le]
        ring
      _ ≤ norm (largePrimeTupleProduct q)^(1/3:ℝ)/2^(i+j) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hn.1 (by norm_num)) (by positivity)
      _ ≤ norm (largePrimeTupleProduct q)^(1/3:ℝ)/2^s.card :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hcard)
      _ ≤ _ := hl
  · have hh := pow_le_pow_left₀ (largeTupleSubsetScale_pos _ _).le hu 2
    have he : (norm (largePrimeTupleProduct q)^(1/2:ℝ))^2 = norm (largePrimeTupleProduct q) := by
      rw [←Real.rpow_mul_natCast hnp.le]
      norm_num
    exact hh.trans (by rw [he]; exact hn.2)

theorem eventually_tailPrimeTupleTail_ordinary_groups (i j : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ H T : ℝ,
      ∀ k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      tailPrimeTupleTail i j ξ H T X k ≠ 0 →
      ∃ s : Finset (Fin i ⊕ Fin j),
        let B := largeTupleSubsetScale (fun a => (k a).val) s
        let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
        ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤ B ∧ B^2 ≤ 3*X ∧ X/(2*2^(i+j)) ≤ A*B ∧ A*B ≤ 3*X ∧
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        (∀ a, (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ H' T' : ℝ, tailPrimeTupleTail i j ξ H' T' X k =
          ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
            envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X (fun a => (k a).val) s)
              (largeTupleOtherSupport ξ X (fun a => (k a).val) s)
              (largeTupleSelectedCoefficient ξ X (fun a => (k a).val) s)
              (largeTupleOtherCoefficient ξ X (fun a => (k a).val) s)
              primeProductEnvelope H' T' X := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1000,
    eventually_tailPrimeTuple_coordinate_envelope (i := i) (j := j)
      (κ := 0) (by norm_num) (by norm_num) hξz,
    tailPrimeTuplePiece_rough_scales i j hξ hξz] with X hX hlog hcoord hrough
  intro H T k hhigh hne
  obtain ⟨v,_hv,q,hq,hqn⟩ := tailPrimeTupleTail_witness k hne
  obtain ⟨s,hB,hBsq⟩ := tailPrimeTupleOrdinary_group hX hlog hξ hξz k hhigh hq hqn
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hprod := tailPrimeTuple_scale_product hXp k hqn
  have hp : largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)*
      largeTupleSubsetScale (fun a => (k a).val) s =
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ := by
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hr := hrough 0 H (T*(3/2:ℝ)^v) k q hq hqn
  have hB3 : largeTupleSubsetScale (fun a => (k a).val) s ≤ 3*X := by
    have hBp := largeTupleSubsetScale_pos (fun a => (k a).val) s
    nlinarith
  have hhigh' : X^(1/3-2*(0:ℝ)) ≤ largeTupleDistinguishedScale (fun a => (k a).val) :=
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/3-2*(0:ℝ)) ≤ 69/200)).trans hhigh
  refine ⟨s,hB,hBsq,by simpa only [hp] using hprod.1,
    by simpa only [hp] using hprod.2,hr.1,
    hr.2 _ (largeTupleSubsetScale_pos _ _).le hB3,?_⟩
  intro H' T'
  unfold tailPrimeTupleTail
  simp_rw [tailPrimeTuplePiece_full i j 0 ξ H' _ X k
    (hcoord 0 H (T*(3/2:ℝ)^v) k hhigh' q hq hqn),
    tailPrimeTupleIndependent_regroup i j 0 ξ H' _ X _ s]
  rw [←Finset.mul_sum,tailPrimeTupleRegrouped_tail]

end CubicFirstMoment

end

end OAI
