import OAI.NumberTheory.DirichletL.Moments.Poisson

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFirstPoisson
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

lemma principalCRT_scaled_left (a b : O) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  simp only [map_mul, hb, zero_mul]

lemma principalCRT_scaled_right (a b : O) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  simp only [map_mul, ha, zero_mul]

theorem coprime_character_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem residueGauss_inverse (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    residueGauss d hd χ⁻¹ h = star (residueGauss d hd χ (-h)) := by
  let := finite_quotient_span hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  have htrace (x : Residue d) : star (quotientTrace d hd x) = quotientTrace d hd (-x) := by
    rw [Complex.star_def, ← Complex.inv_eq_conj ((quotientTrace d hd).norm_apply x),
      AddChar.map_neg_eq_inv]
  simp only [residueGauss, tsum_fintype, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

theorem coprime_pair_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x)) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a)) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        star (residueGauss b hb χb (-(frequencyReduction b (a * b) (dvd_mul_left b a) h))) := by
  simp only [MulChar.star_apply']
  rw [coprime_character_fourier a b ha hb hcop χa χb⁻¹ h, residueGauss_inverse]

theorem coprime_pair_poisson (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, χa (Ideal.Quotient.mk _ z) * star (χb (Ideal.Quotient.mk _ z)) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) *
        (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
      ∑' j : O, residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P := fun x : Residue (a * b) =>
    χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
      star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hcoeff (j : O) :
      (∑ r : Residue (a * b), P r * quotientTrace (a * b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk _ j * r)) =
      (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
        (residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    have h := coprime_pair_fourier a b ha hb hcop χa χb (Ideal.Quotient.mk _ j)
    simpa only [P, frequencyReduction_mk, map_neg, mul_assoc] using h
  have hpoisson := actual_radial_paper_poisson_trace W K hK (a * b) (mul_ne_zero ha hb) P
  change (∑' z : O, P (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) •
      ∑' j : O, (∑ r : Residue (a * b), P r * quotientTrace (a * b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk _ j * r)) *
          paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) at hpoisson
  simp only [P, frequencyReduction_mk] at hpoisson
  rw [hpoisson]
  change (K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) •
    (∑' j : O, (∑ r : Residue (a * b), P r * quotientTrace (a * b) (mul_ne_zero ha hb)
      (Ideal.Quotient.mk _ j * r)) *
      paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2)) = _
  simp_rw [hcoeff, mul_assoc]
  simp_rw [tsum_mul_left]
  rw [Complex.real_smul]

end SevenEighths.CenteredMomentFirstPoisson
end

end OAI
