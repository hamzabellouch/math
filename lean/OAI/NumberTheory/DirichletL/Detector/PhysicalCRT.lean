import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalRowCompletion GaussianShiftedPartition
open CanonicalQuadraticSieve CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentFirstPoisson CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem coprime_function_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (Fa : Residue a → ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      Fa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      (∑ x : Residue a, Fa (Ideal.Quotient.mk _ b*x) *
        quotientTrace a ha (frequencyReduction a (a*b) (dvd_mul_right a b) h*x)) *
      (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
        quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
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
  simp only [ he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem sexticGauss_coprime_product (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : IsCoprime a b) (H : O) :
    sexticGauss (a*b) (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)) H =
      idealRowHom b (Ideal.span {a}) * idealRowHom a (Ideal.span {b}) *
        sexticGauss a (supportedElement_ne_zero a ha) H *
        sexticGauss b (supportedElement_ne_zero b hb) H := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let := finite_quotient_span (supportedElement_ne_zero b hb)
  let := finite_quotient_span (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a*b)) := Fintype.ofFinite _
  have he := coprime_character_fourier a b (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)
    hcop (supportedModulusCharacter a ha) (supportedModulusCharacter b hb) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk,
    residueGauss_supported_mk] at he
  rw [← he]
  unfold sexticGauss
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sexticGauss_coefficient_mk]
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk]
  congr 1
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma elementFourier_const_mul (c : O) (hc : c≠0) (F : O → ℂ) (H : O) (B : ℂ) :
    elementFourier c hc (fun m => B*F m) H = B*elementFourier c hc F H := by
  simp only [elementFourier, mul_assoc, tsum_mul_left]

lemma bareMoving_product (A B s r : O) (hs : Supported (Ideal.span {s}))
    (hr : Supported (Ideal.span {r})) (hcop : IsCoprime s r) (m : O) :
    idealRowHom m (Ideal.span {A*B}) *
      sexticGauss (s*r) (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) (-m) =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      ((idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) := by
  rw [sexticGauss_coprime_product s r hs hr hcop]
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  ring

theorem barePhysicalFourier_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    barePhysicalFourier (A*B) (s*r) (mul_ne_zero hA hB)
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
  have hsc : IsCoprime s r := hcop.of_mul_left_right.of_mul_right_right
  have hc1 : IsCoprime (B*r) s := hcop.of_mul_left_right.symm
  have hc2 : IsCoprime (A*s) r := hcop.of_mul_right_right
  have hAs := mul_ne_zero hA (supportedElement_ne_zero s hs)
  have hBr := mul_ne_zero hB (supportedElement_ne_zero r hr)
  let := finite_quotient_span hAs
  let := finite_quotient_span hBr
  let := finite_quotient_span (mul_ne_zero hAs hBr)
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let : Fintype (Residue (B*r)) := Fintype.ofFinite _
  let : Fintype (Residue ((A*s)*(B*r))) := Fintype.ofFinite _
  have he := coprime_function_fourier (A*s) (B*r) hAs hBr hcop
    (movingQuotient A s (supportedElement_ne_zero s hs))
    (movingQuotient B r (supportedElement_ne_zero r hr)) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk] at he
  simp_rw [movingQuotient_unit_scale A s hs (B*r) hc1,
    movingQuotient_unit_scale B r hr (A*s) hc2, mul_assoc] at he
  simp only [← Finset.mul_sum] at he
  have hexpand : elementFourier ((A*s)*(B*r)) (mul_ne_zero hAs hBr)
      (fun m => (idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) H =
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
    unfold elementFourier
    rw [tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hmk := representative_spec ((A*s)*(B*r)) x
        have hred1 : frequencyReduction (A*s) ((A*s)*(B*r)) (dvd_mul_right _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        have hred2 : frequencyReduction (B*r) ((A*s)*(B*r)) (dvd_mul_left _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        rw [hred1, hred2, movingQuotient_mk, movingQuotient_mk]
        ring
      _ = _ := he
      _ = _ := by
        simp only [barePhysicalFourier, elementFourier, movingQuotient, tsum_fintype]
        ring
  simp only [barePhysicalFourier] at hexpand
  unfold barePhysicalFourier
  rw [elementFourier_congr ((A*B)*(s*r)) ((A*s)*(B*r)) _ (mul_ne_zero hAs hBr) _ H (by ring)]
  simp_rw [bareMoving_product A B s r hs hr hsc]
  rw [elementFourier_const_mul, hexpand]
  ring

theorem bareCongruenceCoefficient_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  have he := barePhysicalFourier_product A B s r hA hB hs hr hcop H
  simp only [barePhysicalFourier_eq] at he
  have hnorm : Ideal.absNorm (Ideal.span {s*r}) =
      Ideal.absNorm (Ideal.span {s}) * Ideal.absNorm (Ideal.span {r}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm, Nat.cast_mul] at he
  have hns : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  have hnr : (Ideal.absNorm (Ideal.span {r}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero r hr))
  apply mul_left_cancel₀ (mul_ne_zero hns hnr)
  rw [he]
  ring

lemma idealRowHom_ne_zero_of_coprime (s a : O)
    (hs : Supported (Ideal.span {s})) (hc : IsCoprime s a) :
    idealRowHom a (Ideal.span {s})≠0 := by
  rw [← supportedModulusCharacter_mk s hs a]
  exact (supportedModulusCharacter s hs).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff s a).mpr hc)

theorem bareCongruenceCoefficient_product_reduced (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  rw [bareCongruenceCoefficient_product A B s r hA hB hs hr hcop H]
  have hsr := idealRowHom_ne_zero_of_coprime s r hs
    hcop.of_mul_left_right.of_mul_right_right
  have hrs := idealRowHom_ne_zero_of_coprime r s hr
    hcop.of_mul_left_right.of_mul_right_right.symm
  have hsB := idealRowHom_ne_zero_of_coprime s B hs
    hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr
    hcop.of_mul_left_left.of_mul_right_right.symm
  simp only [idealRowHom_argument_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
