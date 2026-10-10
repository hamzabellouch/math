import OAI.NumberTheory.DirichletL.Detector.LowActualEnergies

namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma calibration_elementNorm_ge_one (C : CalibrationData) : 1≤elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma sexticGauss_norm_le (s : O) (hs : s≠0) (m : O) : ‖sexticGauss s hs m‖≤elementNorm s := by
  let := finite_quotient_span hs
  let : Fintype (O⧸Ideal.span {s}) := Fintype.ofFinite _
  rw [sexticGauss,tsum_fintype]
  calc
    _ ≤ ∑d : O⧸Ideal.span {s},‖idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s})*
      quotientTrace s hs (Ideal.Quotient.mk _ m*d)‖ := norm_sum_le _ _
    _ ≤ ∑_d : O⧸Ideal.span {s},(1:ℝ) := Finset.sum_le_sum (fun d _=>by
      rw [norm_mul,(quotientTrace s hs).norm_apply,mul_one]
      exact idealRowHom_norm _ _)
    _ = _ := by simp [elementNorm,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma physicalRowWeight_arithmetic_form (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*lowArithmeticCoefficient C r.1*
        (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
        C.residueMonoid r.2*(Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)) := by
  unfold physicalRowWeight lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma physicalRowWeight_crude_point (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (B0 B1 : ℝ) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : ∀x,‖W0 x‖≤B0) (hW1 : ∀x,‖W1 x‖≤B1)
    (X Y : ℝ) (hX : 1≤X) (hY : 0<Y) (r : PhysicalRowIndex) :
    ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1*‖C.tau‖⁻¹/Y := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hb := calibration_elementNorm_ge_one C
  have hscale : 0<elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X :=
    physicalRowScale_pos C X (lt_of_lt_of_le zero_lt_one hX) r.1
  have hqscale : (Ideal.absNorm r.1.val:ℝ)≤elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X := by
    have hbx : 1≤elementNorm C.generator*X := one_le_mul_of_one_le_of_one_le hb hX
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hqscale
  have hrad : (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)≤1 := by
    have hspos : 0<Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
      Real.sqrt (Ideal.absNorm r.1.val:ℝ) := mul_pos (Real.sqrt_pos.mpr hscale) (Real.sqrt_pos.mpr hq)
    calc
      _ = (Ideal.absNorm r.1.val:ℝ)/(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
        Real.sqrt (Ideal.absNorm r.1.val:ℝ)) := by simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ ≤ 1 := (div_le_one hspos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (Ideal.absNorm r.1.val:ℝ)), Real.sq_sqrt hq.le])
  have hg := sexticGauss_norm_le (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)
  have he := (primaryGenerator_spec r.1.val (supported_primaryGenerator_ne_zero r.1.val r.1.property)).1
  unfold elementNorm at hg
  rw [he] at hg
  rw [physicalRowWeight_arithmetic_form]
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Y⁻¹*B1*‖C.tau‖⁻¹*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      1*(Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)*B0 := by
      gcongr
      · exact hW1 _
      · exact lowArithmeticCoefficient_norm C r.1
      · exact C.residueMonoid_norm_le_one r.2
      · exact hW0 _
    _ = (B0*B1*‖C.tau‖⁻¹/Y)*((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
        (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hrad

lemma lowNumeratorRows_card (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 1≤Q) :
    ((lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)).card:ℝ)≤256*max 1 b*Q := by
  have hscale : 1≤2*max 1 b*Q := by nlinarith [le_max_left 1 b]
  have hh := DescentFiberCost.finite_element_count_real (lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)) _ hscale
    (by
      intro m hm
      have h := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ) m).mp hm)).2
      have hn := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hQ)).mp h
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      change elementNorm m≤2*max 1 b*Q
      exact hn.trans (by gcongr;exact le_max_right _ _))
  convert hh using 1 ; ring

lemma lowPhysicalScale_ge_one (C : CalibrationData) (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    1≤lowPhysicalScale C X Y :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (calibration_elementNorm_ge_one C) hX) hY

lemma physicalRowWeight_source_rectangle (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW1c : HasCompactSupport W1) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex)
    (hr : r∉(lowGaussColumns W1 hW1c Y hY) ×ˢ
      (lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY))) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  by_cases hs : r.1∈lowGaussColumns W1 hW1c Y hY
  · have hm : r.2∉lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY) := fun hm=>hr (Finset.mem_product.mpr ⟨hs,hm⟩)
    have hz : lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      simpa only [lowNumeratorRows_mem,not_not] using hm
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    change lowOuterCutoff _ _ (elementNorm r.2/lowPhysicalScale C X Y)*_=0
    rw [hz,zero_mul]
  · apply physicalRowWeight_outer_zero
    simpa only [lowGaussColumns_mem,not_not] using hs

theorem physicalRowWeight_source_mass (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀X Y : ℝ,1≤X → 1≤Y →
      (∑'r : PhysicalRowIndex,‖physicalRowWeight (calibrationForSet S hS) W0 W1 X Y r‖)≤
        K*lowPhysicalScale (calibrationForSet S hS) X Y := by
  let K := 32768*max 1 b1*max 1 (b0*b1)*B0*B1+1
  refine ⟨K,by dsimp only [K];positivity,?_⟩
  intro S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 X Y hX hY
  let C := calibrationForSet S hS
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale C X Y
  have hQ : 1≤Q := lowPhysicalScale_ge_one C X Y hX hY
  let F := lowGaussColumns W1 hW1c Y hy
  let R := lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q (lowPhysicalScale_pos C X Y hx hy)
  have hzero (r : PhysicalRowIndex) (hr : r∉F×ˢR) : ‖physicalRowWeight C W0 W1 X Y r‖=0 := by
    rw [physicalRowWeight_source_rectangle C W0 W1 hW1c a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hx hy r hr,norm_zero]
  have hpoint (r : PhysicalRowIndex) : ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1/Y := by
    have h := physicalRowWeight_crude_point C W0 W1 B0 B1 hB0 hB1 hWB0 hWB1 X Y hX hy r
    simpa only [C,calibrationForSet_tau_norm,inv_one,mul_one] using h
  have hF : (F.card:ℝ)≤128*max 1 b1*Y := lowGaussColumns_card W1 hW1c Y hY a1 b1 hW1
  have hR : (R.card:ℝ)≤256*max 1 (b0*b1)*Q := by
    simpa only [R,max_eq_right (le_max_left 1 (b0*b1))] using lowNumeratorRows_card (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q hQ
  rw [tsum_eq_sum (s:=F×ˢR) hzero]
  calc
    _ ≤ ∑_r∈F×ˢR,B0*B1/Y := Finset.sum_le_sum (fun r _=>hpoint r)
    _ = (F.card:ℝ)*(R.card:ℝ)*(B0*B1/Y) := by simp [Finset.card_product,mul_assoc]
    _ ≤ (128*max 1 b1*Y)*(256*max 1 (b0*b1)*Q)*(B0*B1/Y) := by gcongr
    _ = (32768*max 1 b1*max 1 (b0*b1)*B0*B1)*Q := by field_simp;ring
    _ ≤ K*Q := mul_le_mul_of_nonneg_right (by dsimp only [K];linarith) (le_trans zero_le_one hQ)

end SevenEighths.ProbePhysical
end

end OAI
