import OAI.NumberTheory.DirichletL.Reflection.FamilyTail

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma familyRawScale_reciprocal {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) :
    (familyRawScale F s X QK QP^2)⁻¹=
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*
        (Ideal.absNorm (∏ i,F.ideal i):ℝ)^4*QK^4*QP^4*(X⁻¹)^2 := by
  unfold familyRawScale actualKernelCoefficient fixedKernelCoefficient
  simp only [ramifiedScale,pow_zero,map_mul,map_one,Nat.cast_mul,Nat.cast_one,one_pow,mul_one]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow,inv_pow]
  ring

lemma family_tail_polynomial_cap {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (Z X QK QP Lcap : ℝ) (hZ : 0<Z) (hQK : 0≤QK) (hQP : 0≤QP) (hX : 0<X)
    (hF : (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap)
    (hK : QK≤Z^Lcap) (hP : QP≤Z^Lcap) (hXi : X⁻¹≤Z^Lcap) :
    ((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*(familyRawScale F s X QK QP^2)⁻¹≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*Z^(17*Lcap) := by
  rw [familyRawScale_reciprocal]
  calc
    _ = (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*
        ((Ideal.absNorm (∏ i,F.ideal i):ℝ)^5*QK^5*QP^5*(X⁻¹)^2) := by ring
    _ ≤ (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*
        ((Z^Lcap)^5*(Z^Lcap)^5*(Z^Lcap)^5*(Z^Lcap)^2) := by gcongr
    _ = _ := by
      rw [←pow_add,←pow_add,←pow_add,←Real.rpow_mul_natCast hZ.le]
      norm_num only [Nat.reduceAdd,Nat.cast_ofNat]
      rw [mul_comm Lcap 17]

theorem choose_rapid_tail_order (Lcap δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ Z : ℝ, 1≤Z →
      (Z^δ)^(-(A:ℝ))*Z^Lcap≤Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((Lcap+saving)/δ)
  refine ⟨A,?_⟩
  intro Z hZ
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hh := (div_lt_iff₀ hδ).mp hA
  nlinarith

theorem choose_weighted_rapid_tail_order (Lcap Lextra δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ Z E : ℝ, 1≤Z → 0≤E → E≤Z^Lextra →
      E*(Z^δ)^(-(A:ℝ))*Z^Lcap≤Z^(-saving) := by
  obtain ⟨A,hA⟩ := choose_rapid_tail_order (Lcap+Lextra) δ saving hδ
  refine ⟨A,?_⟩
  intro Z E hZ hE he
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  calc
    _ ≤ Z^Lextra*(Z^δ)^(-(A:ℝ))*Z^Lcap := by gcongr
    _ = (Z^δ)^(-(A:ℝ))*Z^(Lcap+Lextra) := by rw [Real.rpow_add hz]; ring
    _ ≤ _ := hA Z hZ
end
end SevenEighths.InverseReflectedPhase

end OAI
