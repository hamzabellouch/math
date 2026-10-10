import OAI.NumberTheory.DirichletL.Reflection.TailAbsorption

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma familyRawScale_inverse {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) :
    (familyRawScale F s X QK QP)⁻¹=
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*
        (Ideal.absNorm (∏ i,F.ideal i):ℝ)^2*QK^2*QP^2*X⁻¹ := by
  unfold familyRawScale actualKernelCoefficient fixedKernelCoefficient
  simp only [ramifiedScale,pow_zero,map_mul,map_one,Nat.cast_mul,Nat.cast_one,one_pow,mul_one]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
  ring

lemma familyRawScale_inverse_cap {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (Z X QK QP Lcap : ℝ) (hZ : 0<Z) (hX : 0<X) (hK : 0≤QK) (hP : 0≤QP)
    (hFcap : (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap)
    (hKcap : QK≤Z^Lcap) (hPcap : QP≤Z^Lcap) (hXcap : X⁻¹≤Z^Lcap) :
    (familyRawScale F s X QK QP)⁻¹≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*Z^(7*Lcap) := by
  rw [familyRawScale_inverse]
  calc
    _ ≤ (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*
        (Z^Lcap)^2*(Z^Lcap)^2*(Z^Lcap)^2*Z^Lcap := by gcongr
    _ = (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*(Z^Lcap)^7 := by ring
    _ = _ := by
      rw [←Real.rpow_mul_natCast hZ.le]
      congr 2
      ring

theorem geometry_source_scale_cap {γ : Type*} [Fintype γ]
    (a c : γ→Eis) (mode : γ→Bool)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c i) (mode i))) :
    ∃ Z₀ : ℝ,1<Z₀ ∧ ∀ i : γ,∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ),
      ∀ Z X QK QP Lcap : ℝ,Z₀≤Z → 0<X → 0≤QK → 0≤QP →
      (Ideal.absNorm (∏ j,F.ideal j):ℝ)≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      (familyRawScale F (s i) X QK QP)⁻¹≤Z^(7*Lcap+1) := by
  let b := fun i => 27*(sourceCuspScale (s i).index)^2*(Ideal.absNorm (Ideal.span {c i}):ℝ)^2
  let Z₀ := (∑ i,b i)+2
  have hb : ∀ i,0≤b i := fun i => by dsimp only [b];positivity
  have hz : 1<Z₀ := by
    have hh := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hb i)
    dsimp only [Z₀]
    linarith
  refine ⟨Z₀,hz,?_⟩
  intro i φ _ F Z X QK QP Lcap hZ hX hK hP hFc hKc hPc hXc
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hz hZ)
  have hc : b i≤Z := by
    have hh : b i≤∑ j,b j := Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
    dsimp only [Z₀] at hZ
    linarith
  apply (familyRawScale_inverse_cap F (s i) Z X QK QP Lcap hzpos hX hK hP hFc hKc hPc hXc).trans
  calc
    _ ≤ Z*Z^(7*Lcap) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hzpos.le _)
    _ = _ := by rw [Real.rpow_add hzpos,Real.rpow_one];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
