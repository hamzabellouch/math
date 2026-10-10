import OAI.NumberTheory.DirichletL.Reflection.TailEnergyBudget

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_row_tail_energy_budget_uniform_degree
    (Lcap Lcount δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ {a c : Eis} {mode : Bool}
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)), ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
      (Z X QK QP nrow nslot : ℝ),
      1≤Z → 0<X → 0≤QK → 0≤QP → 0≤nrow → 0≤nslot →
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap →
      QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      nrow≤Z^Lcount → nslot≤Z^Lcount →
      nrow*(nslot*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        (Z^δ)^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹)^2≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^4*Z^(-saving) := by
  obtain ⟨A,hA⟩ := choose_weighted_rapid_tail_order (17*Lcap) Lcount δ ((saving+Lcount)/2) hδ
  refine ⟨A,?_⟩
  intro a c mode s φ _ F Z X QK QP nrow nslot hZ hX hQK hQP hnrow hnslot hF hK hP hXi hrow hslot
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2
  have hcusp : 0≤cusp := by dsimp [cusp];positivity
  have hs := family_tail_polynomial_cap F s Z X QK QP Lcap hz hQK hQP hX hF hK hP hXi
  have ha := hA Z nslot hZ hnslot hslot
  have hb : nslot*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*(Z^δ)^(-(A:ℝ))*
        (familyRawScale F s X QK QP^2)⁻¹≤cusp^2*Z^(-((saving+Lcount)/2)) := by
    calc
      _ = (nslot*(Z^δ)^(-(A:ℝ)))*
          (((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*(familyRawScale F s X QK QP^2)⁻¹) := by ring
      _ ≤ (nslot*(Z^δ)^(-(A:ℝ)))*(cusp^2*Z^(17*Lcap)) := by
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      _ = cusp^2*(nslot*(Z^δ)^(-(A:ℝ))*Z^(17*Lcap)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
  calc
    _ ≤ Z^Lcount*(cusp^2*Z^(-((saving+Lcount)/2)))^2 := by gcongr
    _ = cusp^4*Z^(Lcount+(-((saving+Lcount)/2))*2) := by
      rw [mul_pow,←pow_mul,←Real.rpow_mul_natCast hz.le,Real.rpow_add hz]
      ring_nf
    _ = _ := by congr 2;ring
end
end SevenEighths.InverseReflectedPhase

end OAI
