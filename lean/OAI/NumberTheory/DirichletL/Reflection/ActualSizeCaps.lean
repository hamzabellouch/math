import OAI.NumberTheory.DirichletL.Reflection.TailEnergyBudget
import OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_ideal_count_polynomial (rows : Finset (Ideal Eis)) (Z H Lcap : ℝ)
    (hZ : 128≤Z) (hH : 1≤H) (hn : ∀ I∈rows,I≠0)
    (hbound : ∀ I∈rows,(Ideal.absNorm I:ℝ)≤H) (hcap : H≤Z^Lcap) :
    (rows.card:ℝ)≤Z^(Lcap+1) := by
  have hz : 0<Z := by linarith
  calc
    _ ≤ 128*H := DescentFiberCost.finite_ideal_count_real rows H hH hn hbound
    _ ≤ Z*Z^Lcap := mul_le_mul hZ hcap (by linarith) hz.le
    _ = _ := by rw [Real.rpow_add hz,Real.rpow_one];ring

lemma original_pool_restricted_norm (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) :
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  exact completed_conductor_norm_bound I Q hI hQ ((poolPrimeFamily J Q Q₀).restrict A).ideal
    ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    (fun b => poolPrimeFamily_fiber_divides J I Q Q₀ hJ hI hQ hpower hmask b.val)

lemma original_pool_restricted_cap (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (Z Li Lq : ℝ) (hZ : 0<Z)
    (hi : (Ideal.absNorm I:ℝ)≤Z^Li) (hq : (Ideal.absNorm Q:ℝ)≤Z^Lq) :
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤Z^(Li+Lq) := by
  apply (original_pool_restricted_norm J I Q Q₀ hJ hI hQ hpower hmask A).trans
  rw [Real.rpow_add hZ]
  exact mul_le_mul hi hq (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem actual_finite_source_tail_budget {a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (Lcap δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
      (rows Pset : Finset (Ideal Eis)) (Z X QK QP : ℝ),
      128≤Z → 0<X → 1≤QK → 1≤QP →
      (∀ K∈rows,K≠0 ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,P≠0 ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap →
      QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      (rows.card:ℝ)*(Pset.card*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        (Z^δ)^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹)^2≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^4*Z^(-saving) := by
  obtain ⟨A,hA⟩ := actual_row_tail_energy_budget s Lcap (Lcap+1) δ saving hδ
  refine ⟨A,?_⟩
  intro φ _ F rows Pset Z X QK QP hZ hX hQK hQP hrows hPs hF hK hP hXi
  have hz : 1≤Z := by linarith
  exact hA F Z X QK QP rows.card Pset.card hz hX (by linarith) (by linarith)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hF hK hP hXi
    (finite_ideal_count_polynomial rows Z QK Lcap hZ hQK (fun K hK => (hrows K hK).1) (fun K hK => (hrows K hK).2) hK)
    (finite_ideal_count_polynomial Pset Z QP Lcap hZ hQP (fun P hP => (hPs P hP).1) (fun P hP => (hPs P hP).2) hP)
end
end SevenEighths.InverseReflectedPhase

end OAI
