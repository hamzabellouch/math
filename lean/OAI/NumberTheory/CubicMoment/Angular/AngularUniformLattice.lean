import OAI.NumberTheory.CubicMoment.Angular.AngularUniformPoisson
import OAI.NumberTheory.CubicMoment.Angular.AngularSquarefreeLattice

namespace OAI

/-! Uniform fixed-angular cancellation on the actual primary, coprime,
squarefree lattice. Constants precede every weight and length parameter. -/
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.primaryAngularLattice_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y → ‖primaryAngularLattice ℓ (W i) Y‖ ≤ K := by
  obtain ⟨C,hC,hbound⟩ := h.primaryAngularLattice_decay hℓ
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨C*S,mul_pos hC hS,?_⟩
  intro i Y hY
  by_cases he : 1 ≤ S*Y
  · apply (hbound i Y hY).trans
    apply (div_le_iff₀ hY).mpr
    nlinarith
  · have hz : primaryAngularLattice ℓ (W i) Y = 0 := by
      have ht (u : PrimaryArgument) : theta ℓ u*W i (norm u/Y) = 0 := by
        have hn := one_le_norm (primary_ne_zero u.property)
        have hw : W i (norm u/Y) = 0 := h.upper_support i _
          ((lt_div_iff₀ hY).mpr ((lt_of_not_ge he).trans_le hn))
        simp only [hw,mul_zero]
      simp only [primaryAngularLattice,ht,tsum_zero]
    rw [hz,norm_zero]
    positivity

theorem UniformLogWeights.primaryCoprimeAngularLattice_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖primaryCoprimeAngularLattice r ℓ (W i) Y‖ ≤ K*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := h.primaryAngularLattice_bounded hℓ
  obtain ⟨D,hD,hdiv⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro i r hr hsr Y hY
  rw [primaryCoprimeAngularLattice_expansion hr hsr ℓ (W i) (h.compact i) (h.smooth i) hY]
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors r).powerset,C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      have hd : primary (∏ p ∈ s, p) := primary_finset_prod _ _
        (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
      rw [norm_mul,norm_mul,norm_theta (primary_ne_zero hd),mul_one]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
      exact hbound i _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hd)))
    _ = C*(2:ℝ)^(primaryPrimeFactors r).card := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ C*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr hsr) hC.le
    _ = _ := by ring

/-- The angular lattice model, with one constant for the
whole given smooth weight family. -/
theorem UniformLogWeights.squarefreeCoprimeAngularLattice_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 1 ≤ Y →
      ‖squarefreeCoprimeAngularLattice r ℓ (W i) Y‖ ≤ K*norm r^ε*Real.sqrt Y := by
  obtain ⟨C,hC,hbound⟩ := h.primaryCoprimeAngularLattice_bound hℓ hε
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨18*Real.sqrt S*C,by positivity,?_⟩
  intro i r hr hsr Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hNr : 0 ≤ norm r^ε := Real.rpow_nonneg (norm_nonneg r) _
  let B := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  have hcard : (B.card:ℝ) ≤ 18*Real.sqrt (S*Y) := by
    have hsub : B ⊆ nonzeroNormBall (Real.sqrt (S*Y)) := by
      intro c hc
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.sqrt_nonneg _))
  rw [squarefreeCoprimeAngularLattice_expansion r ℓ (W i) (h.compact i) (h.smooth i) hY0
    (h.upper_support i)]
  calc
    _ ≤ ∑ c ∈ B,C*norm r^ε := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      have hprim : primary (c^2) := by
        simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
          (mem_squarefreeDivisorTruncation.mp hc).1
      by_cases hcop : IsCoprime r (c^2)
      · rw [ite_eq_left hcop,norm_mul,norm_mul,norm_theta (primary_ne_zero hprim),one_mul]
        apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one c)).trans
        exact hbound i r hr hsr _ (div_pos hY0 (norm_pos_of_ne_zero (primary_ne_zero hprim)))
      · simp only [ite_eq_right hcop,mul_zero,norm_zero]
        exact mul_nonneg hC.le hNr
    _ = (B.card:ℝ)*(C*norm r^ε) := by simp
    _ ≤ (18*Real.sqrt (S*Y))*(C*norm r^ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le hNr)
    _ = _ := by rw [Real.sqrt_mul hS.le]; ring

end CubicFirstMoment

end

end OAI
