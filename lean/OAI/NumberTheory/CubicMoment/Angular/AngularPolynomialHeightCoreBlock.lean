import OAI.NumberTheory.CubicMoment.Angular.AngularLargeCoreBlockMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularSmallCoreBlockMoment
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The large-core bound extends to the fixed polynomial height window
needed before taking the rapidly decreasing Mellin tails. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_uniform_core_block_polynomial_height (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (C T₀ : ℝ) (A : ℕ), 0 < C ∧
    ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ) (e : Eisenstein) (u : ℝ)
      (H : Finset Eisenstein), T₀ ≤ L r →
      (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
      0 ≤ B → B ≤ (L r)^(1+η) → coreDyadicConductor i j ≤ B →
      (1+Real.log (L r))^A ≤ 8*coreDyadicConductor i j →
      e ≠ 0 → norm e ≤ (L r)^σ → 1+|u| ≤ (L r)^(9/25:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,CL,ν,hη,hη₁,hσ,hCL,hν,hlarge⟩ :=
    angular_large_core_block_moment ℓ (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR
      (by norm_num : (0:ℝ) < 1/4) hGI hGQ
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨TS,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨CS,A,hCS,hsmall⟩ := angular_small_core_block_log_saving ℓ hHuxley hW hR hlo hhi k
  have hev := (eventually_ge_atTop TS).and ((negative_power_log_saving hν k).and
    (eventually_const_mul_rpow_le
      (by norm_num : (1/2:ℝ) < 1) 16))
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp hev
  refine ⟨max CS CL,T₀,A,lt_of_lt_of_le hCS (le_max_left _ _),?_⟩
  intro r X B i j e u H hT₀ hprod hX hB hBL hDB hcut he heN hu hH
  obtain ⟨hTS,hneg,hmargin⟩ := hT (L r) hT₀
  have hXone : ∀ a, 1 ≤ X a := fun a =>
    (Real.one_le_rpow (by linarith [hL r] : 1 ≤ 2*L r) hc.le).trans (hX a).le
  have hz : 0 ≤ (1+Real.log (L r))^k := pow_nonneg (by linarith [Real.log_nonneg (hL r)]) _
  have hbase : 0 ≤ (L r)^2*B^(1/3:ℝ) := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hB _)
  by_cases hD : coreDyadicConductor i j ≤ (L r)^(1/4:ℝ)
  · have hm := hsmall r X B i j 1 e u H (hL r) hXone hprod hB
      (small_core_ordinary_window (zero_le_one.trans (hL r))
        (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hD
        (by simpa only [Real.rpow_one] using hmargin)) hcut hH
    apply hm.trans
    apply div_le_div_of_nonneg_right _ hz
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left CS CL) hbase]
  · have hm := hlarge r X B i j 1 e u H hTS hprod hX hB hBL hDB
      (le_of_not_ge hD) one_ne_zero he
      (by simpa only [norm_one_eq] using Real.one_le_rpow (hL r) hσ.le) heN
      hu hH
    apply hm.trans
    calc
      _ ≤ CL*(L r)^2*B^(1/3:ℝ)*(1/(1+Real.log (L r))^k) :=
        mul_le_mul_of_nonneg_left hneg (mul_nonneg (mul_nonneg hCL.le (sq_nonneg _))
          (Real.rpow_nonneg hB _))
      _ = CL*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hz
        nlinarith [mul_le_mul_of_nonneg_right (le_max_right CS CL) hbase]

end CubicFirstMoment

end

end OAI
