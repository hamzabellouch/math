import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedMatrixError
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialHoppingSmallness
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.RoundingPolynomialBudget

namespace OAI

/-! Polynomial budgets for the unwanted nonedge hopping and the finite
coordinate error of the rational contact realization. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_nonedge_hopping_offset {a : ℝ} (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ s p k : ℕ, q+s+p ≤ 5*k →
      ∀ N D : ℝ, 2 ≤ N → 35*(k:ℝ)*Real.log N ≤ D →
      (a*(N^k)^30)*planarHoppingUpperConstant*(2*N^s+1)*Real.exp (-D) ≤ (N^p)⁻¹ := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1)
    (3*a*planarHoppingUpperConstant)
  refine ⟨q,by omega,fun s p k hk N D hN hD => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hU : 0 ≤ planarHoppingUpperConstant := planarHoppingUpperConstant_positive.le
  have hexp : Real.exp (-D) ≤ (N^(35*k))⁻¹ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hD)).trans_eq
    rw [show -(35*(k:ℝ)*Real.log N) = -((35*k:ℕ):ℝ)*Real.log N by push_cast; ring,
      neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hN0]
  have hsize : 2*N^s+1 ≤ 3*N^s := by nlinarith [one_le_pow₀ hN1 (n := s)]
  calc
    _ ≤ (a*(N^k)^30)*planarHoppingUpperConstant*(3*N^s)*(N^(35*k))⁻¹ := by
      gcongr
    _ = (3*a*planarHoppingUpperConstant)*N^s*(N^(5*k))⁻¹ := by
      rw [← pow_mul,show 35*k=k*30+5*k by omega,pow_add,mul_inv_rev]
      field_simp
    _ ≤ N^q*N^s*(N^(5*k))⁻¹ := by
      gcongr
      exact (hbound N hN).2
    _ = (N^(5*k))⁻¹*N^(q+s) := by rw [pow_add]; ring
    _ ≤ _ := inverse_power_product_le hN1 hk

theorem coulomb_target_lipschitz_power {N τ K : ℝ} (hN : 1 ≤ N)
    (_hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hK : 0 ≤ K) {A : ℕ} (hKA : K ≤ N^A) (freq : ℝ) :
    coulombTargetLipschitzConstant freq τ K ≤
      (localizedCoulombLipschitzConstant freq/(2*Real.sqrt (localizedGramConstant freq)))*N^A := by
  let C := localizedCoulombLipschitzConstant freq/(2*Real.sqrt (localizedGramConstant freq))
  have hC : 0 ≤ C := div_nonneg (localizedCoulombLipschitzConstant_nonnegative freq) (by positivity)
  have hs : Real.sqrt K ≤ N^A := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hp := one_le_pow₀ hN (n := A)
    exact hKA.trans (by nlinarith)
  have ht := mul_le_mul hτ1 hs (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  calc
    _ = C*(τ*Real.sqrt K) := by unfold coulombTargetLipschitzConstant C; ring
    _ ≤ _ := by simpa only [one_mul,C] using mul_le_mul_of_nonneg_left ht hC

theorem exists_contact_coordinate_offset {a : ℝ} (ha : 0 < a) (freq : ℝ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ k A s p h pc : ℕ,
      q+30*k+A+s+p+1 ≤ h → p+1 ≤ pc →
      ∀ N τ K Q : ℝ, 2 ≤ N → 0 ≤ τ → τ ≤ 1 → 0 ≤ K → K ≤ N^A →
      0 ≤ Q → Q ≤ N^s →
      1/(N^pc+1) +
        ((a*(N^k)^30)*(planarHoppingLipschitzConstant : ℝ)+coulombTargetLipschitzConstant freq τ K)*
          (Q*(72*(N^h+1)⁻¹)) ≤ (N^p)⁻¹ := by
  let C := localizedCoulombLipschitzConstant freq/(2*Real.sqrt (localizedGramConstant freq))
  have hC : 0 ≤ C := div_nonneg (localizedCoulombLipschitzConstant_nonnegative freq) (by positivity)
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1)
    (72*(a*(planarHoppingLipschitzConstant : ℝ)+C))
  refine ⟨q,by omega,fun k A s p h pc hh hpc N τ K Q hN hτ hτ1 hK hKA hQ hQs => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : 0 ≤ (planarHoppingLipschitzConstant : ℝ) := by positivity
  have hcoef : (a*(N^k)^30)*(planarHoppingLipschitzConstant : ℝ)+
      coulombTargetLipschitzConstant freq τ K ≤ (a*(planarHoppingLipschitzConstant : ℝ)+C)*N^(30*k+A) := by
    have ht := coulomb_target_lipschitz_power hN1 hτ hτ1 hK hKA freq
    have h1 : (N^k)^30 ≤ N^(30*k+A) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    have h2 : N^A ≤ N^(30*k+A) := pow_le_pow_right₀ hN1 (by omega)
    have hh1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg ha.le hL)
    have hh2 := mul_le_mul_of_nonneg_left h2 hC
    change coulombTargetLipschitzConstant freq τ K ≤ C*N^A at ht
    calc
      _ ≤ (a*(planarHoppingLipschitzConstant : ℝ))*N^(30*k+A)+C*N^(30*k+A) :=
        add_le_add (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hh1) (ht.trans hh2)
      _ = _ := by ring
  have hcoord : ((a*(N^k)^30)*(planarHoppingLipschitzConstant : ℝ)+
      coulombTargetLipschitzConstant freq τ K)*(Q*(72*(N^h+1)⁻¹)) ≤ (N^(p+1))⁻¹ := by
    have hden : (N^h+1)⁻¹ ≤ (N^h)⁻¹ := inv_anti₀ (pow_pos hN0 h) (by linarith)
    calc
      _ ≤ ((a*(planarHoppingLipschitzConstant : ℝ)+C)*N^(30*k+A))*(N^s*(72*(N^h)⁻¹)) := by
        gcongr
      _ = (72*(a*(planarHoppingLipschitzConstant : ℝ)+C))*N^(30*k+A+s)*(N^h)⁻¹ := by
        rw [pow_add]; ring
      _ ≤ N^q*N^(30*k+A+s)*(N^h)⁻¹ := by
        gcongr
        exact (hbound N hN).2
      _ = (N^h)⁻¹*N^(q+30*k+A+s) := by rw [show q+30*k+A+s=q+(30*k+A+s) by omega,pow_add]; ring
      _ ≤ _ := inverse_power_product_le hN1 (by omega)
  have hnom : 1/(N^pc+1) ≤ (N^(p+1))⁻¹ := by
    calc
      _ ≤ (N^pc)⁻¹ := by simpa only [one_div] using
        one_div_le_one_div_of_le (pow_pos hN0 pc) (show N^pc ≤ N^pc+1 by linarith)
      _ ≤ _ := inv_anti₀ (pow_pos hN0 (p+1)) (pow_le_pow_right₀ hN1 hpc)
  have htwo : 2*(N^(p+1))⁻¹ ≤ (N^p)⁻¹ := by
    rw [pow_succ]
    have hn := inv_anti₀ (by norm_num : (0:ℝ)<2) hN
    rw [mul_inv_rev]
    nlinarith [mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (N^p)⁻¹)]
  linarith

end ContinuumCoulomb

end

end OAI
