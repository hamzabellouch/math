import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedResidualMajorant

namespace OAI

/-! Fixed polynomial exponents control the actual differential residual
uniformly in the source size, the site count and the coordinate extent. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem exists_manufactured_residual_parameter_offset {freq rho a d : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) (ha : 0 < a) (hd : 0 ≤ d) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s k : ℕ, k₀+7*r+72*s ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S D δ : ℝ, (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
        (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 →
        25*(k:ℝ)*Real.log N ≤ D → 0 ≤ δ → δ ≤ d*N^r/(a*(N^k)^30) →
        ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r → (∀ j, ‖u j‖ ≤ N^s) →
        δ ≤ 1 ∧ 4*(m:ℝ)^2*(∑ j,
          manufacturedOrbitalSquaredError rho H S freq δ D ((N^k)^5) u j) ≤
          ((N^k)^19)⁻¹^2 := by
  obtain ⟨C,hC,hmajor⟩ := manufacturedResidual_four_power_majorant hf hrho
  let A := 12*(PlanarSobolev.wellBound*planarWellMatrixConstant)
  let B := 768*C
  let V := 12*PlanarSobolev.wellBound^2*d^2/a^2
  let W := 12288*PlanarSobolev.wellBound^2*C
  have hwell := PlanarSobolev.wellBound_nonnegative
  have hplanar := planarWellMatrixConstant_nonnegative
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨k₁,hk₁,hsmall⟩ := exists_four_residual_norm_offset A B V W hA hB hV hW
  obtain ⟨q,_hq,hcoef⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (d/a)
  refine ⟨k₁+q+2,by omega,?_⟩
  intro r s k hk N hN H S D δ hHlo hHhi hSlo hShi hD hδ hδa m u hm hu
  let E := 7*r+72*s
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hk1 : 1 ≤ k := by omega
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hδ1 : δ ≤ 1 := by
    calc
      δ ≤ (d/a)*N^r/N^(k*30) := by
        convert hδa using 1
        rw [pow_mul]
        ring
      _ ≤ N^q*N^r/N^(k*30) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (hcoef N hN).2 (by positivity)
      _ ≤ 1 := by
        rw [div_le_one (pow_pos hN0 _),← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  refine ⟨hδ1,?_⟩
  have hmaj := hmajor (N^k) (N^s) H S D a d δ (N^r) hR (one_le_pow₀ hN1)
    hHlo hHhi hSlo hShi ha hd hδ hδ1 hδa (logarithmic_separation_residual hN k hD) m u hm hu
  change _ ≤ A*(N^r)^5/(N^k)^40+B*(N^r)^3*(N^s)^72/(N^k)^70+
    V*(N^r)^7/(N^k)^60+W*(N^r)^5*(N^s)^8/(N^k)^40 at hmaj
  have hp5 : (N^r)^5 ≤ N^E := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hp3 : (N^r)^3*(N^s)^72 ≤ N^E := by
    rw [← pow_mul,← pow_mul,← pow_add]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hp7 : (N^r)^7 ≤ N^E := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hp58 : (N^r)^5*(N^s)^8 ≤ N^E := by
    rw [← pow_mul,← pow_mul,← pow_add]
    exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have ht1 : A*(N^r)^5/(N^k)^40 ≤ A*N^E/(N^k)^40 := by gcongr
  have ht2 : B*(N^r)^3*(N^s)^72/(N^k)^70 ≤ B*N^E/(N^k)^70 := by
    rw [mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp3 hB) (by positivity)
  have ht3 : V*(N^r)^7/(N^k)^60 ≤ V*N^E/(N^k)^60 := by gcongr
  have ht4 : W*(N^r)^5*(N^s)^8/(N^k)^40 ≤ W*N^E/(N^k)^40 := by
    rw [mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp58 hW) (by positivity)
  exact hmaj.trans ((add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4).trans
    (hsmall E k (by dsimp [E]; omega) N hN))

theorem exists_manufactured_residual_parameters {freq rho a d : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) (ha : 0 < a) (hd : 0 ≤ d) (r s : ℕ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S D δ : ℝ, (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
        (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 →
        25*(k:ℝ)*Real.log N ≤ D → 0 ≤ δ → δ ≤ d*N^r/(a*(N^k)^30) →
        ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r → (∀ j, ‖u j‖ ≤ N^s) →
        δ ≤ 1 ∧ 4*(m:ℝ)^2*(∑ j,
          manufacturedOrbitalSquaredError rho H S freq δ D ((N^k)^5) u j) ≤
          ((N^k)^19)⁻¹^2 := by
  obtain ⟨q,hq,hbound⟩ := exists_manufactured_residual_parameter_offset hf hrho ha hd
  exact ⟨q+7*r+72*s,by omega,fun k hk => hbound r s k hk⟩

end ContinuumCoulomb

end

end OAI
