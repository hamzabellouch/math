import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteBoxMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabPolynomialResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialConstantBounds

namespace OAI

/-! The retained counterterm has only a vertical truncation error. The
seventy-second slab moment makes its matrix error small after amplification. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem finiteBoxSquaredError_box {rho R H S freq δ : ℝ}
    (hrho : 0 ≤ rho) (hR : 2 ≤ R)
    (hHlo : R^50 ≤ H) (hHhi : H ≤ 2*R^50)
    (hSlo : R^5 ≤ S) (hShi : S ≤ 2*R^5)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    finiteBoxOrbitalSquaredError rho H S freq δ (R^5) u j ≤
      128*slabResidualSeventySecondBound rho freq (u j)/R^70+
        2^27*(m:ℝ)^2*PlanarSobolev.wellBound^2*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^120 := by
  have hR0 : 0 < R := by linarith
  have hW := PlanarSobolev.wellBound_nonnegative
  have hT : 2 ≤ R^5 := hR.trans (le_self_pow₀ (by linarith) (by decide : 5 ≠ 0))
  have htail := slabSeventySecondTail_box_bound (freq := freq) hrho hT
    (by simpa only [← pow_mul] using hHlo) (by simpa only [← pow_mul] using hHhi)
    hSlo hShi (u j)
  have hM : 0 ≤ ∫ x : Position, ‖x‖^24*continuumLocalizedMode freq 0 x^2 :=
    integral_nonneg (fun x => mul_nonneg (by positivity) (sq_nonneg _))
  have hw : ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(S/2)^24*
      (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) ≤
      2^26*(m:ℝ)^2*PlanarSobolev.wellBound^2*
        (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^120 := by
    calc
      _ ≤ ((m:ℝ)*2*PlanarSobolev.wellBound)^2/(R^5/2)^24*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) := by
        gcongr
        linarith
      _ = _ := by field_simp [ne_of_gt hR0]
  unfold finiteBoxOrbitalSquaredError
  rw [show (R^5)^14 = R^70 by rw [← pow_mul]] at htail
  have h := mul_le_mul_of_nonneg_left (add_le_add htail hw) (by norm_num : (0:ℝ) ≤ 2)
  convert h using 1
  ring

theorem finiteBoxSquaredError_polynomial {freq rho : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R L H S δ : ℝ, 2 ≤ R → 1 ≤ L →
      R^50 ≤ H → H ≤ 2*R^50 → R^5 ≤ S → S ≤ 2*R^5 →
      0 ≤ δ → δ ≤ 1 → ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ j, ‖u j‖ ≤ L) → ∀ j,
      finiteBoxOrbitalSquaredError rho H S freq δ (R^5) u j ≤
        C*(L^72/R^70+(m:ℝ)^2/R^120) := by
  obtain ⟨A,hA,hbound⟩ := localized_slab_moments_polynomial hf rho
  let B := (2:ℝ)^27*PlanarSobolev.wellBound^2*
    (∫ x : Position, ‖x‖^24*continuumLocalizedMode freq 0 x^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C := 1+128*A+B
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,hC,fun R L H S δ hR hL hHlo hHhi hSlo hShi hδ hδ1 m u hu j => ?_⟩
  apply (finiteBoxSquaredError_box hrho hR hHlo hHhi hSlo hShi hδ hδ1 u j).trans
  have hs := mul_le_mul_of_nonneg_left (hbound L hL (u j) (hu j)).1 (by norm_num : (0:ℝ) ≤ 128)
  have hs' := div_le_div_of_nonneg_right hs (show 0 ≤ R^70 by positivity)
  have hca : 128*A ≤ C := by dsimp [C]; linarith
  have hcb : B ≤ C := by dsimp [C]; nlinarith
  have h1 := mul_le_mul_of_nonneg_right hca (show 0 ≤ L^72/R^70 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hcb (show 0 ≤ (m:ℝ)^2/R^120 by positivity)
  calc
    _ ≤ 128*(A*L^72)/R^70+
        2^27*(m:ℝ)^2*PlanarSobolev.wellBound^2*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)/R^120 := add_le_add hs' le_rfl
    _ = 128*A*(L^72/R^70)+B*((m:ℝ)^2/R^120) := by dsimp [B]; ring
    _ ≤ C*(L^72/R^70)+C*((m:ℝ)^2/R^120) := add_le_add h1 h2
    _ = _ := by ring

theorem exists_finiteBoxResidual_parameter_offset {freq rho : ℝ}
    (hf : 0 < freq) (hrho : 0 ≤ rho) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r s k : ℕ, k₀+2*r+72*s ≤ k →
      ∀ N H S δ : ℝ, 2 ≤ N →
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 0 ≤ δ → δ ≤ 1 →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r →
      (∀ j, ‖u j‖ ≤ N^s) → ∀ j,
      finiteBoxOrbitalSquaredError rho H S freq δ ((N^k)^5) u j ≤
        ((N^k)^32)⁻¹^2 := by
  obtain ⟨C,hC,hbound⟩ := finiteBoxSquaredError_polynomial hf hrho
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1) (2*C)
  refine ⟨q+1,by omega,fun r s k hk N H S δ hN hHlo hHhi hSlo hShi hδ hδ1 m u hm hu j => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  apply (hbound (N^k) (N^s) H S δ hR (one_le_pow₀ hN1)
    hHlo hHhi hSlo hShi hδ hδ1 m u hu j).trans
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hpow : (N^k)^70 ≤ (N^k)^120 := pow_le_pow_right₀ hR1 (by decide)
  have hm2 : (m:ℝ)^2 ≤ N^(2*r+72*s) := calc
    _ ≤ (N^r)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2
    _ ≤ N^(2*r+72*s) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
  have hL : (N^s)^72 ≤ N^(2*r+72*s) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by omega)
  calc
    C*((N^s)^72/(N^k)^70+(m:ℝ)^2/(N^k)^120) ≤
        C*(N^(2*r+72*s)/(N^k)^70+N^(2*r+72*s)/(N^k)^70) := by gcongr
    _ = 2*C*N^(2*r+72*s)/(N^k)^70 := by ring
    _ ≤ N^q*N^(2*r+72*s)/(N^k)^70 := by
      gcongr
      exact (hconst N hN).2
    _ ≤ 1/(N^k)^64 := by
      rw [div_le_div_iff₀ (by positivity : 0 < (N^k)^70) (by positivity : 0 < (N^k)^64),
        one_mul,← pow_add,← pow_mul,← pow_add,← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    _ = _ := by simp only [one_div,inv_pow,← pow_mul,Nat.mul_assoc]

end ContinuumCoulomb

end

end OAI
