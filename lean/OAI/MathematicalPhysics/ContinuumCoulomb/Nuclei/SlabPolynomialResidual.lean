import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabBoxResidual

namespace OAI

/-! Uniform polynomial dependence of the finite-slab residual on the
actual well centers. All constants are chosen before the geometry. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem moment_translate_budget {M t L a : ℝ} {k j : ℕ}
    (hM : 0 ≤ M) (ht : 0 ≤ t) (hL : 1 ≤ L) (htL : t ≤ L)
    (ha : 0 ≤ a) (hkj : k ≤ j) :
    a*(M+t^k) ≤ a*(M+1)*L^j := by
  have hLj : 1 ≤ L^j := one_le_pow₀ hL
  have htj := (pow_le_pow_left₀ ht htL k).trans (pow_le_pow_right₀ hL hkj)
  calc
    _ ≤ a*(M*L^j+L^j) := mul_le_mul_of_nonneg_left
      (add_le_add (le_mul_of_one_le_right hM hLj) htj) ha
    _ = _ := by ring

theorem localized_slab_moments_polynomial {freq : ℝ} (hf : 0 < freq) (rho : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ u : PlanarPosition, ‖u‖ ≤ L →
      slabResidualSeventySecondBound rho freq u ≤ C*L^72 ∧
      localizedDensityMoment freq u 8 ≤ C*L^8 := by
  let M4 := localizedDensityMoment freq 0 4
  let M8 := localizedDensityMoment freq 0 8
  let M72 := localizedDensityMoment freq 0 72
  have h4 : 0 ≤ M4 := localizedDensityMoment_nonnegative _ _ _
  have h8 : 0 ≤ M8 := localizedDensityMoment_nonnegative _ _ _
  have h72 : 0 ≤ M72 := localizedDensityMoment_nonnegative _ _ _
  let B4 := 8*(M4+1)
  let B8 := 128*(M8+1)
  let B72 := (2:ℝ)^71*(M72+1)
  let C0 := 72*Real.pi^2*rho^2+8192*rho^2*B4+
    8*(slabGrowthConstant rho)^2*B72+8*Real.pi^2*rho^2*B72
  have hb4 : 0 ≤ B4 := by dsimp [B4]; positivity
  have hb8 : 0 ≤ B8 := by dsimp [B8]; positivity
  have hb72 : 0 ≤ B72 := by dsimp [B72]; positivity
  have hc0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨1+C0+B8,by linarith,fun L hL u hu => ?_⟩
  have hmu4 : localizedDensityMoment freq u 4 ≤ B4*L^72 :=
    (localizedDensity_fourth_moment_translate hf u).2.trans
      (moment_translate_budget h4 (norm_nonneg _) hL hu (by norm_num) (by decide : 4 ≤ 72))
  have hmu8 : localizedDensityMoment freq u 8 ≤ B8*L^8 :=
    (localizedDensity_eighth_moment_translate hf u).2.trans
      (moment_translate_budget h8 (norm_nonneg _) hL hu (by norm_num) (by decide : 8 ≤ 8))
  have hmu72 : localizedDensityMoment freq u 72 ≤ B72*L^72 :=
    (localizedDensity_seventySecond_moment_translate hf u).2.trans
      (moment_translate_budget h72 (norm_nonneg _) hL hu (by positivity) (by decide : 72 ≤ 72))
  constructor
  · have hc : 72*Real.pi^2*rho^2 ≤ 72*Real.pi^2*rho^2*L^72 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
    have hsum := add_le_add (add_le_add (add_le_add hc
      (mul_le_mul_of_nonneg_left hmu4 (by positivity : 0 ≤ 8192*rho^2)))
      (mul_le_mul_of_nonneg_left hmu72 (by positivity : 0 ≤ 8*(slabGrowthConstant rho)^2)))
      (mul_le_mul_of_nonneg_left hmu72 (by positivity : 0 ≤ 8*Real.pi^2*rho^2))
    calc
      slabResidualSeventySecondBound rho freq u ≤ C0*L^72 := by
        dsimp only [slabResidualSeventySecondBound,C0]
        nlinarith only [hsum]
      _ ≤ (1+C0+B8)*L^72 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact hmu8.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem manufacturedResidual_polynomial_geometry {freq : ℝ} (hf : 0 < freq)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T L H S δ D : ℝ), 2 ≤ T → 1 ≤ L →
      T^10 ≤ H → H ≤ 2*T^10 → T ≤ S → S ≤ 2*T →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (∀ j, ‖u j‖ ≤ L) →
      (∑ j, manufacturedOrbitalSquaredError rho H S freq δ D T u j) ≤
        3*m*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
          64*C*L^72/T^14+((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
          256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/T^8) := by
  obtain ⟨C,hC,hbound⟩ := localized_slab_moments_polynomial hf rho
  refine ⟨C,hC,fun T L H S δ D hT hL hHlo hHhi hSlo hShi m u hu => ?_⟩
  have hpoint (j : Fin m) : manufacturedOrbitalSquaredError rho H S freq δ D T u j ≤
      3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        64*C*L^72/T^14+((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/T^8) :=
    (manufacturedOrbitalSquaredError_box hrho hT
    hHlo hHhi hSlo hShi u j).trans (show _ ≤ _ from by
      obtain ⟨hs,hm⟩ := hbound L hL (u j) (hu j)
      have hs' : 64*slabResidualSeventySecondBound rho freq (u j)/T^14 ≤
          64*C*L^72/T^14 := by
        simpa only [mul_assoc] using div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 64))
          (show 0 ≤ T^14 by positivity)
      have hm' : 256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
          localizedDensityMoment freq (u j) 8/T^8 ≤
          256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/T^8 := by
        calc
          _ ≤ 256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*(C*L^8)/T^8 := by
            gcongr
          _ = _ := by ring
      linarith only [hs',hm'])
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  convert hsum using 1
  ring

end ContinuumCoulomb

end

end OAI
