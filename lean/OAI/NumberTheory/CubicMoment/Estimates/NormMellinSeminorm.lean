import OAI.NumberTheory.CubicMoment.Estimates.NormFourierSeminorm
import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! Uniform finite-profile control of the actual full Mellin-line moments. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment

theorem normDenominatorMellinCoefficient_moment_control (M : ℝ) (hM : 0 < M) (A B : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
        (ρ : ℝ), 0 ≤ ρ →
      (1+ρ)^A*(∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz W hW hW') := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k*∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  obtain ⟨I₀,C₀,hC₀,h₀⟩ := normDenominatorFourier_seminorm_control M hM 0 0 (2*A)
  obtain ⟨I₁,C₁,hC₁,h₁⟩ := normDenominatorFourier_seminorm_control M hM (B+k) 0 (2*A)
  let I := I₀ ∪ I₁
  refine ⟨I,D*(C₀+C₁)+1,by positivity,?_⟩
  intro W hW hW' ρ hρ
  let F := normProfileFourierSchwartz W hW hW'
  let S := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have hsup₀ : (I₀.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) F
  have hsup₁ : (I₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) F
  have hc₀ := (h₀ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₀ hC₀.le)
  have hc₁ := (h₁ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₁ hC₁.le)
  rw [←normDenominatorLogSchwartz_eq_annular] at hc₀ hc₁
  calc
    _ ≤ (1+Real.sqrt ρ)^(2*A)*(D*
        (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
         SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
      mul_le_mul hs h (integral_nonneg (fun _ => by positivity)) (by positivity)
    _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
      (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
    _ ≤ D*(C₀*S+C₁*S) := mul_le_mul_of_nonneg_left (add_le_add hc₀ hc₁) hD
    _ ≤ (D*(C₀+C₁)+1)*S := by nlinarith

end CubicFirstMoment

end

end OAI
