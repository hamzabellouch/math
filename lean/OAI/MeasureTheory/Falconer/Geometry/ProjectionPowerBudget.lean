import OAI.MeasureTheory.Falconer.Geometry.ProjectionSampleBudget

namespace OAI

/-! The explicit quadratic depth loss in projection sampling fits into
any prescribed positive dyadic power, uniformly over a fixed exponent gap. -/
namespace Falconer

theorem dyadic_quadratic_loss {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*((N:ℝ)+1)^2 ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  let a := η*Real.log 2
  have ha : 0 < a := mul_pos hη (Real.log_pos (by norm_num))
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1 (24*C/a^3))
  have hN01 : (1:ℝ) ≤ N0 := (le_max_left _ _).trans hN0.le
  refine ⟨N0,by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN01),?_⟩
  intro N hN
  have hNN : (N0:ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN1 : (1:ℝ) ≤ N := hN01.trans hNN
  have hscale : 24*C ≤ a^3*(N:ℝ) := by
    have hh := (le_max_right _ _).trans (hN0.le.trans hNN)
    have he := (div_le_iff₀ (pow_pos ha 3)).1 hh
    nlinarith only [he]
  have hsize : ((N:ℝ)+1)^2 ≤ (2*(N:ℝ))^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hN1]) 2
  have hcub := mul_le_mul_of_nonneg_right hscale (sq_nonneg (N:ℝ))
  calc
    _ ≤ C*(2*(N:ℝ))^2 := mul_le_mul_of_nonneg_left hsize hC
    _ ≤ (a*(N:ℝ))^3/6 := by nlinarith only [hcub]
    _ ≤ Real.exp (a*(N:ℝ)) := by
      simpa only [Nat.factorial_succ,Nat.factorial_zero,Nat.reduceAdd,Nat.reduceMul,
        Nat.cast_ofNat] using Real.pow_div_factorial_le_exp (a*(N:ℝ))
          (by positivity : 0 ≤ a*(N:ℝ)) 3
    _ = _ := by congr 1; dsimp [a]; ring

theorem projection_sample_power_budget {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let D := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ s t KI KP ρ : ℝ, s ≤ 1 → κ ≤ t-s →
        0 ≤ KI → 0 ≤ KP → KI ≤ D → KP ≤ D → 1/D ≤ ρ →
        projectedSubsetSampleConstant N s t KI KP ρ ≤
          Real.exp (θ*(N:ℝ)*Real.log 2) := by
  let H := projectionGapConstant κ
  let G := 512*(64*Real.exp 1*(1+32*H)+100)^2
  have hH : 0 < H := projectionGapConstant_pos hκ
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_quadratic_loss (by positivity : 0 < θ/2)
    (show 0 ≤ G by dsimp [G]; positivity)
  refine ⟨θ/16,N0,by positivity,hN0,?_⟩
  intro N hN
  dsimp only
  intro s t KI KP ρ hs hgap hKI hKP hKIup hKPup hρlow
  let D := Real.exp ((θ/16)*(N:ℝ)*Real.log 2)
  have hD0 : 0 < D := Real.exp_pos _
  have hD1 : 1 ≤ D := Real.one_le_exp_iff.mpr (by positivity)
  have hρ : 0 < ρ := (one_div_pos.mpr hD0).trans_le hρlow
  have hst : s < t := by linarith only [hκ,hgap]
  have hbound := projectedSubsetSampleConstant_upper N hst hs hKI hKP hD1
    hKIup hKPup hρ hρlow hH.le (planarPotentialConstant_gap hκ hs hgap)
  have hDpow : D^8 = Real.exp ((θ/2)*(N:ℝ)*Real.log 2) := by
    dsimp [D]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ G*((N:ℝ)+1)^2*D^8 := hbound
    _ ≤ Real.exp ((θ/2)*(N:ℝ)*Real.log 2)*D^8 :=
      mul_le_mul_of_nonneg_right (hpoly N hN) (pow_nonneg hD0.le 8)
    _ = Real.exp (θ*(N:ℝ)*Real.log 2) := by
      rw [hDpow,← Real.exp_add]
      congr 1
      ring

end Falconer

end OAI
