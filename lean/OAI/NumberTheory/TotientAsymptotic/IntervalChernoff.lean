import OAI.NumberTheory.TotientAsymptotic.IntervalMomentBound

namespace OAI

/-! Exponential deviation estimates for reciprocal cofactor mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma exp_small_tilt {t : ℝ} (ht : |t|≤1/4) :
    Real.exp t≤3/2 ∧ Real.exp t-1-t≤t^2 := by
  have hn : ‖t‖≤1 := by rw [Real.norm_eq_abs]; linarith
  have h := Real.norm_exp_sub_one_sub_id_le hn
  rw [Real.norm_eq_abs,Real.norm_eq_abs,sq_abs] at h
  have ht' := abs_le.mp ht
  have hsq : t^2≤(1/4:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num)).mpr ht
  have he := (abs_le.mp h).2
  constructor <;> nlinarith

/-- A single estimate handles the upper and lower tails by choosing the sign
of `t`. The mass uses every prime factor with multiplicity. -/
theorem interval_omega_chernoff : ∃ C : ℝ, 0<C ∧
    ∀ N : ℕ, 2≤N → ∀ U T : ℝ, 2≤U → U≤T → T≤N →
    ∀ t h : ℝ, |t|≤1/4 → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n≤N ∧ |t| *h≤t*((omegaIn n U T:ℝ)-(B T-B U))) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log N*
      Real.exp (t^2*(B T-B U)-|t| *h) := by
  obtain ⟨C,hC,hM⟩ := interval_omega_moment_bound
  refine ⟨C,hC,?_⟩
  intro N hN U T hU hUT hTN t h ht Q hQ
  let M := B T-B U
  let E := Real.exp (-|t| *h-t*M)
  have hM0 : 0≤M := sub_nonneg.mpr (Real.log_le_log
    (Real.log_pos (by linarith : (1:ℝ)<U))
    (Real.log_le_log (by linarith : (0:ℝ)<U) hUT))
  have htE := exp_small_tilt ht
  have hmass := hM (Real.exp t) (Real.exp_pos _).le htE.1 N hN U T hU hUT hTN Q
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hp (n : ℕ) (hn : n∈Q) : (n:ℝ)⁻¹ ≤ E*intervalOmegaWeight (Real.exp t) U T n := by
    have he : (Real.exp t)^omegaIn n U T = Real.exp (t*(omegaIn n U T:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hh : 1≤E*(Real.exp t)^omegaIn n U T := by
      rw [he,← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      dsimp [E,M]
      have := (hQ n hn).2.2
      linarith
    have hmul := mul_le_mul_of_nonneg_right hh (show 0≤(n:ℝ)⁻¹ by positivity)
    simpa only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,div_eq_mul_inv,
      mul_assoc,one_mul] using hmul
  calc
    _ ≤ E*(∑ n ∈ Q,intervalOmegaWeight (Real.exp t) U T n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hp
    _ ≤ E*(C*Real.log N*Real.exp ((Real.exp t-1)*M)) :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = C*Real.log N*Real.exp ((Real.exp t-1-t)*M-|t| *h) := by
      calc
        _ = C*Real.log N*(E*Real.exp ((Real.exp t-1)*M)) := by ring
        _ = _ := by
          dsimp [E]
          rw [← Real.exp_add]
          congr 1
          congr 1
          ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le
        (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))))
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right htE.2 hM0
      linarith

end TotientAsymptotic

end

end OAI
