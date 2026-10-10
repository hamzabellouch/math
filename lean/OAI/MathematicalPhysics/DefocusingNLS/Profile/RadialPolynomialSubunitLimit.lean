import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialUniform

namespace OAI

/-! Uniform disappearance of the polynomial odd power near a subunit constant term. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem radialPolynomial_eventually_subunit_circle (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ j, j ≤ d → Tendsto (fun n => (P n).coeff j) atTop (nhds (Q.coeff j)))
    (hzero : ‖Q.coeff 0‖ < 1) :
    ∃ ε ρ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ ε → ‖(P n).eval z‖ ≤ ρ := by
  obtain ⟨B,hB,hbound⟩ := radialPolynomial_coefficients_eventually_bounded P Q d hP
  let ρ₀ : ℝ := (‖Q.coeff 0‖+1)/2
  let ρ₁ : ℝ := (ρ₀+1)/2
  have h01 : ρ₀ < ρ₁ := by dsimp [ρ₀,ρ₁]; linarith
  have h1 : ρ₁ < 1 := by dsimp [ρ₀,ρ₁]; linarith
  have hpos : 0 ≤ ρ₁ := by dsimp [ρ₀,ρ₁]; positivity
  have h0 : ‖Q.coeff 0‖ < ρ₀ := by dsimp [ρ₀]; linarith
  have he0 : ∀ᶠ n in atTop, ‖(P n).coeff 0‖ ≤ ρ₀ :=
    ((hP 0 (Nat.zero_le _)).norm.eventually (gt_mem_nhds h0)).mono (fun _ h => h.le)
  obtain ⟨ε,hε,hε1,hcircle⟩ := exists_radialPolynomial_subunit_circle d B ρ₀ ρ₁ hB h01
  refine ⟨ε,ρ₁,hε,hε1,hpos,h1,?_⟩
  filter_upwards [hdeg,hbound,he0] with n hn hb hz z he
  exact hcircle (P n) hn hz hb z he

theorem radialPolynomialPower_uniform_limit (P : ℕ → ℂ[X]) (ε ρ : ℝ)
    (hε : 0 < ε) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP : ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ ε → ‖(P n).eval z‖ ≤ ρ) :
    TendstoUniformlyOn (fun n z => (radialPolynomialPower n (P n)).eval z)
      (fun _ => 0) atTop (Metric.closedBall (0 : ℂ) ε) := by
  have hq : ρ^2 < 1 := pow_lt_one₀ hρ hρ1 (by decide : 2 ≠ 0)
  have hh : Tendsto (fun n : ℕ => ρ^(2*n+1)) atTop (nhds 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ) hq).const_mul ρ using 1
    · funext n
      rw [pow_add,pow_one,pow_mul]
      ring
    · simp
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hP,hh.eventually (gt_mem_nhds hη)] with n hn hb z hz
  rw [dist_comm,dist_eq_norm,sub_zero]
  have hcircle : ∀ w : ℂ, ‖w‖=ε → ‖(radialPolynomialPower n (P n)).eval w‖ ≤ ρ^(2*n+1) :=
    radialPolynomialPower_circle_bound (P n) n ε ρ hρ (fun w hw => hn w hw.le)
  exact (radialPolynomial_eval_le_of_circle _ ε _ hε hcircle z
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans_lt hb

end DefocusingNLS

end OAI
