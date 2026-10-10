import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialCoefficientLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingPolynomialLimit

namespace OAI

/-! Uniform polynomial estimates needed for the normalized outgoing residual.
High polynomial degrees of the nonlinear coefficients are allowed. -/

open Filter Topology Set Polynomial
namespace DefocusingNLS

theorem spectralPolynomial_subunit_uniform_limit (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)))
    (hzero : ‖Q.coeff 0‖ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      TendstoUniformlyOn (fun n z => (spectralDiagonalPolynomial n (P n)).eval z) (fun _ => 0)
        atTop (Metric.closedBall (0 : ℂ) ε) ∧
      TendstoUniformlyOn (fun n z => (spectralCrossPolynomial n (P n)).eval z) (fun _ => 0)
        atTop (Metric.closedBall (0 : ℂ) ε) := by
  obtain ⟨ε,ρ,hε,hε1,hρ,hρ1,hcircle⟩ :=
    radialPolynomial_eventually_subunit_circle P Q d hdeg hP hzero
  have hδ := spectralSubunitCoefficient_decay ρ hρ hρ1
  refine ⟨ε,hε,hε1,?_,?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    filter_upwards [hcircle,eventually_ge_atTop 1,hδ.eventually (gt_mem_nhds hη)] with n hn hmn hd z hz
    rw [dist_zero_left]
    exact (radialPolynomial_eval_le_of_circle _ ε _ hε
      (fun w hw => (spectralPolynomial_circle_bound (P n) n hmn ε ρ hρ
        (fun v hv => hn v hv.le) w hw).1) z
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans_lt hd
  · rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    filter_upwards [hcircle,eventually_ge_atTop 1,hδ.eventually (gt_mem_nhds hη)] with n hn hmn hd z hz
    rw [dist_zero_left]
    exact (radialPolynomial_eval_le_of_circle _ ε _ hε
      (fun w hw => (spectralPolynomial_circle_bound (P n) n hmn ε ρ hρ
        (fun v hv => hn v hv.le) w hw).2) z
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans_lt hd

theorem spectralPolynomial_mul_uniform_zero (A U : ℕ → ℂ[X]) (U₀ : ℂ[X])
    (d : ℕ) (ε : ℝ) (hε : ε ≤ 1)
    (hA : TendstoUniformlyOn (fun n z => (A n).eval z) (fun _ => 0)
      atTop (Metric.closedBall (0 : ℂ) ε))
    (hdeg : ∀ᶠ n in atTop, (U n).natDegree ≤ d)
    (hU : ∀ k, k ≤ d → Tendsto (fun n => (U n).coeff k) atTop (𝓝 (U₀.coeff k))) :
    TendstoUniformlyOn (fun n z => (A n*U n).eval z) (fun _ => 0)
      atTop (Metric.closedBall (0 : ℂ) ε) := by
  obtain ⟨B,hB,hcoeff⟩ := radialPolynomial_coefficients_eventually_bounded U U₀ d hU
  let C := ((d+1 : ℕ) : ℝ)*B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have heval : ∀ᶠ n in atTop, ∀ z ∈ Metric.closedBall (0 : ℂ) ε, ‖(U n).eval z‖ ≤ C := by
    filter_upwards [hdeg,hcoeff] with n hn hc z hz
    have hz1 : ‖z‖ ≤ 1 := (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz : ‖z‖ ≤ ε).trans hε
    calc
      _ ≤ ∑ k ∈ Finset.range (d+1), ‖(U n).coeff k‖ := radialPolynomial_eval_sum_bound _ d hn z hz1
      _ ≤ ∑ k ∈ Finset.range (d+1), B := Finset.sum_le_sum (fun k hk => hc k (by
        have := Finset.mem_range.mp hk
        omega))
      _ = C := by simp [C]
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hηC : 0 < η/(C+1) := div_pos hη (by linarith)
  filter_upwards [heval,(Metric.tendstoUniformlyOn_iff.mp hA) (η/(C+1)) hηC] with n hn ha z hz
  have ha' : ‖(A n).eval z‖ < η/(C+1) := by simpa only [dist_zero_left] using ha z hz
  have hh : ‖(A n).eval z‖*(C+1) < η := (lt_div_iff₀ (by linarith)).mp ha'
  rw [dist_zero_left,eval_mul,norm_mul]
  calc
    _ ≤ ‖(A n).eval z‖*C := mul_le_mul_of_nonneg_left (hn z hz) (norm_nonneg _)
    _ ≤ ‖(A n).eval z‖*(C+1) := by gcongr; linarith
    _ < η := hh

theorem spectralPolynomial_star_uniform_zero (A : ℕ → ℂ[X]) (ε : ℝ)
    (hA : TendstoUniformlyOn (fun n z => (A n).eval z) (fun _ => 0)
      atTop (Metric.closedBall (0 : ℂ) ε)) :
    TendstoUniformlyOn (fun n z => (Polynomial.mapRingHom (starRingEnd ℂ) (A n)).eval z)
      (fun _ => 0) atTop (Metric.closedBall (0 : ℂ) ε) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hA) η hη] with n hn z hz
  have he : (Polynomial.mapRingHom (starRingEnd ℂ) (A n)).eval z=star ((A n).eval (star z)) := by
    simpa using (Polynomial.eval_map_apply (p := A n) (starRingEnd ℂ) (star z))
  rw [dist_zero_left,he,norm_star]
  have hz' : star z ∈ Metric.closedBall (0 : ℂ) ε := by
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_star] using hz
  simpa only [dist_zero_left] using hn (star z) hz'

end DefocusingNLS

end OAI
