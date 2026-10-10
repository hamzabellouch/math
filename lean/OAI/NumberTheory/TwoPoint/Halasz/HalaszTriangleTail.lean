import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseConjugation

namespace OAI

/-! Summable nonstationary tails of the smoothed logarithmic kernel. -/
namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_triangle_boundary_bound (N u v lam : ℝ) (hN : 0 < N) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc (N/2) (5*N/2), lam ≤ |halaszLogSlope u v x|) :
    ‖((2/N:ℝ):ℂ) *
      (2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 -
        halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2 -
        halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2)‖ ≤
      8/(N*lam^2) := by
  have hp (x : ℝ) (hx : x ∈ Set.Icc (N/2) (5*N/2)) :
      ‖halaszLogPhase u v x/(halaszLogSlope u v x:ℂ)^2‖ ≤ 1/lam^2 := by
    simp only [norm_div, norm_pow, halasz_log_phase_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact hs x hx
  have hpa := hp (N/2) ⟨le_rfl, by linarith⟩
  have hpb := hp (3*N/2) ⟨by linarith, by linarith⟩
  have hpc := hp (5*N/2) ⟨by linarith, le_rfl⟩
  have he : 2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 =
      2*(halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2) := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hN), he]
  have hb := norm_sub_le
    (2*(halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2) -
      halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2)
    (halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2)
  have hb' := norm_sub_le
    (2*(halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2))
    (halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2)
  rw [norm_mul] at hb'
  have htwo : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
  rw [htwo] at hb'
  calc
    _ ≤ (2/N)*(4/lam^2) := by
      gcongr
      simp only [div_eq_mul_inv] at hb hb' hpa hpb hpc ⊢
      linarith
    _ = _ := by ring

lemma halasz_triangle_remainder_bound (N u v lam : ℝ) (hN : 0 < N) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc (N/2) (5*N/2), lam ≤ |halaszLogSlope u v x|) :
    ‖(∫ x in N/2..3*N/2, (halaszLogAmplitude2Deriv u v (2/N) (-1) x:ℂ)*
        halaszLogPhase u v x) +
       ∫ x in 3*N/2..5*N/2, (halaszLogAmplitude2Deriv u v (-(2/N)) 5 x:ℂ)*
        halaszLogPhase u v x‖ ≤
      112*|u| /(N^2*lam^3) + 192*u^2/(N^3*lam^4) := by
  have h1 := halasz_log_remainder_integral u v (2/N) (-1) (N/2) (N/2) (3*N/2) lam 2
    (by positivity) le_rfl (by linarith) hlam
    (fun x hx => hs x ⟨hx.1, by linarith [hx.2]⟩) (by
      intro x hx
      apply abs_le.mpr
      have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  have h2 := halasz_log_remainder_integral u v (-(2/N)) 5 (N/2) (3*N/2) (5*N/2) lam 2
    (by positivity) (by linarith) (by linarith) hlam
    (fun x hx => hs x ⟨by linarith [hx.1], hx.2⟩) (by
      intro x hx
      apply abs_le.mpr
      have he : (-(2/N)*x)*N = -2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  have hpos : 0 < 2/N := by positivity
  rw [abs_of_pos hpos] at h1
  rw [abs_neg, abs_of_pos hpos] at h2
  have he :
      (3*(2/N)*|u| /((N/2)^2*lam^3) + 2*2*|u| /((N/2)^3*lam^3) +
        3*2*u^2/((N/2)^4*lam^4))*(3*N/2-N/2) +
      (3*(2/N)*|u| /((N/2)^2*lam^3) + 2*2*|u| /((N/2)^3*lam^3) +
        3*2*u^2/((N/2)^4*lam^4))*(5*N/2-3*N/2) =
      112*|u| /(N^2*lam^3) + 192*u^2/(N^3*lam^4) := by
    field_simp
    ring
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq he)

theorem halasz_triangle_nonstationary (N u v lam : ℝ) (hN : 0 < N) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc (N/2) (5*N/2), lam ≤ |halaszLogSlope u v x|) :
    ‖halaszTriangleIntegral N u v‖ ≤ 8/(N*lam^2) +
      112*|u| /(N^2*lam^3) + 192*u^2/(N^3*lam^4) := by
  rw [halasz_triangle_double_integral N u v hN (by
    intro x hx
    exact abs_pos.mp (hlam.trans_le (hs x hx)))]
  exact (norm_sub_le _ _).trans (by
    have h1 := halasz_triangle_boundary_bound N u v lam hN hlam hs
    have h2 := halasz_triangle_remainder_bound N u v lam hN hlam hs
    linarith)

end TwoPointCorrelations

end OAI
