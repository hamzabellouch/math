import OAI.NumberTheory.TwoPoint.Halasz.HalaszOscillationBounds

namespace OAI

/-! The compact triangular majorant used for a dyadic Dirichlet kernel. -/
namespace TwoPointCorrelations

open MeasureTheory

noncomputable def halaszTriangleIntegral (N u v : ℝ) : ℂ :=
  (∫ x in N/2..3*N/2, ((2/N*x-1:ℝ):ℂ)*halaszLogPhase u v x) +
  (∫ x in 3*N/2..5*N/2, ((-(2/N)*x+5:ℝ):ℂ)*halaszLogPhase u v x)

lemma halasz_triangle_stationary (N u v : ℝ) (hN : 0 < N) (hu : 0 < u) :
    ‖halaszTriangleIntegral N u v‖ ≤ 110*N/Real.sqrt u := by
  have h1 := halasz_log_stationary_affine u v (N/2) (3*N/2) (2/N) (-1) hu
    (by positivity) (by linarith)
  have h2 := halasz_log_stationary_affine u v (3*N/2) (5*N/2) (-(2/N)) 5 hu
    (by positivity) (by linarith)
  have he1 : 2/N*(3*N/2)+(-1) = 2 := by field_simp [hN.ne']; ring
  have he2 : -(2/N)*(5*N/2)+5 = 0 := by field_simp [hN.ne']; ring
  have he3 : |2/N| = 2/N := abs_of_pos (by positivity)
  have he4 : |-(2/N)| = 2/N := by rw [abs_neg, he3]
  rw [he1, he3, abs_of_pos (by norm_num : (0:ℝ)<2)] at h1
  rw [he2, he4, abs_zero] at h2
  have hr1 : (2+2/N*(3*N/2-N/2))*(10*(3*N/2)/Real.sqrt u) =
      60*N/Real.sqrt u := by field_simp [hN.ne']; ring
  have hr2 : (0+2/N*(5*N/2-3*N/2))*(10*(5*N/2)/Real.sqrt u) =
      50*N/Real.sqrt u := by field_simp [hN.ne']; ring
  rw [hr1] at h1
  rw [hr2] at h2
  exact (norm_add_le _ _).trans (by
    change ‖_‖ + ‖_‖ ≤ _
    simp only [sub_eq_add_neg, div_eq_mul_inv] at h1 h2 ⊢
    linarith)

lemma halasz_triangle_boundary (N u v : ℝ) (hN : 0 < N) :
    halaszLogDoublePrimitive u v (2/N) (-1) (3*N/2) -
      halaszLogDoublePrimitive u v (2/N) (-1) (N/2) +
      halaszLogDoublePrimitive u v (-(2/N)) 5 (5*N/2) -
      halaszLogDoublePrimitive u v (-(2/N)) 5 (3*N/2) =
    ((2/N:ℝ):ℂ) *
      (2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 -
        halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2 -
        halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2) := by
  have hLa : 2/N*(N/2)+(-1) = 0 := by field_simp [hN.ne']; ring
  have hLb : 2/N*(3*N/2)+(-1) = 2 := by field_simp [hN.ne']; ring
  have hRb : -(2/N)*(3*N/2)+5 = 2 := by field_simp [hN.ne']; ring
  have hRc : -(2/N)*(5*N/2)+5 = 0 := by field_simp [hN.ne']; ring
  unfold halaszLogDoublePrimitive halaszLogAmplitude0 halaszLogAmplitude2
  rw [hLa, hLb, hRb, hRc]
  push_cast
  ring

theorem halasz_triangle_double_integral (N u v : ℝ) (hN : 0 < N)
    (hd : ∀ x ∈ Set.Icc (N/2) (5*N/2), halaszLogSlope u v x ≠ 0) :
    halaszTriangleIntegral N u v =
      ((2/N:ℝ):ℂ) *
        (2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 -
          halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2 -
          halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2) -
      ((∫ x in N/2..3*N/2, (halaszLogAmplitude2Deriv u v (2/N) (-1) x:ℂ)*
        halaszLogPhase u v x) +
       ∫ x in 3*N/2..5*N/2, (halaszLogAmplitude2Deriv u v (-(2/N)) 5 x:ℂ)*
        halaszLogPhase u v x) := by
  have h1 := halasz_log_double_integral u v (2/N) (-1) (N/2) (3*N/2)
    (by positivity) (by linarith) (fun x hx => hd x ⟨hx.1, by linarith [hx.2]⟩)
  have h2 := halasz_log_double_integral u v (-(2/N)) 5 (3*N/2) (5*N/2)
    (by positivity) (by linarith) (fun x hx => hd x ⟨by linarith [hx.1], hx.2⟩)
  have he := halasz_triangle_boundary N u v hN
  dsimp only [halaszTriangleIntegral]
  simp only [sub_eq_add_neg] at h1 h2 he ⊢
  rw [h1, h2]
  linear_combination he

end TwoPointCorrelations

end OAI
