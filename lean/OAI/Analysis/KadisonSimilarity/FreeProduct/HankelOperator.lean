import OAI.Analysis.KadisonSimilarity.FreeProduct.HankelBounds

namespace OAI

/-! The narrow-arc Hankel test on an arbitrary complex Hilbert space. -/

noncomputable section

namespace KadisonSimilarity

open Finset

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A finite orthonormal compression with entries bounded below forces an
operator-norm lower bound. The ambient Hilbert space may be infinite-dimensional. -/
theorem norm_lower_of_orthonormal_coefficients {N : ℕ} (hN : 0 < N)
    (T : H →L[ℂ] H) (e : Fin N → H) (he : Orthonormal ℂ e) {c : ℝ}
    (hcoeff : ∀ j k, c ≤ (inner ℂ (e j) (T (e k))).re) :
    N * c ≤ ‖T‖ := by
  let v : H := ∑ i : Fin N, e i
  have hv : ‖v‖ ^ 2 = (N : ℝ) := by
    have hi : inner ℂ v v = (N : ℂ) := by
      dsimp [v]
      simp only [sum_inner, inner_sum, orthonormal_iff_ite.mp he]
      simp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hi]
    simp
  have hlow : (N : ℝ) * ((N : ℝ) * c) ≤ (inner ℂ v (T v)).re := by
    calc
      (N : ℝ) * ((N : ℝ) * c) = ∑ _j : Fin N, ∑ _k : Fin N, c := by simp
      _ ≤ ∑ j : Fin N, ∑ k : Fin N, (inner ℂ (e j) (T (e k))).re := by
        apply Finset.sum_le_sum
        intro j _
        exact Finset.sum_le_sum fun k _ => hcoeff j k
      _ = (inner ℂ v (T v)).re := by
        simp only [v, map_sum, sum_inner, inner_sum, Complex.re_sum]
        exact Finset.sum_comm
  have hupp : (inner ℂ v (T v)).re ≤ ‖T‖ * N := by
    calc
      _ ≤ ‖v‖ * ‖T v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖v‖ * (‖T‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg v)
      _ = ‖T‖ * N := by rw [← hv]; ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact (mul_le_mul_iff_right₀ hNr).mp (by nlinarith [hlow.trans hupp])

/-- A compression with the actual narrow-arc Fourier coefficients has a
uniform lower bound, independently of the ambient space and `N`. -/
theorem norm_lower_of_arcHankelCompression {N : ℕ} (hN : 0 < N)
    (T : H →L[ℂ] H) (e : Fin N → H) (he : Orthonormal ℂ e)
    (hcoeff : ∀ j k, (inner ℂ (e j) (T (e k))).re = arcHankelMatrix N j k) :
    1 / Real.pi ^ 2 ≤ ‖T‖ := by
  have h := norm_lower_of_orthonormal_coefficients hN T e he
    (fun j k => (arcHankelMatrix_entry_lower hN j k).trans_eq (hcoeff j k).symm)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert h using 1
  unfold arcWidth
  field_simp

end KadisonSimilarity

end

end OAI
