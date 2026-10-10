import OAI.Geometry.SurfaceImmersion.Primitive.UniformCrossingBounds

namespace OAI

/-! Choose the crossing threshold before the longitudinal curvature term. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma quadratic_dominates_linear (A P Q R : ℝ)
    (hA : 0 < A) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    ∃ H : ℝ, 0 < H ∧ ∀ N : ℝ, H < |N| → R < N^2/A-Q-P*|N| := by
  let H := max 1 (A*(P+Q+R+1))
  refine ⟨H,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro N hN
  have hx1 : 1 < |N| := (le_max_left _ _).trans_lt hN
  have hx : 0 < |N| := zero_lt_one.trans hx1
  have hlin : A*(P+Q+R+1) < |N| := (le_max_right _ _).trans_lt hN
  have hdiv : P+Q+R+1 < |N|/A := (lt_div_iff₀ hA).mpr (by simpa only [mul_comm] using hlin)
  have hmul := mul_lt_mul_of_pos_right hdiv hx
  have hsq : |N|/A*|N| = N^2/A := by rw [div_mul_eq_mul_div,← sq, sq_abs]
  rw [hsq] at hmul
  have hsmall : P*|N|+Q+R < (P+Q+R+1)*|N| := by
    nlinarith [mul_nonneg (add_nonneg hQ hR) (sub_nonneg.mpr hx1.le)]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniform_crossing_threshold (sLo sHi K d T R : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K)
    (hd : 0 ≤ d) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∃ H : ℝ, 0 < H ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → H < |N| →
      0 < (slopePure S D N L k t).1 ∧
      R < inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let Q := K/sLo+2*T*(d+sHi*T)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨H,hH,hh⟩ := quadratic_dominates_linear sHi (2*T) Q R hmax hQ hR
  refine ⟨H,hH,?_⟩
  intro n m hn hm hmn S D N L k t u hSmin hSmax hk hDb htb hub hN
  have hlarge := hh N hN
  have he : N^2/sHi-Q-(2*T)*|N| = N^2/sHi-K/sLo-2*T*(d+sHi*T+|N|) := by
    dsimp [Q]; ring
  rw [he] at hlarge
  have htail : 0 ≤ 2*T*(d+sHi*T+|N|) := by positivity
  have hfirst : K/sLo < N^2/sHi := by linarith
  obtain ⟨hp,hbound⟩ := uniform_crossing_projection_lower hn hm hmn
    hmin hSmin hSmax hK hk hDb htb hub hfirst
  exact ⟨hp,hlarge.trans_le hbound⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
