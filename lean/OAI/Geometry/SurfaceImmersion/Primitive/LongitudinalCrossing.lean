import OAI.Geometry.SurfaceImmersion.Primitive.CrossingInvariantThreshold

namespace OAI

/-! Away from angular turns, the large longitudinal component alone gives
both ordered crossing inequalities. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma frameVector_inner_second {n m : E} (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    (v : ℝ × ℝ) : inner ℝ (frameVector n m v) m = v.2 := by
  have hnm : inner ℝ n m = 0 := by rw [real_inner_comm]; exact hmn
  simp only [frameVector,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    hm,one_pow,hnm,mul_one,mul_zero,zero_add]

lemma crossing_projection_of_nonzero {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {S D N L k t u : ℝ} (hS : S ≠ 0)
    (hP : frameVector n m (slopePure S D N L k t) ≠ 0) :
    ‖frameVector n m (slopePure S D N L k t)‖-|u-t| * (|D+S*t|+|N|) ≤
      inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let P := frameVector n m (slopePure S D N L k t)
  let Z := frameVector n m (slopeMixed S D N L k t u)
  have he : Z-P = (u-t) • frameVector n m (D+S*t,N) := by
    change frameVector n m (slopeMixed S D N L k t u)-
      frameVector n m (slopePure S D N L k t) = _
    rw [← frameVector_sub,mixed_sub_left hS,frameVector_smul]
  have hdiff : ‖Z-P‖ ≤ |u-t| * (|D+S*t|+|N|) := by
    rw [he,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (frameVector_norm_le hn hm _) (abs_nonneg _)
  exact (sub_le_sub_left hdiff ‖P‖).trans (mixed_projection_lower hP)

lemma longitudinal_norm_lower {n m : E} (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    {S D N L k t B T : ℝ} (hB : 0 ≤ B) (hN : |N| ≤ B) (ht : |t| ≤ T) :
    |L|-2*B*T ≤ ‖frameVector n m (slopePure S D N L k t)‖ := by
  let P := frameVector n m (slopePure S D N L k t)
  have hi : inner ℝ P m = L+2*N*t := frameVector_inner_second hm hmn _
  have hnorm : |L+2*N*t| ≤ ‖P‖ := by
    rw [← hi]
    simpa only [hm,mul_one] using abs_real_inner_le_norm P m
  have hadd := abs_sub (L+2*N*t) (2*N*t)
  have hNt : |2*N*t| ≤ 2*B*T := by
    simp only [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) ht (abs_nonneg _) (by positivity)
  simp only [add_sub_cancel_right] at hadd
  linarith

theorem longitudinal_projection_threshold (sHi d B T R : ℝ)
    (hsHi : 0 ≤ sHi) (hd : 0 ≤ d) (hB : 0 ≤ B) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∃ H : ℝ, 0 < H ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, 0 < S → S ≤ sHi → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → H < |L| →
      R < inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let H := R+2*T*(d+sHi*T+2*B)+1
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H,hH,?_⟩
  intro n m hn hm hmn S D N L k t u hS hSmax hDb hNb htb hub hL
  have hp := longitudinal_norm_lower (S := S) (D := D) (L := L) (k := k) hm hmn hB hNb htb
  have hP : frameVector n m (slopePure S D N L k t) ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hp
    have hrest : 0 ≤ 2*T*(d+sHi*T) := by positivity
    dsimp [H] at hL
    nlinarith
  have hdiff := crossing_slope_bound hS.le hSmax hDb htb hub (N := N)
  have hbd : |u-t| * (|D+S*t|+|N|) ≤ 2*T*(d+sHi*T+B) :=
    hdiff.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hNb) (by positivity))
  have hproj := crossing_projection_of_nonzero hn hm hS.ne' hP (u := u)
  dsimp [H] at hL
  nlinarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
