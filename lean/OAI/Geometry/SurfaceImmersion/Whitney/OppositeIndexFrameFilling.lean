import OAI.Geometry.SurfaceImmersion.Whitney.ShiftedRotationFilling

namespace OAI

/-! The opposite-index pair can be filled while keeping its first column fixed. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def oppositeIndexFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 ((x 0)^2-1) (x 1)

def filledOppositeIndex (χ : ℝ → ℝ) (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 ((x 0)^2-1+2*χ (x 0)*χ (x 1)) (x 1)

lemma filledOppositeIndex_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (filledOppositeIndex χ) := by
  have hy : ContDiff ℝ ∞ (fun x : Base =>
      (![0,(x 0)^2-1+2*χ (x 0)*χ (x 1),x 1] : FrameTarget)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact (((contDiff_apply ℝ ℝ 0).pow 2).sub contDiff_const).add
        ((contDiff_const.mul (hχ.comp (contDiff_apply ℝ ℝ 0))).mul
          (hχ.comp (contDiff_apply ℝ ℝ 1)))
    · exact contDiff_apply ℝ ℝ 1
  exact contDiff_const.add (contDiff_const.smulRight hy)

theorem compact_opposite_index_frame_filling_radius {R : ℝ} (hR : 1 < R) :
    ∃ (B : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ B ∧ (∀ x, Function.Injective (B x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) R ∧ ∀ x ∉ K, B =ᶠ[𝓝 x] oppositeIndexFrame := by
  let u : ℝ := (1+R)/2
  let v : ℝ := (u+R)/2
  have hu : 1 < u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u,v]; linarith
  have hvR : v < R := by dsimp [u,v]; linarith
  have hv : 0 < v := by linarith
  obtain ⟨χ,hχ,_hχc,hχrange,hχsupp,hχone⟩ := CollarVelocity.compact_cutoff
    (isCompact_closedBall (0:ℝ) u) isOpen_ball (closedBall_subset_ball huv)
  have hχ0 : χ 0 = 1 := hχone 0 (mem_closedBall_self (by linarith))
  let B := filledOppositeIndex χ
  let K := closedBall (0:Base) v
  have hz : ∀ x ∉ K, χ (x 0)*χ (x 1) = 0 := by
    intro x hx
    by_contra hh
    obtain ⟨h0,h1⟩ := mul_ne_zero_iff.mp hh
    have hb0 := hχsupp (subset_tsupport χ h0)
    have hb1 := hχsupp (subset_tsupport χ h1)
    have hn : ‖x‖ ≤ v := by
      apply (pi_norm_le_iff_of_nonneg hv.le).mpr
      intro i
      fin_cases i
      · change ‖x 0‖ ≤ v
        have hb : ‖x 0‖ < v := by simpa only [mem_ball,dist_zero_right] using hb0
        exact hb.le
      · change ‖x 1‖ ≤ v
        have hb : ‖x 1‖ < v := by simpa only [mem_ball,dist_zero_right] using hb1
        exact hb.le
    exact hx (by simpa only [K,mem_closedBall,dist_zero_right] using hn)
  refine ⟨B,K,filledOppositeIndex_smooth hχ,?_,isCompact_closedBall _ _,
    closedBall_subset_ball hvR,?_⟩
  · intro x
    apply axisNormalFrame_injective (by norm_num)
    by_cases hx1 : x 1 = 0
    · left
      rw [hx1,hχ0,mul_one]
      have hp : 0 < (x 0)^2-1+2*χ (x 0) := by
        by_cases hxu : x 0 ∈ closedBall (0:ℝ) u
        · rw [hχone _ hxu]
          nlinarith [sq_nonneg (x 0)]
        · have ha : u < |x 0| := by
            simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,not_le] using hxu
          have hs := (one_lt_sq_iff_one_lt_abs (x 0)).mpr (hu.trans ha)
          nlinarith [(hχrange (x 0)).1]
      exact hp.ne'
    · exact Or.inr hx1
  · intro x hx
    filter_upwards [(isClosed_closedBall.isOpen_compl).mem_nhds hx] with y hy
    have he := hz y hy
    change axisNormalFrame 1 ((y 0)^2-1+2*χ (y 0)*χ (y 1)) (y 1) = _
    have hzero : 2*χ (y 0)*χ (y 1) = 0 := by rw [mul_assoc,he,mul_zero]
    simp only [hzero,add_zero,oppositeIndexFrame]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
