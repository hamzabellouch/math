import OAI.Geometry.SurfaceImmersion.Whitney.ShiftedRotationFrame
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleRotationFilling

namespace OAI

/-! A compact explicit filling of the frame for two equal-index zeros. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def shiftedDoubleFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  shiftedRotationFrame (x 0) (x 1) 0 1

def filledShiftedRotation (χ ψ : Base → ℝ) (x : Base) : Base →L[ℝ] FrameTarget :=
  filledDoubleRotation χ x-
    (ContinuousLinearMap.proj 1).smulRight (![0,1-ψ x,0] : FrameTarget)

lemma filledShiftedRotation_smooth {χ ψ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (filledShiftedRotation χ ψ) := by
  have hV : ContDiff ℝ ∞ (fun x => (![0,1-ψ x,0] : FrameTarget)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_const.sub hψ
    · exact contDiff_const
  exact (filledDoubleRotation_smooth hχ).sub (contDiff_const.smulRight hV)

lemma norm_large_square_sum_radius {x : Base} {r : ℝ} (hr : 1 < r)
    (hx : x ∉ closedBall (0:Base) r) :
    1 < (x 0)^2+(x 1)^2 := by
  by_contra hh
  have hs : (x 0)^2+(x 1)^2 ≤ 1 := le_of_not_gt hh
  have hn : ‖x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_le]
    fin_cases i
    · change -1 ≤ x 0 ∧ x 0 ≤ 1
      constructor <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
    · change -1 ≤ x 1 ∧ x 1 ≤ 1
      constructor <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  apply hx
  simpa only [mem_closedBall,dist_zero_right] using hn.trans hr.le

theorem compact_shifted_double_filling_radius {R : ℝ} (hR : 1 < R) :
    ∃ (A : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ A ∧ (∀ x, Function.Injective (A x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) R ∧ ∀ x ∉ K, A =ᶠ[𝓝 x] shiftedDoubleFrame := by
  let r : ℝ := (1+R)/2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  obtain ⟨χ,hχ,hχc,_hχr,hχs,hχone⟩ := CollarVelocity.compact_cutoff
    (isCompact_singleton (x := (0:Base))) isOpen_ball
    (singleton_subset_iff.mpr (mem_ball_self (by linarith : (0:ℝ)<r)))
  obtain ⟨ψ,hψ,hψc,hψr,hψs,hψone⟩ := CollarVelocity.compact_cutoff
    (isCompact_closedBall (0:Base) r) isOpen_ball
    (closedBall_subset_ball hrR)
  let A := filledShiftedRotation χ ψ
  let K := tsupport χ ∪ tsupport ψ
  refine ⟨A,K,filledShiftedRotation_smooth hχ hψ,?_,hχc.union hψc,?_,?_⟩
  · intro x
    change Function.Injective (shiftedRotationFrame (x 0) (x 1) (χ x) (1-ψ x))
    apply shiftedRotationFrame_injective
    · by_cases hx : x = 0
      · subst x
        rw [hχone 0 (mem_singleton 0)]
        norm_num
      · have hn : 0 < (x 0)^2+(x 1)^2 := by
          by_contra hh
          have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
          have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
          apply hx
          ext i
          fin_cases i
          · exact h0
          · exact h1
        exact add_pos_of_pos_of_nonneg hn (sq_nonneg _)
    · by_cases he : 1-ψ x = 0
      · exact Or.inl he
      · have hx : x ∉ closedBall (0:Base) r := by
          intro hx
          exact he (by rw [hψone x hx]; ring)
        have hc : χ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hh => hx (ball_subset_closedBall (hχs hh)))
        exact Or.inr ⟨hc,norm_large_square_sum_radius hr hx,by
          constructor <;> linarith [(hψr x).1,(hψr x).2]⟩
  · intro x hx
    rcases hx with hx | hx
    · exact (ball_subset_ball hrR.le) (hχs hx)
    · exact hψs hx
  · intro x hx
    have hxc : x ∉ tsupport χ := fun h => hx (Or.inl h)
    have hxp : x ∉ tsupport ψ := fun h => hx (Or.inr h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxc,
      notMem_tsupport_iff_eventuallyEq.mp hxp] with y hyc hyp
    change χ y = 0 at hyc
    change ψ y = 0 at hyp
    change shiftedRotationFrame (y 0) (y 1) (χ y) (1-ψ y) = shiftedDoubleFrame y
    simp only [hyc,hyp,sub_zero,shiftedDoubleFrame]

lemma norm_large_square_sum {x : Base} (hx : x ∉ closedBall (0:Base) 2) :
    1 < (x 0)^2+(x 1)^2 := norm_large_square_sum_radius (by norm_num) hx

theorem compact_shifted_double_filling :
    ∃ (A : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ A ∧ (∀ x, Function.Injective (A x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) 3 ∧ ∀ x ∉ K, A =ᶠ[𝓝 x] shiftedDoubleFrame :=
  compact_shifted_double_filling_radius (by norm_num)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
