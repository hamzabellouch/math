import OAI.Analysis.KadisonKastler.SpectralClipStar
import OAI.Analysis.KadisonKastler.GraphOrbitSelection
import OAI.Analysis.KadisonKastler.FourthMomentClipping
import OAI.Analysis.KadisonKastler.RecoveryJointLaw

namespace OAI

/-! # Spectral clipping of a rescaled graph vector

The positive vector state can be applied to the two C*-order tail
bounds. Adjoint compatibility gives the same cutoff on both graph
coordinates. No traciality of the vector state is used.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance graphClippingOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance graphClippingStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- A positive vector functional is monotone in the C*-order. -/
theorem realVectorState_mono (Ω : H) {x y : H →L[ℂ] H} (hxy : x ≤ y) :
    realVectorState Ω x ≤ realVectorState Ω y := by
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
  have h : 0 ≤ realVectorState Ω (star z * z) := by
    rw [realVectorState_star_mul_self]
    positivity
  rw [← hz, map_sub] at h
  linarith

/-- Right vector-state variance decreases under clipping. -/
theorem vectorState_spectralClip_right_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖spectralClip β x Ω‖ ^ 2 ≤ ‖x Ω‖ ^ 2 := by
  simpa only [realVectorState_star_mul_self] using
    realVectorState_mono Ω (spectralClip_star_mul_self_le hβ x)

/-- The adjoint coordinate has the same variance decrease. -/
theorem vectorState_spectralClip_left_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖star (spectralClip β x) Ω‖ ^ 2 ≤ ‖star x Ω‖ ^ 2 := by
  simpa only [star_spectralClip hβ] using vectorState_spectralClip_right_le Ω hβ (star x)

/-- The clipped graph remains bounded by the sampled second and fourth
moment cost. -/
theorem norm_rescaledGraph_spectralClip_sq_le_cost
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c (spectralClip β x)‖ ^ 2 ≤
      graphMomentCost Ω (c ^ 2) x := by
  rw [norm_rescaledGraphVector_sq]
  have hr := vectorState_spectralClip_right_le Ω hβ x
  have hl := mul_le_mul_of_nonneg_left
    (vectorState_spectralClip_left_le Ω hβ x) (sq_nonneg c)
  have hp : 0 ≤ realVectorState Ω ((star x * x) ^ 2) := by
    have he : (star x * x) ^ 2 = star (star x * x) * (star x * x) := by
      simp only [star_mul, star_star, pow_two]
    rw [he, realVectorState_star_mul_self]
    positivity
  have hq : 0 ≤ realVectorState Ω ((x * star x) ^ 2) := by
    have he : (x * star x) ^ 2 = star (x * star x) * (x * star x) := by
      simp only [star_mul, star_star, pow_two]
    rw [he, realVectorState_star_mul_self]
    positivity
  unfold graphMomentCost
  rw [realVectorState_star_mul_self]
  have he : realVectorState Ω (x * star x) = ‖star x Ω‖ ^ 2 := by
    simpa only [star_star] using realVectorState_star_mul_self Ω (star x)
  rw [he]
  nlinarith [mul_nonneg (sq_nonneg c) hq]

/-- The right-coordinate clipping tail is controlled by the actual
fourth moment of the original vector state. -/
theorem vectorState_spectralClip_discard_right_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖(x - spectralClip β x) Ω‖ ^ 2 ≤
      realVectorState Ω ((star x * x) ^ 2) / β ^ 2 := by
  have h := realVectorState_mono Ω (spectralClip_discard_fourth_bound hβ x)
  simpa only [realVectorState_star_mul_self, map_smul, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- The same tail estimate holds on the adjoint coordinate. -/
theorem vectorState_spectralClip_discard_left_le (Ω : H) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖star (x - spectralClip β x) Ω‖ ^ 2 ≤
      realVectorState Ω ((x * star x) ^ 2) / β ^ 2 := by
  simpa only [star_sub, star_spectralClip hβ, star_star] using
    vectorState_spectralClip_discard_right_le Ω hβ (star x)

/-- The weighted graph tail is controlled uniformly in the rescaling. -/
theorem norm_rescaledGraph_spectralClip_discard_sq_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c (x - spectralClip β x)‖ ^ 2 ≤
      (realVectorState Ω ((star x * x) ^ 2) +
        c ^ 2 * realVectorState Ω ((x * star x) ^ 2)) / β ^ 2 := by
  rw [norm_rescaledGraphVector_sq]
  have hr := vectorState_spectralClip_discard_right_le Ω hβ x
  have hl := mul_le_mul_of_nonneg_left
    (vectorState_spectralClip_discard_left_le Ω hβ x) (sq_nonneg c)
  exact (add_le_add hr hl).trans_eq (by ring)

/-- The full cost also bounds the weighted fourth-moment tail. -/
theorem norm_rescaledGraph_spectralClip_discard_sq_le_cost
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) {β : ℝ} (hβ : 0 < β)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c (x - spectralClip β x)‖ ^ 2 ≤
      graphMomentCost Ω (c ^ 2) x / β ^ 2 := by
  refine (norm_rescaledGraph_spectralClip_discard_sq_le J Ω c hβ x).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg β)
  unfold graphMomentCost
  have hr : 0 ≤ realVectorState Ω (star x * x) := by
    rw [realVectorState_star_mul_self]; positivity
  have hl : 0 ≤ realVectorState Ω (x * star x) := by
    simpa only [star_star] using
      (show 0 ≤ realVectorState Ω (star (star x) * star x) from by
        rw [realVectorState_star_mul_self]; positivity)
  nlinarith [mul_nonneg (sq_nonneg c) hl]

/-- Clipping respects the actual concrete von Neumann algebra. -/
theorem spectralClip_mem_vonNeumannAlgebra (M : VonNeumannAlgebra H)
    (β : ℝ) {x : H →L[ℂ] H} (hx : x ∈ M) : spectralClip β x ∈ M :=
  spectralClip_mem_closedStarSubalgebra M.toStarSubalgebra (isClosed_algebra M) β hx

/-- The signal lost in clipping is at most the operator norm times the
graph-tail norm. -/
theorem graphSignal_spectralClip_loss_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (β : ℝ) (x : H →L[ℂ] H) :
    ‖T (rescaledGraphVector J Ω c x)‖ ≤
      ‖T (rescaledGraphVector J Ω c (spectralClip β x))‖ +
        ‖T‖ * ‖rescaledGraphVector J Ω c (x - spectralClip β x)‖ := by
  have he := (rescaledGraphOperatorMap J Ω c).map_sub x (spectralClip β x)
  change rescaledGraphVector J Ω c (x - spectralClip β x) =
    rescaledGraphVector J Ω c x - rescaledGraphVector J Ω c (spectralClip β x) at he
  have hd := T.le_opNorm (rescaledGraphVector J Ω c (x - spectralClip β x))
  rw [he, map_sub] at hd
  rw [← he] at hd
  have ht := norm_le_norm_add_norm_sub
    (T (rescaledGraphVector J Ω c (spectralClip β x))) (T (rescaledGraphVector J Ω c x))
  rw [norm_sub_rev] at ht
  exact ht.trans (add_le_add le_rfl hd)

/-- The concrete cutoff 128 makes the graph-tail norm at most one eighth
whenever the sampled graph cost is at most 240. -/
theorem norm_rescaledGraph_spectralClip_128_discard_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : H →L[ℂ] H)
    (hcost : graphMomentCost Ω (c ^ 2) x ≤ 240) :
    ‖rescaledGraphVector J Ω c (x - spectralClip 128 x)‖ ≤ 1 / 8 := by
  have h := (norm_rescaledGraph_spectralClip_discard_sq_le_cost J Ω c
    (by norm_num : (0 : ℝ) < 128) x).trans
      (div_le_div_of_nonneg_right hcost (by norm_num : (0 : ℝ) ≤ 128 ^ 2))
  nlinarith [norm_nonneg (rescaledGraphVector J Ω c (x - spectralClip 128 x))]

/-- A sampled vector with the retained squared signal admits an actual
bounded clipping that still retains a uniform fraction of that signal. -/
theorem graphSignal_spectralClip_128_lower_bound
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (x : H →L[ℂ] H)
    (hcost : graphMomentCost Ω (c ^ 2) x ≤ 240)
    (hsignal : ‖T‖ ^ 2 / 8 ≤ ‖T (rescaledGraphVector J Ω c x)‖ ^ 2) :
    ‖T‖ / 8 ≤ ‖T (rescaledGraphVector J Ω c (spectralClip 128 x))‖ := by
  have ht := graphSignal_spectralClip_loss_le J Ω c T 128 x
  have he := norm_rescaledGraph_spectralClip_128_discard_le J Ω c x hcost
  have hs : ‖T‖ / 3 ≤ ‖T (rescaledGraphVector J Ω c x)‖ := by
    nlinarith [norm_nonneg T, norm_nonneg (T (rescaledGraphVector J Ω c x))]
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg T)
  nlinarith [norm_nonneg T]

end

end KadisonKastler

end OAI
