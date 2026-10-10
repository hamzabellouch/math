import OAI.Analysis.RotationWeights.Regular

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

namespace ContinuousCircleWeight
abbrev FiberHilbert := lp (fun _ : ℤ => ℂ) 2
abbrev FiberOperator := FiberHilbert →L[ℂ] FiberHilbert

def lpDiagonal {ι : Type uι} (a : ι → ℂ) (B : ℝ≥0) (ha : ∀ i, ‖a i‖ ≤ B) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => a i * f i, by
        apply (((lp.memℓp f).norm).const_mul (B : ℝ)).mono
        intro i
        change ‖a i * f i‖ ≤ (B : ℝ) * ‖f i‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)⟩
      map_add' := by intro f g; ext i; exact mul_add _ _ _
      map_smul' := by intro c f; ext i; exact mul_left_comm _ _ _ }
    B (by
      intro f
      calc
        _ ≤ ‖(B : ℂ) • f‖ := lp.norm_mono (by norm_num) (by
          intro i
          change ‖a i * f i‖ ≤ ‖((B : ℝ) : ℂ) * f i‖
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa using mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (f i))
)
        _ = (B : ℝ) * ‖f‖ := by
          rw [norm_smul]
          simp)

@[simp] theorem lpDiagonal_apply {ι : Type uι} (a : ι → ℂ) (B : ℝ≥0)
    (ha : ∀ i, ‖a i‖ ≤ B) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpDiagonal a B ha f i = a i * f i := rfl

def fiberShift (n : ℤ) : FiberHilbert ≃ₗᵢ[ℂ] FiberHilbert :=
  lpPermute (Equiv.addLeft n)

@[simp] theorem fiberShift_apply (n : ℤ) (f : FiberHilbert) (k : ℤ) :
    fiberShift n f k = f (k-n) := by
  change f (-n+k) = _
  apply congrArg f; omega

@[simp] theorem fiberShift_add (m n : ℤ) :
    fiberShift (m+n) = fiberShift m * fiberShift n := by
  ext f k
  change fiberShift (m+n) f k = fiberShift m (fiberShift n f) k
  simp only [fiberShift_apply]
  apply congrArg f; omega

def fiberWeightedShift (w : ℤ → ℂ) (hw : ∀ k, ‖w k‖ ≤ 1) : FiberOperator :=
  (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap * lpDiagonal w 1 hw

@[simp] theorem fiberWeightedShift_apply (w : ℤ → ℂ) (hw : ∀ k, ‖w k‖ ≤ 1)
    (f : FiberHilbert) (k : ℤ) :
    fiberWeightedShift w hw f k = w (k-1) * f (k-1) := by
  change fiberShift 1 (lpDiagonal w 1 hw f) k = _
  rw [fiberShift_apply]
  rfl

def fiberCocycleShift (F : ℤ → ℝ) (hF : ∀ k, 0 < F k) (hmono : Antitone F) :
    FiberOperator :=
  fiberWeightedShift (fun k => ((F (k+1) / F k : ℝ) : ℂ)) (by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hF _) (hF _))]
    exact (div_le_one (hF k)).mpr (hmono (by omega)))

@[simp] theorem fiberCocycleShift_apply (F : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hmono : Antitone F) (f : FiberHilbert) (k : ℤ) :
    fiberCocycleShift F hF hmono f k = (F k / F (k-1) : ℝ) * f (k-1) := by
  simp [fiberCocycleShift]

theorem fiberCocycleShift_pow_apply (F : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hmono : Antitone F) (n : ℕ) (f : FiberHilbert) (k : ℤ) :
    (fiberCocycleShift F hF hmono ^ n) f k =
      (F k / F (k-n) : ℝ) * f (k-n) := by
  induction n generalizing f k with
  | zero => simp [ne_of_gt (hF k)]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, fiberCocycleShift_apply, ih]
    have hk : k - 1 - (n : ℤ) = k - ((n+1 : ℕ) : ℤ) := by omega
    rw [hk, ← mul_assoc, ← Complex.ofReal_mul]
    have hr : F k / F (k-1) * (F (k-1) / F (k - ((n+1 : ℕ) : ℤ))) =
        F k / F (k - ((n+1 : ℕ) : ℤ)) := by
      field_simp [ne_of_gt (hF (k-1))]
    rw [hr]

theorem invariant_fixed_vector {T q : FiberOperator}
    (hinv : (1-q) * T * q = 0) {v : FiberHilbert} (hv : q v = v) :
    q (T v) = T v := by
  have h := congrArg (fun A : FiberOperator => A v) hinv
  have heq : T v - q (T v) = 0 := by
    simpa only [mul_apply_eq_comp, hv, sub_apply,
      one_apply_eq_self, zero_apply] using h
  exact (sub_eq_zero.mp heq).symm

theorem invariant_fixed_vector_pow {T q : FiberOperator}
    (hinv : (1-q) * T * q = 0) {v : FiberHilbert} (hv : q v = v) (n : ℕ) :
    q ((T ^ n) v) = (T ^ n) v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact invariant_fixed_vector hinv ih

theorem projection_complement_inner {q : FiberOperator} (hq : IsStarProjection q)
    {v : FiberHilbert} (hv : q v = v) (e : FiberHilbert) :
    inner ℂ ((1-q) e) v = 0 := by
  rw [← (hq.one_sub.isSelfAdjoint.adjoint_eq),
    ContinuousLinearMap.adjoint_inner_left]
  simp [hv]

def cocycleRatioDiagonal (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (horder : ∀ k, G k ≤ F k) : FiberOperator :=
  lpDiagonal (fun k => ((G k / F k : ℝ) : ℂ)) 1 (by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hG _) (hF _))]
    exact (div_le_one (hF k)).mpr (horder k))

@[simp] theorem cocycleRatioDiagonal_apply (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (horder : ∀ k, G k ≤ F k) (v : FiberHilbert) (k : ℤ) :
    cocycleRatioDiagonal F G hF hG horder v k = (G k / F k : ℝ) * v k := rfl

theorem cocycle_action_coordinate (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (hmono : Antitone G) (horder : ∀ k, G k ≤ F k)
    (ξ : FiberHilbert) (n : ℕ) (k : ℤ) :
    ((fiberCocycleShift G hG hmono ^ n)
      (cocycleRatioDiagonal F G hF hG horder ξ)) (n+k) =
      (G (n+k) / F k : ℝ) * ξ k := by
  rw [fiberCocycleShift_pow_apply]
  simp only [add_sub_cancel_left, cocycleRatioDiagonal_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp [ne_of_gt (hG k)]

theorem fiber_full_convolution (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (hmono : Antitone G) (horder : ∀ k, G k ≤ F k)
    (q : FiberOperator) (hq : IsStarProjection q)
    (hinv : (1-q) * fiberCocycleShift G hG hmono * q = 0)
    (ξ e : FiberHilbert)
    (hξ : q (cocycleRatioDiagonal F G hF hG horder ξ) =
      cocycleRatioDiagonal F G hF hG horder ξ) (n : ℕ) :
    Summable (fun v : ℤ => (G (n+v) / F v : ℝ) * ξ v *
        starRingEnd ℂ (((1-q) e) (n+v))) ∧
      (∑' v : ℤ, (G (n+v) / F v : ℝ) * ξ v *
        starRingEnd ℂ (((1-q) e) (n+v))) = 0 := by
  let η := (fiberCocycleShift G hG hmono ^ n)
    (cocycleRatioDiagonal F G hF hG horder ξ)
  let g := (1-q) e
  have hcoord (k : ℤ) : inner ℂ (g (n+k)) (η (n+k)) =
      (G (n+k) / F k : ℝ) * ξ k * starRingEnd ℂ (g (n+k)) := by
    rw [RCLike.inner_apply]
    rw [show η (n+k) = (G (n+k) / F k : ℝ) * ξ k from
      cocycle_action_coordinate F G hF hG hmono horder ξ n k]
  constructor
  · have hs := (Equiv.addLeft (n : ℤ)).summable_iff.mpr (lp.summable_inner (𝕜 := ℂ) g η)
    change Summable (fun k : ℤ => inner ℂ (g (n+k)) (η (n+k))) at hs
    simpa only [hcoord] using hs
  · have hzero : inner ℂ g η = 0 := projection_complement_inner hq
      (invariant_fixed_vector_pow hinv hξ n) e
    rw [lp.inner_eq_tsum] at hzero
    rw [← (Equiv.addLeft (n : ℤ)).tsum_eq (fun k => inner ℂ (g k) (η k))] at hzero
    change (∑' k : ℤ, inner ℂ (g (n+k)) (η (n+k))) = 0 at hzero
    simpa only [hcoord] using hzero

theorem cocycle_two_ratio_bounds (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (hFmono : Antitone F) (hGmono : Antitone G)
    (horder : ∀ k, G k ≤ F k) (n : ℕ) (k : ℤ) :
    0 < G (n+k) / F k ∧
    G (n+k) / F k ≤ G k / F k ∧
    G (n+k) / F k ≤ G (n+k) / F (n+k) ∧
    G k / F k ≤ 1 ∧ G (n+k) / F (n+k) ≤ 1 := by
  have hkn : k ≤ (n : ℤ) + k := by omega
  exact ⟨div_pos (hG _) (hF _),
    div_le_div_of_nonneg_right (hGmono hkn) (hF _).le,
    div_le_div_of_nonneg_left (hG _).le (hF _) (hFmono hkn),
    (div_le_one (hF _)).mpr (horder _),
    (div_le_one (hF _)).mpr (horder _)⟩

end ContinuousCircleWeight

end

end OAI
