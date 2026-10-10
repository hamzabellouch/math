import OAI.Analysis.LiebThirring.MatrixTangent

namespace OAI

universe u16 u17 u18

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SharpLiebThirring.ScalarProof

lemma symmetric_shift_boundary {g : ℝ → ℝ} (hg : Continuous g) (he : Function.Even g)
    (R b : ℝ) :
    (∫ s in -R..R, g (s - b) - g s) =
      ∫ t in 0..b, g (R + t) - g (R - b + t) := by
  have hc1 : Continuous (fun s : ℝ ↦ g (s - b)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ ↦ g (R + t)) := by fun_prop
  have hc3 : Continuous (fun t : ℝ ↦ g (R - b + t)) := by fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_comp_sub_right]
  rw [intervalIntegral.integral_interval_sub_interval_comm
    (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hn : (∫ s in -R - b..-R, g s) = ∫ t in R..R + b, g t := by
    have h := intervalIntegral.integral_comp_neg (f := g) (a := R) (b := R + b)
    calc
      _ = ∫ x in R..R + b, g (-x) := by
        simpa only [show -(R + b) = -R - b by ring] using h.symm
      _ = _ := intervalIntegral.integral_congr (fun x _ ↦ he x)
  rw [hn, intervalIntegral.integral_sub (hc2.intervalIntegrable _ _)
    (hc3.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_comp_add_left, add_zero, sub_add_cancel]

lemma symmetric_shift_norm_le {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (R b C T : ℝ) (hR : T + 2 * |b| ≤ R)
    (hbound : ∀ x, T ≤ x → ‖g' x‖ ≤ C) :
    ‖∫ s in -R..R, g (s - b) - g s‖ ≤ C * |b| ^ 2 := by
  rw [symmetric_shift_boundary (continuous_iff_continuousAt.2 (fun x ↦ (hg x).continuousAt)) he]
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C * |b|) (fun t ht ↦ ?_)) (by simp [pow_two, mul_assoc])
  have ht' : -|b| ≤ t := by
    have := ht.1
    have hmin : -|b| ≤ min 0 b := le_min (by linarith [abs_nonneg b]) (neg_abs_le b)
    linarith
  have hx : R - b + t ∈ Ici T := by
    have := le_abs_self b
    change T ≤ _
    linarith
  have hy : R + t ∈ Ici T := by change T ≤ _; linarith [abs_nonneg b]
  have hm := (convex_Ici T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hg x).hasDerivWithinAt) (fun x hx ↦ hbound x hx) hx hy
  simpa only [show R + t - (R - b + t) = b by ring, Real.norm_eq_abs] using hm

lemma symmetric_shift_tendsto_zero {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (hlim : Tendsto g' atTop (𝓝 0)) (b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R, g (s - b) - g s) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hc : 0 < ε / (|b| ^ 2 + 1) := div_pos hε (by positivity)
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hlim) _ hc
  refine ⟨T + 2 * |b|, fun R hR ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt (symmetric_shift_norm_le hg he R b (ε / (|b| ^ 2 + 1)) T hR (fun x hx ↦ ?_)) ?_
  · simpa only [dist_zero_right] using (hT x hx).le
  · have hden : 0 < |b| ^ 2 + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.ScalarProof

lemma primitive_quadratic_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ regularizedPrimitive σ δ (t ^ 2 + z))
      (2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) s := by
  convert! (primitive_hasDerivAt σ hδ (s ^ 2 + z)).comp s
    (((hasDerivAt_id s).pow 2).add_const z) using 1
  simp only [id_eq, Nat.cast_ofNat, mul_one]
  ring

lemma primitive_quadratic_deriv_tendsto {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Tendsto (fun s : ℝ ↦ 2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) atTop (𝓝 0) := by
  let a := δ / (δ + |z| + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : Tendsto (fun s : ℝ ↦ (2 * a ^ (σ - 3 / 2)) * s ^ (2 * σ - 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 - 2 * σ by linarith)).const_mul
      (2 * a ^ (σ - 3 / 2))
    simpa only [show -(2 - 2 * σ) = 2 * σ - 2 by ring, mul_zero] using h
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs₀ : 0 < s := by linarith
    have hb := Real.rpow_le_rpow_of_nonpos (show 0 < a * (1 + s ^ 2) by positivity)
      (shifted_base_lower hδ z s) (show σ - 3 / 2 ≤ 0 by linarith)
    have hsq := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hs₀)
      (show s ^ 2 ≤ 1 + s ^ 2 by linarith) (show σ - 3 / 2 ≤ 0 by linarith)
    rw [Real.mul_rpow ha.le (by positivity)] at hb
    calc
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (s ^ 2) ^ (σ - 3 / 2)) := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs₀.le]
        norm_num only [Nat.cast_ofNat]
        conv_lhs => arg 1; arg 2; rw [← Real.rpow_one s]
        rw [show 2 * s ^ (1 : ℝ) * (a ^ (σ - 3 / 2) * s ^ ((2 : ℝ) * (σ - 3 / 2))) =
          (2 * a ^ (σ - 3 / 2)) * (s ^ (1 : ℝ) * s ^ (2 * (σ - 3 / 2))) by ring,
          ← Real.rpow_add hs₀]
        congr 2
        ring

lemma primitive_symmetric_shift_zero {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2 + z))
      atTop (𝓝 0) :=
  symmetric_shift_tendsto_zero (primitive_quadratic_hasDerivAt σ hδ z)
    (fun s ↦ by simp) (primitive_quadratic_deriv_tendsto hσ hδ z) b

/-- The symmetric shift identity, with exactly the cutoff used in the field. -/
lemma primitive_shift_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ * ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2))
      atTop (𝓝 (scalarMu σ δ z)) := by
  have hc := (primitive_differentiable σ hδ).continuous
  have h₁ := primitive_symmetric_shift_zero hσ hδ z b
  have h₂ := intervalIntegral_tendsto_integral (mu_integrand_integrable hσ hδ z)
    tendsto_neg_atTop_atBot tendsto_id
  have hh := (h₁.add h₂).const_mul (fieldNormalization σ)
  simp only [zero_add] at hh
  apply hh.congr
  intro R
  congr 1
  simp only [id_eq]
  rw [← intervalIntegral.integral_add
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - b) ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2 + z)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s hs
  ring

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.ScalarProof

lemma derivative_lipschitz_on_positive {σ δ a : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) {x y : ℝ} (hx : a ≤ x) (hy : a ≤ y) :
    ‖(x + δ) ^ (σ - 3 / 2) - (y + δ) ^ (σ - 3 / 2)‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * ‖x - y‖ := by
  have hd : ∀ t ∈ Ici a, HasDerivWithinAt (fun t : ℝ ↦ (t + δ) ^ (σ - 3 / 2))
      ((σ - 3 / 2) * (t + δ) ^ (σ - 5 / 2)) (Ici a) t := by
    intro t ht
    change a ≤ t at ht
    have hp : t + δ ≠ 0 := by linarith
    convert! (((hasDerivAt_id t).add_const δ).rpow_const (p := σ - 3 / 2)
      (Or.inl hp)).hasDerivWithinAt using 1
    simp only [id_eq]
    ring_nf
  have hb : ∀ t ∈ Ici a, ‖(σ - 3 / 2) * (t + δ) ^ (σ - 5 / 2)‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) := by
    intro t ht
    change a ≤ t at ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_neg (show σ - 3 / 2 < 0 by linarith),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hr := Real.rpow_le_rpow_of_nonpos (show 0 < a + δ by linarith)
      (show a + δ ≤ t + δ by linarith) (show σ - 5 / 2 ≤ 0 by linarith)
    nlinarith
  exact (convex_Ici a).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

lemma primitive_taylor_bound {σ δ a x r y : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r) (hy : |y| ≤ r) :
    ‖regularizedPrimitive σ δ (x + y) - regularizedPrimitive σ δ x -
      (x + δ) ^ (σ - 3 / 2) * y‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r ^ 2 := by
  let L := (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2)
  have hL : 0 ≤ L := mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
  have hx : a ≤ x := by linarith
  have hxy : x + y ∈ Icc (x - r) (x + r) := by
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have hxx : x ∈ Icc (x - r) (x + r) := ⟨by linarith, by linarith⟩
  have hd (t : ℝ) (ht : t ∈ Icc (x - r) (x + r)) :
      HasDerivWithinAt (fun t : ℝ ↦ regularizedPrimitive σ δ t -
        regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * (t - x))
        ((t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)) (Icc (x - r) (x + r)) t := by
    have ht₀ : 0 ≤ t := by have := ht.1; linarith
    convert! (((primitive_hasDerivAt σ hδ t).sub_const (regularizedPrimitive σ δ x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul ((x + δ) ^ (σ - 3 / 2)))).hasDerivWithinAt
      using 1
    simp [max_eq_left ht₀]
  have hb (t : ℝ) (ht : t ∈ Icc (x - r) (x + r)) :
      ‖(t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)‖ ≤ L * r := by
    refine (derivative_lipschitz_on_positive hσ hδ ha (hxr.trans ht.1) hx).trans ?_
    apply mul_le_mul_of_nonneg_left _ hL
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hm := (convex_Icc (x - r) (x + r)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb hxx hxy
  simp only [sub_self, mul_zero, sub_zero, add_sub_cancel_left, Real.norm_eq_abs] at hm
  refine hm.trans ((mul_le_mul_of_nonneg_left hy (mul_nonneg hL hr)).trans_eq ?_)
  dsimp [L]
  ring

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u16} [Fintype n] [DecidableEq n]

lemma cfc_scalar_add (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc f (x • 1 + A) = cfc (fun y : ℝ ↦ f (x + y)) A := by
  have h := cfc_comp' f (fun y : ℝ ↦ x + y) A hf.continuousOn (by fun_prop) hA
  erw [cfc_const_add x id A (by fun_prop) hA, cfc_id ℝ A hA,
    Algebra.algebraMap_eq_smul_one] at h
  exact h.symm

lemma spectrum_abs_le_matrix_norm {A : Matrix n n ℂ} {y : ℝ} (hy : y ∈ spectrum ℝ A) :
    |y| ≤ ‖A‖ := by
  cases isEmpty_or_nonempty n with
  | inl h =>
      have h1 : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
      have hy0 : y = 0 := by simpa [h1] using spectrum.norm_le_norm_mul_of_mem hy
      simp [hy0]
  | inr h => simpa using spectrum.norm_le_norm_mul_of_mem hy

lemma primitive_cfc_taylor_bound {σ δ a x r : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hAr : ‖A‖ ≤ r) :
    ‖cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r ^ 2 := by
  have hc := (primitive_differentiable σ hδ).continuous
  have he : cfc (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * y) A =
      cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A := by
    erw [cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x) (fun y : ℝ ↦ (x + δ) ^ (σ - 3 / 2) * y) A
      (by fun_prop) (by fun_prop),
      cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y))
        (fun _ : ℝ ↦ regularizedPrimitive σ δ x) A (by fun_prop) (by fun_prop),
      cfc_const (regularizedPrimitive σ δ x) A hA,
      cfc_const_mul_id ((x + δ) ^ (σ - 3 / 2)) A hA,
      Algebra.algebraMap_eq_smul_one, ← cfc_scalar_add _ hc x hA]
  rw [← he]
  have hb : 0 ≤ (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r ^ 2 := by
    have : 0 ≤ 3 / 2 - σ := by linarith
    positivity
  apply norm_cfc_le hb
  intro y hy
  exact primitive_taylor_bound hσ hδ ha hr hxr
    ((spectrum_abs_le_matrix_norm hy).trans hAr)

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u17} [Fintype n] [DecidableEq n]

lemma quadratic_taylor_weight {σ δ s A : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hs : 1 ≤ s) :
    (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2 ≤
      (1 / 4 : ℝ) ^ (σ - 5 / 2) * A ^ 2 * (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hb : 0 < (1 + s ^ 2) / 4 := by positivity
  have hle : (1 + s ^ 2) / 4 ≤ s ^ 2 / 2 + δ := by nlinarith
  have hr := Real.rpow_le_rpow_of_nonpos hb hle (by linarith : σ - 5 / 2 ≤ 0)
  have he : ((1 + s ^ 2) / 4) ^ (σ - 5 / 2) =
      (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 5 / 2) := by
    rw [show (1 + s ^ 2) / 4 = (1 / 4 : ℝ) * (1 + s ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
  have he2 : (1 + s ^ 2) ^ (σ - 5 / 2) * (1 + s ^ 2) =
      (1 + s ^ 2) ^ (σ - 3 / 2) := by
    rw [← Real.rpow_add_one (by positivity)]
    congr 1
    ring
  calc
    _ ≤ ((1 + s ^ 2) / 4) ^ (σ - 5 / 2) * (A * s) ^ 2 :=
      mul_le_mul_of_nonneg_right hr (sq_nonneg _)
    _ = (1 / 4 : ℝ) ^ (σ - 5 / 2) * A ^ 2 *
        ((1 + s ^ 2) ^ (σ - 5 / 2) * s ^ 2) := by rw [he]; ring
    _ ≤ (1 / 4 : ℝ) ^ (σ - 5 / 2) * A ^ 2 *
        ((1 + s ^ 2) ^ (σ - 5 / 2) * (1 + s ^ 2)) := by gcongr; linarith
    _ = _ := by rw [he2]

lemma quadratic_derivative_weight {σ δ s : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hs : 1 ≤ s) :
    (s ^ 2 + δ) ^ (σ - 3 / 2) ≤
      (1 / 2 : ℝ) ^ (σ - 3 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hr := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + s ^ 2) / 2)
    (by nlinarith : (1 + s ^ 2) / 2 ≤ s ^ 2 + δ) (by linarith : σ - 3 / 2 ≤ 0)
  simpa only [show (1 + s ^ 2) / 2 = (1 / 2 : ℝ) * (1 + s ^ 2) by ring,
    Real.mul_rpow (by positivity : 0 ≤ (1 / 2 : ℝ)) (by positivity : 0 ≤ 1 + s ^ 2)] using hr

def quadraticMatrix (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  s ^ 2 • 1 + (C - (2 * s) • B)

def pairedFieldIntegrand (σ δ : ℝ) (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) +
    cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
    (2 * regularizedPrimitive σ δ (s ^ 2)) • 1

lemma pairedFieldIntegrand_even (σ δ : ℝ) (C B : Matrix n n ℂ) :
    Function.Even (pairedFieldIntegrand σ δ C B) := by
  intro s
  simp only [pairedFieldIntegrand, neg_neg, neg_sq, add_comm]

omit [Fintype n] in
lemma quadraticMatrix_hermitian {C B : Matrix n n ℂ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (s : ℝ) :
    (quadraticMatrix C B s).IsHermitian :=
  ((isHermitian_one (n := n) (α := ℂ)).smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (s ^ 2))).add (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s))))

lemma perturbed_norm_le {C B : Matrix n n ℂ} {s : ℝ} (hs : 1 ≤ |s|) :
    ‖C - (2 * s) • B‖ ≤ (‖C‖ + 2 * ‖B‖) * |s| := by
  calc
    _ ≤ ‖C‖ + ‖(2 * s) • B‖ := norm_sub_le _ _
    _ = ‖C‖ + 2 * |s| * ‖B‖ := by simp [norm_smul]
    _ ≤ _ := by nlinarith [norm_nonneg C, norm_nonneg B]

lemma pairedFieldIntegrand_bound {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    {s : ℝ} (hs : max 1 (2 * (‖C‖ + 2 * ‖B‖)) ≤ s) :
    ‖pairedFieldIntegrand σ δ C B s‖ ≤
      (2 * (3 / 2 - σ) * (1 / 4 : ℝ) ^ (σ - 5 / 2) * (‖C‖ + 2 * ‖B‖) ^ 2 +
        2 * ‖C‖ * (1 / 2 : ℝ) ^ (σ - 3 / 2)) * (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsA : 2 * (‖C‖ + 2 * ‖B‖) ≤ s := (le_max_right _ _).trans hs
  have hs0 : 0 < s := by linarith
  let A := ‖C‖ + 2 * ‖B‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hxr : s ^ 2 / 2 ≤ s ^ 2 - A * s := by dsimp [A]; nlinarith
  have hn₁ : ‖C - (2 * s) • B‖ ≤ A * s := by
    simpa only [abs_of_pos hs0] using (perturbed_norm_le (C := C) (B := B)
      (s := s) (by rwa [abs_of_pos hs0]))
  have hn₂ : ‖C - (2 * -s) • B‖ ≤ A * s := by
    simpa only [abs_neg, abs_of_pos hs0] using (perturbed_norm_le (C := C) (B := B)
      (s := -s) (by rwa [abs_neg, abs_of_pos hs0]))
  have ht₁ := primitive_cfc_taylor_bound hσ hδ (by positivity : 0 < s ^ 2 / 2)
    (mul_nonneg hA hs0.le) hxr (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))) hn₁
  have ht₂ := primitive_cfc_taylor_bound hσ hδ (by positivity : 0 < s ^ 2 / 2)
    (mul_nonneg hA hs0.le) hxr (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * -s)))) hn₂
  let E₁ := cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix n n ℂ) -
    (s ^ 2 + δ) ^ (σ - 3 / 2) • (C - (2 * s) • B)
  let E₂ := cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
    regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix n n ℂ) -
    (s ^ 2 + δ) ^ (σ - 3 / 2) • (C - (2 * -s) • B)
  have he : pairedFieldIntegrand σ δ C B s =
      E₁ + E₂ + (2 * (s ^ 2 + δ) ^ (σ - 3 / 2)) • C := by
    dsimp [pairedFieldIntegrand, E₁, E₂]
    module
  have ht₂' : ‖E₂‖ ≤ (3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2 := by
    simpa only [E₂, quadraticMatrix, neg_sq] using ht₂
  have hw := quadratic_taylor_weight (A := A) hσ hδ hs1
  have hd := quadratic_derivative_weight hσ hδ hs1
  have hr : 0 ≤ (s ^ 2 + δ) ^ (σ - 3 / 2) := Real.rpow_nonneg (by positivity) _
  have hp : 0 ≤ 3 / 2 - σ := by linarith
  rw [he]
  calc
    _ ≤ ‖E₁‖ + ‖E₂‖ + ‖(2 * (s ^ 2 + δ) ^ (σ - 3 / 2)) • C‖ :=
      by linarith [norm_add_le E₁ E₂, norm_add_le (E₁ + E₂) ((2 * (s ^ 2 + δ) ^ (σ - 3 / 2)) • C)]
    _ ≤ 2 * ((3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2) +
        2 * (s ^ 2 + δ) ^ (σ - 3 / 2) * ‖C‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hr)]
      have ht₁' : ‖E₁‖ ≤ (3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2 := ht₁
      linarith
    _ ≤ _ := by dsimp [A] at *; nlinarith [mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp),
      mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg C))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u18} [Fintype n] [DecidableEq n]

lemma continuous_quadratic_cfc {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Continuous (fun s : ℝ ↦ cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s)) := by
  exact Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (Filter.univ_mem) (by
    unfold quadraticMatrix
    fun_prop) (fun s ↦ quadraticMatrix_hermitian hC hB s)
      (primitive_differentiable σ hδ).continuous.continuousOn

lemma continuous_pairedFieldIntegrand {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Continuous (pairedFieldIntegrand σ δ C B) := by
  unfold pairedFieldIntegrand
  exact ((continuous_quadratic_cfc hδ σ hC hB).add
    ((continuous_quadratic_cfc hδ σ hC hB).comp continuous_neg)).sub
    (((continuous_const.mul ((primitive_differentiable σ hδ).continuous.comp
      (continuous_pow 2)))).smul continuous_const)

lemma integrable_pairedFieldIntegrand {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Integrable (pairedFieldIntegrand σ δ C B) := by
  apply MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (continuous_pairedFieldIntegrand hδ σ hC hB).locallyIntegrable
    (g := fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2))
  · exact Filter.Eventually.of_forall (fun s ↦ congrArg norm
      ((pairedFieldIntegrand_even σ δ C B s).symm))
  · apply Asymptotics.IsBigO.of_bound
      (2 * (3 / 2 - σ) * (1 / 4 : ℝ) ^ (σ - 5 / 2) * (‖C‖ + 2 * ‖B‖) ^ 2 +
        2 * ‖C‖ * (1 / 2 : ℝ) ^ (σ - 3 / 2))
    filter_upwards [eventually_ge_atTop (max 1 (2 * (‖C‖ + 2 * ‖B‖)))] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + s ^ 2) _)]
    exact pairedFieldIntegrand_bound hσ hδ hC hB hs
  · exact (normalization_integrable hσ).integrableAtFilter atTop

def fieldIntegrand (σ δ : ℝ) (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • 1

def hermitianField (σ δ : ℝ) (C B : Matrix n n ℂ) : Matrix n n ℂ :=
  (fieldNormalization σ / 2) • ∫ s : ℝ, pairedFieldIntegrand σ δ C B s

lemma continuous_fieldIntegrand {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Continuous (fieldIntegrand σ δ C B) :=
  (continuous_quadratic_cfc hδ σ hC hB).sub
    (((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2)).smul continuous_const)

lemma cutoff_paired_identity {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (R : ℝ) :
    (∫ s in -R..R, pairedFieldIntegrand σ δ C B s) =
      (2 : ℝ) • ∫ s in -R..R, fieldIntegrand σ δ C B s := by
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have he : pairedFieldIntegrand σ δ C B = fun s ↦
      fieldIntegrand σ δ C B s + fieldIntegrand σ δ C B (-s) := by
    funext s
    simp only [pairedFieldIntegrand, fieldIntegrand, neg_sq]
    module
  rw [he]
  dsimp only
  erw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    ((hc.comp continuous_neg).intervalIntegrable _ _)]
  have hn := intervalIntegral.integral_comp_neg (f := fieldIntegrand σ δ C B) (a := -R) (b := R)
  simp only [neg_neg] at hn
  simp only [Function.comp_apply]
  erw [hn]
  module

lemma hermitianField_cutoff_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ C B s)
      atTop (𝓝 (hermitianField σ δ C B)) := by
  have hi := integrable_pairedFieldIntegrand hσ hδ hC hB
  have ht := intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
  have hh := ht.const_smul (fieldNormalization σ / 2)
  simp only [id_eq] at hh
  convert! hh using 1
  funext R
  rw [cutoff_paired_identity hδ σ hC hB, smul_smul]
  congr 1
  ring

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
