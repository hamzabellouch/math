import OAI.Geometry.Kahler.HartogsMatrixBounds

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma normalError_HHHH {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a b c d : Fin 2) :
    normalError f lam w (some a) (some b) (some c) (some d) =
      -(barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedFourth f (0,w) a.castSucc b.castSucc c.castSucc d.castSucc +
      (barrierX (normalLogWeight f w (0,w)) : ℂ)^2 *
        (∑ e : Fin 2, ∑ k : Fin 2,
          (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))))⁻¹ e k *
          liftedThird f (0,w) a.castSucc c.castSucc e.castSucc *
          star (liftedThird f (0,w) b.castSucc d.castSucc k.castSucc)) := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalError, Pi.sub_apply, normalCurvature, pullTensor, verticalScale, normalIndex,
    Complex.ofReal_one, one_mul, principal_HHHH]
  rw [normalPotential_curvature_HHHH hf lam w hn hG', complex_horizontalMetric]
  simp only [barrierQ]
  ring

lemma normalError_HHHV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a b c : Fin 2) :
    normalError f lam w (some a) (some b) (some c) none =
      (Real.sqrt (barrierQ (normalLogWeight f w (0,w))) : ℂ) *
        (-liftedThird f (0,w) a.castSucc c.castSucc b.castSucc +
          (barrierX (normalLogWeight f w (0,w)) : ℂ) *
            (∑ e : Fin 2, ∑ k : Fin 2,
              (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))))⁻¹ e k *
              liftedThird f (0,w) a.castSucc c.castSucc e.castSucc * star (baseHessian f 0 b k))) := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalError, Pi.sub_apply, normalCurvature, pullTensor, verticalScale, normalIndex,
    Complex.ofReal_one, one_mul, principal_HHHV, sub_zero]
  rw [normalPotential_curvature_HHHV hf lam w hn hG', complex_horizontalMetric]
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).2.1
  linear_combination (-liftedThird f (0,w) a.castSucc c.castSucc b.castSucc +
    (barrierX (normalLogWeight f w (0,w)) : ℂ) *
      (∑ e : Fin 2, ∑ k : Fin 2,
        (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))))⁻¹ e k *
        liftedThird f (0,w) a.castSucc c.castSucc e.castSucc * star (baseHessian f 0 b k))) * hs

lemma componentNorm_bound {T : Tensor Index} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a b c d, ‖T a b c d‖ ≤ M) : componentNorm T ≤ 9*M := by
  unfold componentNorm
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    ∑ t : Quad Index, Complex.normSq (T t.1 t.2.1 t.2.2.1 t.2.2.2) ≤
        ∑ _ : Quad Index, M^2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (h _ _ _ _) 2
    _ = (9*M)^2 := by norm_num [Fintype.card_prod, Fintype.card_option]; ring

lemma horizontalPart4_bound {T : Tensor Index} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a b c d : Fin 2, ‖T (some a) (some b) (some c) (some d)‖ ≤ M) :
    componentNorm (horizontalPart 4 T) ≤ 9*M := by
  apply componentNorm_bound hM
  intro a b c d
  cases a <;> cases b <;> cases c <;> cases d <;> simp [horizontalPart, horizontalCount, hM, h]

lemma horizontalPart3_bound {T : Tensor Index} {M : ℝ} (hM : 0 ≤ M) (hT : Symmetries T)
    (h : ∀ a b c : Fin 2, ‖T (some a) (some b) (some c) none‖ ≤ M) :
    componentNorm (horizontalPart 3 T) ≤ 9*M := by
  apply componentNorm_bound hM
  intro a b c d
  cases a <;> cases b <;> cases c <;> cases d <;> simp [horizontalPart, horizontalCount, hM]
  all_goals first
    | exact h _ _ _
    | (rw [hT.anti]; exact h _ _ _)
    | (rw [← norm_star, hT.reality]; exact h _ _ _)
    | (rw [hT.hol, ← norm_star, hT.reality]; exact h _ _ _)

lemma matrix_triple_sum_bound {A : Matrix (Fin 2) (Fin 2) ℂ} {u v : Fin 2 → ℂ}
    {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hA : ∀ i j, ‖A i j‖ ≤ r) (hu : ∀ i, ‖u i‖ ≤ s) (hv : ∀ j, ‖v j‖ ≤ t) :
    ‖∑ i, ∑ j, A i j * u i * v j‖ ≤ 4*r*s*t := by
  calc
    _ ≤ ∑ i, ‖∑ j, A i j * u i * v j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, r*s*t := by
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (hv j)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
          (mul_le_mul
            (mul_le_mul (hA i j) (hu i) (norm_nonneg _) hr)
            le_rfl ht (mul_nonneg hr hs))
    _ = _ := by simp; ring

lemma scaled_inverse_contraction_bound {c C lam x : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlam : 0 < lam) (hx : 0 ≤ x) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * euclidean.q w)
    (u v : Fin 2 → ℂ) (hub : ∀ i, ‖u i‖ ≤ C) (hvb : ∀ j, ‖v j‖ ≤ C) :
    x * ‖∑ i, ∑ j, (horizontalMetric A lam x)⁻¹ i j * u i * v j‖ ≤ 4*C^2/c := by
  have hd : 0 < lam+x*c := add_pos_of_pos_of_nonneg hlam (mul_nonneg hx hc.le)
  have hb := matrix_triple_sum_bound (inv_nonneg.mpr hd.le) hC hC
    (horizontal_inverse_bound hc hlam hx A hA hl hu) hub hvb
  have hc' : x*(lam+x*c)⁻¹ ≤ c⁻¹ := by
    have hh : x/(lam+x*c) ≤ 1/c := (div_le_div_iff₀ hd hc).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hh
  calc
    _ ≤ x*(4*(lam+x*c)⁻¹*C*C) := mul_le_mul_of_nonneg_left hb hx
    _ = (4*C^2)*(x*(lam+x*c)⁻¹) := by ring
    _ ≤ (4*C^2)*c⁻¹ := mul_le_mul_of_nonneg_left hc' (by positivity)
    _ = _ := by ring

lemma normalErrors_bounds {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C) (hlam : 0 < lam)
    (hl : ∀ u, c * euclidean.q u ≤ (form (baseHessian f 0)
      (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u)
    (hu : ∀ u, (form (baseHessian f 0)
      (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C * euclidean.q u)
    (hJ : ∀ a c d : Fin 2, ‖liftedThird f (0,0) a.castSucc c.castSucc d.castSucc‖ ≤ C)
    (hB : ∀ a b c d : Fin 2, ‖liftedFourth f (0,0) a.castSucc b.castSucc c.castSucc d.castSucc‖ ≤ C)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    componentNorm (horizontalPart 4 (normalError f lam w)) ≤
      (9*(C+4*C^2/c)) * barrierX (normalLogWeight f w (0,w)) ∧
    componentNorm (horizontalPart 3 (normalError f lam w)) ≤
      (9*(C+4*C^2/c)) * Real.sqrt (barrierQ (normalLogWeight f w (0,w))) := by
  let x := barrierX (normalLogWeight f w (0,w))
  let q := barrierQ (normalLogWeight f w (0,w))
  have hx : 0 ≤ x := (barrierX_positive hn).le
  have hq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hCp : 0 ≤ C := hc.le.trans hC
  have hH := baseHessian_isHermitian (hf.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top))
  have hG : (horizontalMetric (baseHessian f 0) lam x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (positive_horizontalMetric hc hlam hx _ hH hl).isUnit)
  have hh (i j : Fin 2) : ‖baseHessian f 0 i j‖ ≤ C :=
    hermitian_entry_bound hCp _ hH (fun u =>
      (mul_nonneg hc.le (euclidean.nonneg_of_pos form_one_pos u)).trans (hl u)) hu i j
  have hJw (a c d : Fin 2) : ‖liftedThird f (0,w) a.castSucc c.castSucc d.castSucc‖ ≤ C := by
    simpa only [liftedThird_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
      liftedThird_horizontal (q := (0,0)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))] using hJ a c d
  have hBw (a b c d : Fin 2) : ‖liftedFourth f (0,w) a.castSucc b.castSucc c.castSucc d.castSucc‖ ≤ C := by
    simpa only [liftedFourth_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
      liftedFourth_horizontal (q := (0,0)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))] using hB a b c d
  have hK : 0 ≤ C+4*C^2/c := by positivity
  constructor
  · have hb := horizontalPart4_bound (T := normalError f lam w) (M := x*(C+4*C^2/c)) (mul_nonneg hx hK) (by
      intro a b j d
      rw [normalError_HHHH hf lam w hn hG]
      let U := ∑ e : Fin 2, ∑ k : Fin 2, (horizontalMetric (baseHessian f 0) lam x)⁻¹ e k *
        liftedThird f (0,w) a.castSucc j.castSucc e.castSucc * star (liftedThird f (0,w) b.castSucc d.castSucc k.castSucc)
      have hU : x*‖U‖ ≤ 4*C^2/c := scaled_inverse_contraction_bound hc hCp hlam hx _ hH hl hu
        (fun e => liftedThird f (0,w) a.castSucc j.castSucc e.castSucc)
        (fun k => star (liftedThird f (0,w) b.castSucc d.castSucc k.castSucc))
        (hJw a j) (fun k => by simpa only [norm_star] using hJw b d k)
      have hn' := norm_add_le (-(x : ℂ)*liftedFourth f (0,w) a.castSucc b.castSucc j.castSucc d.castSucc) ((x : ℂ)^2*U)
      simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at hn'
      change ‖-(x : ℂ)*liftedFourth f (0,w) a.castSucc b.castSucc j.castSucc d.castSucc + (x : ℂ)^2*U‖ ≤ _
      nlinarith only [hn', mul_le_mul_of_nonneg_left (hBw a b j d) hx, mul_le_mul_of_nonneg_left hU hx])
    change componentNorm _ ≤ (9*(C+4*C^2/c))*x
    nlinarith only [hb]
  · have hb := horizontalPart3_bound (T := normalError f lam w) (M := Real.sqrt q*(C+4*C^2/c))
      (mul_nonneg hq hK) (normalError_symmetries hf lam w hn) (by
        intro a b j
        rw [normalError_HHHV hf lam w hn hG]
        let U := ∑ e : Fin 2, ∑ k : Fin 2, (horizontalMetric (baseHessian f 0) lam x)⁻¹ e k *
          liftedThird f (0,w) a.castSucc j.castSucc e.castSucc * star (baseHessian f 0 b k)
        have hU : x*‖U‖ ≤ 4*C^2/c := scaled_inverse_contraction_bound hc hCp hlam hx _ hH hl hu
          (fun e => liftedThird f (0,w) a.castSucc j.castSucc e.castSucc)
          (fun k => star (baseHessian f 0 b k))
          (hJw a j) (fun k => by simpa only [norm_star] using hh b k)
        have hn' := norm_add_le (-liftedThird f (0,w) a.castSucc j.castSucc b.castSucc) ((x : ℂ)*U)
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at hn'
        change ‖(Real.sqrt q : ℂ)*(-liftedThird f (0,w) a.castSucc j.castSucc b.castSucc + (x : ℂ)*U)‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
        apply mul_le_mul_of_nonneg_left _ hq
        linarith only [hn', hJw a j b, hU])
    change componentNorm _ ≤ (9*(C+4*C^2/c))*Real.sqrt q
    nlinarith only [hb]

end PinchedHartogs

end

end OAI
