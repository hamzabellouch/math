import OAI.Analysis.AllenCahn.Hessian

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff

lemma inverseHessian_drift_abs_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j : Fin n) (x : Space n) :
    |Laplacian.laplacian (inverseHessian v i j) x -
      fderiv ℝ (inverseHessian v i j) x (diffuseDrift v x)| ≤
      (2 + 4 * n + 4 * n * (12 * (2 * Real.sqrt 2 + 1))) *
        (diffuseDefect v x + Real.sqrt (hessianSquare v x)) := by
  let K := 12 * (2 * Real.sqrt 2 + 1)
  let S := Real.sqrt (hessianSquare v x)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ diffuseDefect v x := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hD1 := diffuseDefect_le_one v x
  have hv1 : |v x| ≤ 1 := abs_le.mpr ⟨(hi x).1.le, (hi x).2.le⟩
  have hq0 : 0 ≤ defectWeight v x := (weight_pos (hi x)).le
  have hq1 : |defectWeight v x| ≤ 1 := by
    rw [abs_of_nonneg hq0]
    dsimp [defectWeight]
    nlinarith [sq_nonneg (v x)]
  have hsr : |Real.sqrt 2| ≤ 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hp (k : Fin n) : |coordDeriv (inverseProfile v) k x| ≤ 1 :=
    (coordDeriv_abs_le_gradient _ _ _).trans (inverseProfile_gradient_bound (smooth_C2 hv) hi hAC x)
  have hT1 : |-defectWeight v x * diffuseDefect v x * inverseHessian v i j x| ≤ S := by
    simp only [abs_mul, abs_neg]
    rw [abs_of_nonneg hD]
    simpa using mul_le_mul (mul_le_mul hq1 hD1 hD (by norm_num))
      (inverseHessian_abs_le_sqrt v i j x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
  have hT2 : |Real.sqrt 2 * v x * defectWeight v x * diffuseDefect v x *
      coordDeriv (inverseProfile v) i x * coordDeriv (inverseProfile v) j x| ≤ 2 * diffuseDefect v x := by
    simp only [abs_mul]
    rw [abs_of_nonneg hD]
    calc |Real.sqrt 2| * |v x| * |defectWeight v x| * diffuseDefect v x *
        |coordDeriv (inverseProfile v) i x| * |coordDeriv (inverseProfile v) j x| ≤
        2 * 1 * 1 * diffuseDefect v x * 1 * 1 := by
          gcongr
          · exact hp i
          · exact hp j
      _ = _ := by ring
  have hT3 : |defectWeight v x * (coordDeriv (inverseProfile v) i x * coordDeriv (diffuseDefect v) j x +
      coordDeriv (inverseProfile v) j x * coordDeriv (diffuseDefect v) i x)| ≤ 4 * n * S := by
    rw [abs_mul]
    calc |defectWeight v x| * |coordDeriv (inverseProfile v) i x * coordDeriv (diffuseDefect v) j x +
        coordDeriv (inverseProfile v) j x * coordDeriv (diffuseDefect v) i x| ≤
      1 * (|coordDeriv (inverseProfile v) i x * coordDeriv (diffuseDefect v) j x| +
        |coordDeriv (inverseProfile v) j x * coordDeriv (diffuseDefect v) i x|) :=
          mul_le_mul hq1 (abs_add_le _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (1 * (2 * n * S) + 1 * (2 * n * S)) := by
        simp only [abs_mul]
        gcongr
        · exact hp i
        · exact coordDeriv_diffuseDefect_bound hv hi hAC j x
        · exact hp j
        · exact coordDeriv_diffuseDefect_bound hv hi hAC i x
      _ = _ := by ring
  have hT4 : |2 * Real.sqrt 2 * v x * (∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x)| ≤
      4 * n * K * S := by
    have hsum : |∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x| ≤ n * K * S := by
      calc |∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x| ≤
          ∑ k : Fin n, |inverseHessian v i k x * inverseHessian v k j x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, K * S := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (inverseHessian_abs_le hv hi hAC i k x)
            (inverseHessian_abs_le_sqrt v k j x) (abs_nonneg _) hK
        _ = _ := by simp; ring
    simp only [abs_mul]
    calc |(2 : ℝ)| * |Real.sqrt 2| * |v x| * |∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x| ≤
        2 * 2 * 1 * (n * K * S) := by
          norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          apply mul_le_mul _ hsum (abs_nonneg _) (by norm_num)
          have hh := mul_le_mul hsr hv1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
          nlinarith
        _ = _ := by ring
  rw [inverseHessian_drift_system hv hi hAC]
  have hsum : |-defectWeight v x * diffuseDefect v x * inverseHessian v i j x +
      Real.sqrt 2 * v x * defectWeight v x * diffuseDefect v x * coordDeriv (inverseProfile v) i x *
        coordDeriv (inverseProfile v) j x -
      defectWeight v x * (coordDeriv (inverseProfile v) i x * coordDeriv (diffuseDefect v) j x +
        coordDeriv (inverseProfile v) j x * coordDeriv (diffuseDefect v) i x) +
      2 * Real.sqrt 2 * v x * (∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x)| ≤
      S + 2 * diffuseDefect v x + 4 * n * S + 4 * n * K * S :=
    (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hT1 hT2)) hT3)) hT4)
  apply hsum.trans
  change S + 2 * diffuseDefect v x + 4 * n * S + 4 * n * K * S ≤
    (2 + 4 * n + 4 * n * K) * (diffuseDefect v x + S)
  have hh : 0 ≤ (4 * n + 4 * n * K) * diffuseDefect v x := by positivity
  nlinarith

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma bounded_quadratic_maximum {n : ℕ} {f : Space n → ℝ}
    (hf : Continuous f) {M ε : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M)
    (hε : 0 < ε) :
    ∃ x : Space n, ∀ y, f y - ε * ‖y‖ ^ 2 ≤ f x - ε * ‖x‖ ^ 2 := by
  let H : Space n → ℝ := fun x => f x - ε * ‖x‖ ^ 2
  have hc : Continuous H := by fun_prop
  let R := Real.sqrt (2 * M / ε + 1)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * M / ε + 1 := Real.sq_sqrt (by positivity)
  have hevent : ∀ᶠ x in cocompact (Space n), H x ≤ H 0 := by
    filter_upwards [(isCompact_closedBall (0 : Space n) R).compl_mem_cocompact] with x hx
    have hx' : R < ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hs : 2 * M / ε + 1 < ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hh := mul_lt_mul_of_pos_left hs hε
    have he : ε * (2 * M / ε + 1) = 2 * M + ε := by field_simp
    rw [he] at hh
    have hb₁ := (abs_le.mp (hb x)).2
    have hb₂ := (abs_le.mp (hb 0)).1
    dsimp [H]
    simp only [norm_zero, zero_pow two_ne_zero, mul_zero, sub_zero]
    linarith
  exact hc.exists_forall_ge' 0 hevent

lemma bounded_drift_threshold {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M B C η : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hη : 0 < η)
    (hb : ∀ x, |f x| ≤ M) (hbdrift : ∀ x, ‖b x‖ ≤ B)
    (hpde : ∀ x, C < f x → η ≤ Laplacian.laplacian f x - fderiv ℝ f x (b x)) :
    ∀ x, f x ≤ C := by
  intro x₀
  by_contra hbad
  have hgap : 0 < f x₀ - C := sub_pos.mpr (lt_of_not_ge hbad)
  let err : ℝ → ℝ := fun t => 2 * n * t + 2 * B * Real.sqrt (2 * M * t)
  have hc : Continuous err := by dsimp [err]; fun_prop
  have hn : ∀ᶠ t : ℝ in 𝓝 0,
      err t < η ∧ t * ‖x₀‖ ^ 2 < f x₀ - C := by
    have h₁ : ∀ᶠ t : ℝ in 𝓝 0, err t < η :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa [err] using hη)
    have h₂ : ∀ᶠ t : ℝ in 𝓝 0, t * ‖x₀‖ ^ 2 < f x₀ - C :=
      (isOpen_lt (continuous_id.mul continuous_const) continuous_const).mem_nhds
        (by simpa using hgap)
    exact h₁.and h₂
  obtain ⟨ε, hε, herror, hεgap⟩ := (frequently_gt_nhds (0 : ℝ)).and_eventually hn |>.exists
  obtain ⟨x, hm⟩ := bounded_quadratic_maximum hf.continuous hM hb hε
  have hval : C < f x := by
    have hx := hm x₀
    nlinarith [mul_nonneg hε.le (sq_nonneg ‖x‖)]
  have hp := hpde x hval
  have hpen : ε * ‖x‖ ^ 2 ≤ 2 * M := by
    have hx := hm 0
    simp only [norm_zero, zero_pow two_ne_zero, mul_zero, sub_zero] at hx
    have hb₁ := (abs_le.mp (hb x)).2
    have hb₂ := (abs_le.mp (hb 0)).1
    linarith
  have hnorm : ContDiff ℝ 2 (fun z : Space n => ‖z‖ ^ 2) := contDiff_id.norm_sq ℝ
  have hF : ContDiff ℝ 2 (fun z : Space n => f z - ε * ‖z‖ ^ 2) :=
    hf.sub (contDiff_const.mul hnorm)
  have hmax : IsLocalMax (fun z : Space n => f z - ε * ‖z‖ ^ 2) x :=
    Filter.Eventually.of_forall hm
  have hl := laplacian_nonpos_of_local_max hF hmax
  rw [laplacian_fun_sub hf (contDiff_const.mul hnorm),
    laplacian_fun_const_mul hnorm, laplacian_norm_sq] at hl
  have hdq : HasFDerivAt (fun z : Space n => ε * ‖z‖ ^ 2)
      (ε • ((2 : ℝ) • innerSL ℝ x)) x := by
    have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul ε
    simpa only [← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] using hd
  have hz := hmax.hasFDerivAt_eq_zero (((hf.differentiable (by norm_num) x).hasFDerivAt).sub hdq)
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (b x)) hz
  simp only [sub_apply, smul_apply, smul_eq_mul, zero_apply, innerSL_apply_apply] at he
  have hsmall : ε * ‖x‖ ≤ Real.sqrt (2 * M * ε) := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * M * ε by positivity)
    have hh := mul_le_mul_of_nonneg_right hpen hε.le
    nlinarith [Real.sqrt_nonneg (2 * M * ε), norm_nonneg x]
  have hg : |fderiv ℝ f x (b x)| ≤ 2 * B * Real.sqrt (2 * M * ε) := by
    have he' : fderiv ℝ f x (b x) = 2 * ε * inner ℝ x (b x) := by linarith
    rw [he', abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε)]
    calc 2 * ε * |inner ℝ x (b x)| ≤ 2 * ε * (‖x‖ * ‖b x‖) :=
           mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
         _ ≤ 2 * ε * (‖x‖ * B) := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left (hbdrift x) (norm_nonneg x)) (by positivity)
         _ ≤ 2 * B * Real.sqrt (2 * M * ε) := by nlinarith
  have hgg := (abs_le.mp hg).1
  dsimp [err] at herror
  linarith

lemma bounded_drift_linear {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M B C : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ M) (hbdrift : ∀ x, ‖b x‖ ≤ B)
    (hpde : ∀ x, f x - C ≤ Laplacian.laplacian f x - fderiv ℝ f x (b x)) :
    ∀ x, f x ≤ C := by
  intro x
  apply le_of_forall_pos_le_add
  intro ε hε
  apply bounded_drift_threshold hf b hM hB hε hb hbdrift
  intro y hy
  exact (by linarith : ε ≤ f y - C).trans (hpde y)

lemma bounded_drift_logistic {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M B C : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ M) (hbdrift : ∀ x, ‖b x‖ ≤ B)
    (hpde : ∀ x, f x ^ 2 - C * f x - C ≤
      Laplacian.laplacian f x - fderiv ℝ f x (b x)) :
    ∀ x, f x ≤ C + 1 := by
  apply bounded_drift_threshold hf b hM hB (by norm_num : (0 : ℝ) < 1) hb hbdrift
  intro y hy
  apply le_trans _ (hpde y)
  have hh : 0 ≤ (f y - (C + 1)) * (f y + 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma laplacian_fun_mul {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    Laplacian.laplacian (fun y => f y * g y) x =
      f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
        2 * inner ℝ (gradient f x) (gradient g x) := by
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  rw [laplacian_eq_sum_coordDeriv (hf.mul hg), laplacian_eq_sum_coordDeriv hf,
    laplacian_eq_sum_coordDeriv hg, inner_gradient_eq_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hc : coordDeriv (fun y => f y * g y) i =
      fun y => f y * coordDeriv g i y + g y * coordDeriv f i y :=
    funext (coordDeriv_mul hd he i)
  rw [hc]
  have hdi := (coordDeriv_contDiff hf i).differentiable (by norm_num)
  have hei := (coordDeriv_contDiff hg i).differentiable (by norm_num)
  have hsum : coordDeriv (fun y => f y * coordDeriv g i y + g y * coordDeriv f i y) i x =
      coordDeriv (fun y => f y * coordDeriv g i y) i x +
      coordDeriv (fun y => g y * coordDeriv f i y) i x := by
    change fderiv ℝ (fun y => f y * coordDeriv g i y + g y * coordDeriv f i y) x (basis n i) = _
    rw [fderiv_fun_add ((hd.fun_mul hei) x) ((he.fun_mul hdi) x)]
    rfl
  rw [hsum, coordDeriv_mul hd hei, coordDeriv_mul he hdi]
  ring

lemma drift_quotient_identity {n : ℕ} {f d : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hd : ContDiff ℝ 2 d) (hnz : ∀ x, d x ≠ 0)
    (b : Space n → Space n) (x : Space n) :
    let w := fun y => f y / d y
    d x * (Laplacian.laplacian w x -
        fderiv ℝ w x (b x - (2 / d x) • gradient d x)) =
      (Laplacian.laplacian f x - fderiv ℝ f x (b x)) -
        w x * (Laplacian.laplacian d x - fderiv ℝ d x (b x)) := by
  dsimp only
  let w := fun y => f y / d y
  have hw : ContDiff ℝ 2 w := hf.div hd hnz
  have he : f = fun y => w y * d y := by funext y; dsimp [w]; field_simp [hnz y]
  have hL := laplacian_fun_mul hw hd x
  rw [← he] at hL
  have hf' : fderiv ℝ f x (b x) =
      w x * fderiv ℝ d x (b x) + d x * fderiv ℝ w x (b x) := by
    conv_lhs => rw [he]
    rw [fderiv_fun_mul (hw.differentiable (by norm_num) x) (hd.differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  change d x * (Laplacian.laplacian w x - _) = _ - w x * _
  rw [hL, hf', map_sub, map_smul, smul_eq_mul]
  simp only [← inner_gradient_left]
  field_simp [hnz x]
  ring

lemma quotient_bernstein {n : ℕ} {f d : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hd : ContDiff ℝ 2 d) (b : Space n → Space n)
    {M B G A c : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hdb : ∀ x, 0 ≤ d x ∧ d x ≤ 1)
    (hbb : ∀ x, ‖b x‖ ≤ B) (hgb : ∀ x, ‖gradient d x‖ ≤ G)
    (hfde : ∀ x, -A * (f x + d x ^ 2) ≤
      Laplacian.laplacian f x - fderiv ℝ f x (b x))
    (hdde : ∀ x, Laplacian.laplacian d x - fderiv ℝ d x (b x) ≤ c * d x - 2 * f x) :
    ∀ x, f x ≤ (A + c + 1) * d x := by
  have hδ {δ : ℝ} (hδ : 0 < δ) (x : Space n) : f x ≤ (A + c + 1) * (d x + δ) := by
    let e := fun y => d y + δ
    let w := fun y => f y / e y
    let b' := fun y => b y - (2 / e y) • gradient d y
    have he : ContDiff ℝ 2 e := hd.add contDiff_const
    have hep (y : Space n) : 0 < e y := by dsimp [e]; linarith [(hdb y).1]
    have heδ (y : Space n) : δ ≤ e y := by dsimp [e]; linarith [(hdb y).1]
    have hw : ContDiff ℝ 2 w := hf.div he (fun y => (hep y).ne')
    have hwe (y : Space n) : w y * e y = f y := by dsimp [w]; field_simp [(hep y).ne']
    have hwp (y : Space n) : 0 ≤ w y := div_nonneg (hfb y).1 (hep y).le
    have hwb (y : Space n) : |w y| ≤ M / δ := by
      rw [abs_of_nonneg (hwp y)]
      exact div_le_div₀ hM (hfb y).2 hδ (heδ y)
    have hb'b (y : Space n) : ‖b' y‖ ≤ B + 2 / δ * G := by
      calc ‖b' y‖ ≤ ‖b y‖ + ‖(2 / e y) • gradient d y‖ := norm_sub_le _ _
           _ = ‖b y‖ + 2 / e y * ‖gradient d y‖ := by
             rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) (hep y))]
           _ ≤ B + 2 / δ * G := add_le_add (hbb y)
             (mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hδ (heδ y)) (hgb y)
               (norm_nonneg _) (by positivity))
    have hele (y : Space n) : Laplacian.laplacian e y = Laplacian.laplacian d y := by
      rw [laplacian_fun_add hd contDiff_const]
      simp
    have hef (y : Space n) : fderiv ℝ e y = fderiv ℝ d y := by
      dsimp [e]
      rw [fderiv_fun_add (hd.differentiable (by norm_num) y) (differentiableAt_const δ)]
      simp
    have heg (y : Space n) : gradient e y = gradient d y := by simp only [gradient, hef]
    have hwde (y : Space n) : w y ^ 2 - (A + c) * w y - (A + c) ≤
        Laplacian.laplacian w y - fderiv ℝ w y (b' y) := by
      have hI := drift_quotient_identity hf he (fun z => (hep z).ne') b y
      change e y * (Laplacian.laplacian w y -
          fderiv ℝ w y (b y - (2 / e y) • gradient e y)) = _ - w y * _ at hI
      rw [heg, hele, hef] at hI
      have h₁ := hfde y
      have h₂ := mul_le_mul_of_nonneg_left (hdde y) (hwp y)
      have h₃ : d y ^ 2 ≤ e y := by dsimp [e]; nlinarith [(hdb y).1, (hdb y).2]
      have h₄ : c * w y * d y ≤ c * w y * e y :=
        mul_le_mul_of_nonneg_left (by dsimp [e]; linarith) (mul_nonneg hc (hwp y))
      have h₅ := mul_le_mul_of_nonneg_left h₃ hA
      have h₆ : 0 ≤ w y ^ 2 * e y := mul_nonneg (sq_nonneg _) (hep y).le
      have h₇ : 0 ≤ c * e y := mul_nonneg hc (hep y).le
      apply (mul_le_mul_iff_right₀ (hep y)).mp
      dsimp only [b']
      rw [← hwe y] at h₁ h₂
      nlinarith
    have hh := bounded_drift_logistic hw b'
      (show 0 ≤ M / δ by positivity) (show 0 ≤ B + 2 / δ * G by positivity)
      (add_nonneg hA hc) hwb hb'b hwde x
    have hh' := mul_le_mul_of_nonneg_right hh (hep x).le
    rw [hwe] at hh'
    exact hh'
  intro x
  by_contra h
  have hh : 0 < f x - (A + c + 1) * d x := sub_pos.mpr (lt_of_not_ge h)
  let δ := (f x - (A + c + 1) * d x) / (2 * (A + c + 1))
  have hK : 0 < A + c + 1 := by linarith
  have hδp : 0 < δ := div_pos hh (by linarith)
  have hh' := hδ hδp x
  dsimp [δ] at hh'
  have hrel : (A + c + 1) * ((f x - (A + c + 1) * d x) / (2 * (A + c + 1))) =
      (f x - (A + c + 1) * d x) / 2 := by field_simp
  rw [mul_add, hrel] at hh'
  linarith

lemma drift_square_identity {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) (x : Space n) :
    Laplacian.laplacian (fun y => f y ^ 2) x - fderiv ℝ (fun y => f y ^ 2) x (b x) =
      2 * ‖gradient f x‖ ^ 2 +
        2 * f x * (Laplacian.laplacian f x - fderiv ℝ f x (b x)) := by
  rw [laplacian_sq hf, fderiv_fun_pow 2 (hf.differentiable (by norm_num) x)]
  simp only [Nat.add_one_sub_one, pow_one, smul_apply, smul_eq_mul]
  ring

end DeGiorgi
end

end OAI
