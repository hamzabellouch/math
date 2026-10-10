import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SobolevDensityInput

namespace OAI

/-! Compact cutoffs of actual smooth weak-H1 vectors. This is the cutoff
step needed after the published smooth-density theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

private theorem cutoff_complex_C1 {n : ℕ} (χ : Configuration n → ℝ)
    (hχ : ContDiff ℝ 1 χ) : ContDiff ℝ 1 (fun x => (χ x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hχ

def smoothCutoffState {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s)) (χ : Configuration n → ℝ)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) : Coulomb.H1Vector n :=
  classicalH1State (fun s x => (χ x : ℂ) * u.value s x)
    (fun s => (cutoff_complex_C1 χ hχ).mul (hu s))
    (fun s => ((cutoff_complex_C1 χ hχ).mul (hu s)).continuous.memLp_of_hasCompactSupport
      ((hc.comp_left Complex.ofReal_zero).mul_right))
    (fun s a =>
      (show Continuous (fun x => fderiv ℝ (fun y => (χ y : ℂ) * u.value s y) x
        (EuclideanSpace.single a 1)) from
          (((cutoff_complex_C1 χ hχ).mul (hu s)).continuous_fderiv (by norm_num)).clm_apply
            continuous_const).memLp_of_hasCompactSupport
        (((hc.comp_left Complex.ofReal_zero).mul_right).fderiv_apply ℝ _))

theorem smoothCutoffState_gradient {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s))
    (hd : ∀ s a x, fderiv ℝ (u.value s) x (EuclideanSpace.single a 1) = u.gradient s a x)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (smoothCutoffState u hu χ hχ hc).gradient s a x =
      (fderiv ℝ χ x (EuclideanSpace.single a 1) : ℂ) * u.value s x +
        (χ x : ℂ) * u.gradient s a x := by
  change fderiv ℝ (fun y => (χ y : ℂ) * u.value s y) x (EuclideanSpace.single a 1) = _
  have hfχ := Complex.ofRealCLM.hasFDerivAt.comp x
    (hχ.differentiable (by norm_num) x).hasFDerivAt
  have hf := hfχ.mul (hu s |>.differentiable (by norm_num) x).hasFDerivAt
  have he := congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1)) hf.fderiv
  calc
    _ = (χ x : ℂ) * u.gradient s a x +
        u.value s x * (fderiv ℝ χ x (EuclideanSpace.single a 1) : ℂ) := by
      simpa only [Pi.mul_def, Function.comp_def, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, hd] using he
    _ = _ := by ring

/-- Dominated convergence for the two terms in the cutoff product rule. -/
theorem cutoff_product_error_tendsto {n : ℕ}
    (f g : Configuration n → ℂ) (hf : MemLp f 2) (hg : MemLp g 2)
    (a b : ℕ → Configuration n → ℝ)
    (ha : ∀ k, Continuous (a k)) (hb : ∀ k, Continuous (b k))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : ∀ k x, |a k x| ≤ A ∧ |b k x| ≤ B)
    (hat : ∀ x, Tendsto (fun k => a k x) atTop (𝓝 0))
    (hbt : ∀ x, Tendsto (fun k => b k x) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖(a k x : ℂ) * f x + (b k x : ℂ) * g x‖^2)
      atTop (𝓝 0) := by
  have hfi : Integrable (fun x => ‖f x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi : Integrable (fun x => ‖g x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  suffices hlim : Tendsto
      (fun k => ∫ x, ‖(a k x : ℂ)*f x + (b k x : ℂ)*g x‖^2)
      atTop (𝓝 (∫ _ : Configuration n, (0 : ℝ))) by
    simpa only [integral_zero] using hlim
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*A^2*‖f x‖^2 + 2*B^2*‖g x‖^2)
  · intro k
    exact ((((Complex.continuous_ofReal.comp (ha k)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).add
      ((Complex.continuous_ofReal.comp (hb k)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable)).norm.pow 2)
  · exact (hfi.const_mul (2*A^2)).add (hgi.const_mul (2*B^2))
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have he : ‖(a k x : ℂ)*f x + (b k x : ℂ)*g x‖ ≤ A*‖f x‖ + B*‖g x‖ := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hab k x).1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hab k x).2 (norm_nonneg _))
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _)))).mpr he
    nlinarith [sq_nonneg (A*‖f x‖ - B*‖g x‖)]
  · filter_upwards [] with x
    have ht := (((Complex.continuous_ofReal.tendsto 0).comp (hat x)).mul_const (f x)).add
      (((Complex.continuous_ofReal.tendsto 0).comp (hbt x)).mul_const (g x))
    simpa using ht.norm.pow 2

theorem smoothCutoffState_error_tendsto {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ 1 (u.value s))
    (hd : ∀ s a x, fderiv ℝ (u.value s) x (EuclideanSpace.single a 1) = u.gradient s a x)
    (χ : ℕ → Configuration n → ℝ) (hχ : ∀ k, ContDiff ℝ 1 (χ k))
    (hc : ∀ k, HasCompactSupport (χ k))
    (D : ℝ) (hb : ∀ k x, |χ k x| ≤ 1)
    (hdb : ∀ k a x, |fderiv ℝ (χ k) x (EuclideanSpace.single a 1)| ≤ D)
    (ht : ∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1))
    (hdt : ∀ a x, Tendsto (fun k => fderiv ℝ (χ k) x (EuclideanSpace.single a 1))
      atTop (𝓝 0)) :
    Tendsto (fun k => h1GraphError u (smoothCutoffState u hu (χ k) (hχ k) (hc k)))
      atTop (𝓝 0) := by
  have hχb (k : ℕ) (x : Configuration n) : |χ k x - 1| ≤ 2 := by
    calc
      _ ≤ |χ k x| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 := by simpa only [abs_one] using (show |χ k x| + 1 ≤ 2 by linarith [hb k x])
  have hv (s : SpinConfiguration n) :
      Tendsto (fun k => ∫ x, ‖u.value s x -
        (smoothCutoffState u hu (χ k) (hχ k) (hc k)).value s x‖^2) atTop (𝓝 0) := by
    have h := cutoff_product_error_tendsto (u.value s) (u.value s)
      (u.value_L2 s) (u.value_L2 s)
      (fun k x => χ k x - 1) (fun _ _ => 0)
      (fun k => (hχ k).continuous.sub continuous_const) (fun _ => continuous_const)
      2 0 (by norm_num) le_rfl (fun k x => ⟨hχb k x, by simp⟩)
      (fun x => by simpa using (ht x).sub_const 1) (fun _ => tendsto_const_nhds)
    convert h using 1
    funext k
    apply integral_congr_ae
    filter_upwards [] with x
    change ‖u.value s x - (χ k x : ℂ)*u.value s x‖^2 = _
    rw [norm_sub_rev]
    congr 2
    push_cast
    ring
  have hg (s : SpinConfiguration n) (a : Fin n × Fin 3) :
      Tendsto (fun k => ∫ x, ‖u.gradient s a x -
        (smoothCutoffState u hu (χ k) (hχ k) (hc k)).gradient s a x‖^2) atTop (𝓝 0) := by
    have h := cutoff_product_error_tendsto (u.value s) (u.gradient s a)
      (u.value_L2 s) (u.partial_L2 s a)
      (fun k x => fderiv ℝ (χ k) x (EuclideanSpace.single a 1)) (fun k x => χ k x - 1)
      (fun k => ((hχ k).continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (fun k => (hχ k).continuous.sub continuous_const)
      |D| 2 (abs_nonneg D) (by norm_num)
      (fun k x => ⟨(hdb k a x).trans (le_abs_self D), hχb k x⟩)
      (hdt a) (fun x => by simpa using (ht x).sub_const 1)
    convert h using 1
    funext k
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smoothCutoffState_gradient u hu hd, norm_sub_rev]
    congr 2
    push_cast
    ring
  simpa only [h1GraphError, Finset.sum_const_zero, zero_add] using
    (tendsto_finsetSum _ (fun s _ => hv s)).add
      (tendsto_finsetSum _ (fun s _ => tendsto_finsetSum _ (fun a _ => hg s a)))

/-- Every smooth actual H1 vector is the graph-norm limit of compactly
supported C1 vectors, using the existing full-space cutoff construction. -/
theorem exists_compact_approximation_of_smooth {n : ℕ} (u : Coulomb.H1Vector n)
    (hu : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (u.value s))
    (hd : ∀ s a x, u.gradient s a x = fderiv ℝ (u.value s) x (EuclideanSpace.single a 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨χ, D, hχ, hc, hb, hdb, ht, hdt⟩ := Coulomb.exists_hardyCutoffs n
  have hu₁ : ∀ s, ContDiff ℝ 1 (u.value s) := fun s => (hu s).of_le (by simp)
  have hχ₁ : ∀ k, ContDiff ℝ 1 (χ k) := fun k => (hχ k).of_le (by simp)
  have he := smoothCutoffState_error_tendsto u hu₁ (fun s a x => (hd s a x).symm)
    χ hχ₁ hc D hb hdb ht hdt
  obtain ⟨k, hk⟩ := (he.eventually (gt_mem_nhds hε)).exists
  refine ⟨smoothCutoffState u hu₁ (χ k) (hχ₁ k) (hc k), fun s => ?_,
    fun _ _ _ => rfl, hk⟩
  exact ⟨(cutoff_complex_C1 _ (hχ₁ k)).mul (hu₁ s),
    ((hc k).comp_left Complex.ofReal_zero).mul_right⟩

end ContinuumCoulomb

end

end OAI
