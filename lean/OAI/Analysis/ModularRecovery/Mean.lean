import OAI.Analysis.ModularRecovery.FiniteMoments

namespace OAI

/-! The fixed free-ultrafilter mean of symmetric Lebesgue averages and orbit defects. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma exists_finite_moment_average (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {y : H →L[ℂ] H} (hy : y ∈ S.M) :
    ∃ (n : ℕ) (p t : Fin n → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (S.state ((S.modularAverage p t (star y * y)) ^ 2)).re ≤
        (‖y S.xi‖ ^ 2 + 1) ^ 2 ∧
      (∑ i, p i * (S.state (star (S.sigma (t i) y) *
        S.modularAverage p t (y * star y) * S.sigma (t i) y)).re) ≤
        ‖y S.xi‖ ^ 2 * ‖star y S.xi‖ ^ 2 + 1 := by
  let q : ℝ := ‖y S.xi‖ ^ 2
  let b : ℝ := ‖star y S.xi‖ ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hbn : b ≤ ‖y‖ ^ 2 := by
    simpa only [b, norm_star] using S.norm_state_real_star_mul (star y)
  have hyn : 0 ≤ 2 * ‖y‖ ^ 2 := by positivity
  obtain ⟨delta,hdelta,hcontrol⟩ := small_on_separating_controls_vector
    S.M S.xi S.separating (y S.xi) hyn (show 0 < 1/(‖y S.xi‖+1) by positivity)
  obtain ⟨n,p,t,hp,hsum,hA,hB⟩ := S.exists_finite_average_pair hscalar
    (mul_mem (star_mem hy) hy) (mul_mem hy (star_mem hy)) (lt_min one_pos hdelta)
  let A := S.modularAverage p t (star y * y)
  let B := S.modularAverage p t (y * star y)
  let C := S.modularAverage p (fun i => -t i) B
  have hAsmall : ‖A S.xi - (q : ℂ) • S.xi‖ < 1 := by
    have := hA.trans_le (min_le_left _ _)
    simpa only [A, S.modularAverage_apply_xi, S.state_star_mul, q] using this
  have hBsmall : ‖B S.xi - (b : ℂ) • S.xi‖ < delta := by
    have := hB.trans_le (min_le_right _ _)
    simpa only [B, S.modularAverage_apply_xi, S.state_mul_star, b] using this
  have hCsmall : ‖C S.xi - (b : ℂ) • S.xi‖ < delta :=
    (S.norm_modularAverage_apply_xi_sub_le p (fun i => -t i) hp hsum B b).trans_lt hBsmall
  have hBmem : B ∈ S.M := S.modularAverage_mem p t (mul_mem hy (star_mem hy))
  have hCmem : C ∈ S.M := S.modularAverage_mem p _ hBmem
  have hCn : ‖C‖ ≤ ‖y‖ ^ 2 := by
    calc
      _ ≤ ‖B‖ := S.norm_modularAverage_le p _ hp hsum B
      _ ≤ ‖y * star y‖ := S.norm_modularAverage_le p t hp hsum _
      _ = ‖y‖ ^ 2 := by rw [CStarRing.norm_self_mul_star, pow_two]
  have hCbn : ‖C - b • (1 : H →L[ℂ] H)‖ ≤ 2 * ‖y‖ ^ 2 := by
    calc
      _ ≤ ‖C‖ + ‖b • (1 : H →L[ℂ] H)‖ := norm_sub_le _ _
      _ ≤ ‖y‖ ^ 2 + b := add_le_add hCn (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
        exact mul_le_of_le_one_right hb ContinuousLinearMap.norm_id_le)
      _ ≤ _ := by linarith
  have hCd : ‖(C - b • (1 : H →L[ℂ] H)) S.xi‖ < delta := by
    change ‖C S.xi - b • S.xi‖ < delta
    rwa [← algebraMap_smul ℂ b S.xi]
  refine ⟨n,p,t,hp,hsum,?_,?_⟩
  · have hAn : ‖A S.xi‖ ≤ q + 1 := by
      have hc : ‖(q : ℂ) • S.xi‖ = q := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, S.norm_xi, mul_one]
      have hh := norm_le_norm_sub_add (A S.xi) ((q : ℂ) • S.xi)
      rw [hc] at hh
      linarith
    have hAA : IsSelfAdjoint A := by
      dsimp only [A]
      rw [← S.averageSquare_eq]
      exact isSelfAdjoint_averageSquare p _
    rw [S.state_sq_re hAA]
    exact pow_le_pow_left₀ (norm_nonneg _) hAn 2
  · rw [S.modularAverage_sandwich]
    have hh := hcontrol (C - b • (1 : H →L[ℂ] H))
      (sub_mem hCmem (S.real_smul_mem (one_mem S.M) b)) hCbn hCd
    have hr := re_inner_operator_le_of_small (y S.xi) C b hh
    dsimp [q,b] at *
    nlinarith

end StandardModularData
end BoundedRecovery

namespace BoundedRecovery

lemma norm_symmetricAverage_le (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C) (k : ℕ) : ‖symmetricAverage f k‖ ≤ C := by
  by_cases hk : k = 0
  · simp [symmetricAverage, hk, hC]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(k : ℝ)) (b := (k : ℝ)) (fun t _ => hf t)
  have hab : |(k : ℝ) - -(k : ℝ)| = 2 * (k : ℝ) := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [hab] at hb
  rw [symmetricAverage, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  calc
    _ ≤ (2 * (k : ℝ))⁻¹ * (C * (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

lemma tendsto_symmetricAverage_mean (omega : Ultrafilter ℕ)
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (symmetricAverage f) (omega : Filter ℕ) (𝓝 (fixedMean omega f)) := by
  obtain ⟨v,hv,ht⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (symmetricAverage f) omega)
    (show (Ultrafilter.map (symmetricAverage f) omega : Filter ℝ) ≤
      𝓟 (Icc (-‖f‖) ‖f‖) from by
      rw [Filter.le_principal_iff]
      change ∀ᶠ k : ℕ in (omega : Filter ℕ), symmetricAverage f k ∈ Icc (-‖f‖) ‖f‖
      exact Filter.Eventually.of_forall (fun k =>
        abs_le.mp (norm_symmetricAverage_le f (norm_nonneg _) f.norm_coe_le_norm k)))
  have h : Tendsto (symmetricAverage f) (omega : Filter ℕ) (𝓝 v) := ht
  simpa only [fixedMean, h.limUnder_eq] using h

lemma norm_fixedMean_le (omega : Ultrafilter ℕ) (f : BoundedContinuousFunction ℝ ℝ) :
    ‖fixedMean omega f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_symmetricAverage_mean omega f).norm
    (Filter.Eventually.of_forall (norm_symmetricAverage_le f (norm_nonneg _) f.norm_coe_le_norm))

lemma symmetricAverage_add (f g : BoundedContinuousFunction ℝ ℝ) (k : ℕ) :
    symmetricAverage (f+g) k = symmetricAverage f k + symmetricAverage g k := by
  simp only [symmetricAverage, Pi.add_apply,
    intervalIntegral.integral_add (f.continuous.intervalIntegrable _ _)
      (g.continuous.intervalIntegrable _ _), mul_add]

lemma symmetricAverage_smul (c : ℝ) (f : BoundedContinuousFunction ℝ ℝ) (k : ℕ) :
    symmetricAverage (c • f) k = c * symmetricAverage f k := by
  simp only [symmetricAverage, Pi.smul_apply, smul_eq_mul,
    intervalIntegral.integral_const_mul]
  ring

lemma fixedMean_add (omega : Ultrafilter ℕ) (f g : BoundedContinuousFunction ℝ ℝ) :
    fixedMean omega (f+g) = fixedMean omega f + fixedMean omega g := by
  apply tendsto_nhds_unique (tendsto_symmetricAverage_mean omega (f+g))
  change Tendsto (fun k => symmetricAverage (f+g) k) _ _
  simp_rw [symmetricAverage_add]
  exact
    (tendsto_symmetricAverage_mean omega f).add (tendsto_symmetricAverage_mean omega g)

lemma fixedMean_smul (omega : Ultrafilter ℕ) (c : ℝ) (f : BoundedContinuousFunction ℝ ℝ) :
    fixedMean omega (c • f) = c * fixedMean omega f := by
  apply tendsto_nhds_unique (tendsto_symmetricAverage_mean omega (c • f))
  change Tendsto (fun k => symmetricAverage (c • f) k) _ _
  simp_rw [symmetricAverage_smul]
  exact (tendsto_symmetricAverage_mean omega f).const_mul c

def meanCLM (omega : Ultrafilter ℕ) : (BoundedContinuousFunction ℝ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => fixedMean omega f
      map_add' := fixedMean_add omega
      map_smul' := fixedMean_smul omega }
    1 (by intro f; simpa using norm_fixedMean_le omega f)

@[simp] lemma meanCLM_apply (omega : Ultrafilter ℕ) (f : BoundedContinuousFunction ℝ ℝ) :
    meanCLM omega f = fixedMean omega f := rfl

lemma symmetricAverage_mono (f g : BoundedContinuousFunction ℝ ℝ)
    (hfg : ∀ t, f t ≤ g t) (k : ℕ) : symmetricAverage f k ≤ symmetricAverage g k := by
  unfold symmetricAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono_on (by linarith [Nat.cast_nonneg (α := ℝ) k])
    (f.continuous.intervalIntegrable _ _) (g.continuous.intervalIntegrable _ _)
    (fun t _ => hfg t)

lemma fixedMean_mono (omega : Ultrafilter ℕ) (f g : BoundedContinuousFunction ℝ ℝ)
    (hfg : ∀ t, f t ≤ g t) : fixedMean omega f ≤ fixedMean omega g := by
  exact le_of_tendsto_of_tendsto (tendsto_symmetricAverage_mean omega f)
    (tendsto_symmetricAverage_mean omega g)
    (Filter.Eventually.of_forall (symmetricAverage_mono f g hfg))

lemma symmetricAverage_const (c : ℝ) {k : ℕ} (hk : k ≠ 0) :
    symmetricAverage (fun _ => c) k = c := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [symmetricAverage, intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma fixedMean_const (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop) (c : ℝ) :
    fixedMean omega (fun _ => c) = c := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [hω (eventually_ge_atTop 1)] with k hk
  exact (symmetricAverage_const c (by omega)).symm

def translateBCF (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) :
    BoundedContinuousFunction ℝ ℝ := f.compContinuous ⟨fun t => t+r, by fun_prop⟩

@[simp] lemma translateBCF_apply (f : BoundedContinuousFunction ℝ ℝ) (r t : ℝ) :
    translateBCF f r t = f (t+r) := rfl

lemma norm_symmetricAverage_translate_sub_le (f : BoundedContinuousFunction ℝ ℝ)
    (r : ℝ) (k : ℕ) :
    ‖symmetricAverage (translateBCF f r) k - symmetricAverage f k‖ ≤
      (2 * (k : ℝ))⁻¹ * (2 * ‖f‖ * |r|) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f.continuous.intervalIntegrable (-(k : ℝ)) (k : ℝ))
    (f.continuous.intervalIntegrable (k : ℝ) ((k : ℝ)+r))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f.continuous.intervalIntegrable (-(k : ℝ)) (-(k : ℝ)+r))
    (f.continuous.intervalIntegrable (-(k : ℝ)+r) ((k : ℝ)+r))
  have he : (∫ t in -(k : ℝ)+r..(k : ℝ)+r, f t) - (∫ t in -(k : ℝ)..(k : ℝ), f t) =
      (∫ t in (k : ℝ)..(k : ℝ)+r, f t) - (∫ t in -(k : ℝ)..-(k : ℝ)+r, f t) := by
    linarith
  have hb (a : ℝ) : ‖∫ t in a..a+r, f t‖ ≤ ‖f‖ * |r| := by
    simpa only [add_sub_cancel_left] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := a+r) (fun t _ => f.norm_coe_le_norm t)
  simp only [symmetricAverage, translateBCF_apply,
    intervalIntegral.integral_comp_add_right, ← mul_sub, he, norm_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * (k : ℝ))⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (by linarith [hb (k : ℝ), hb (-(k : ℝ))])

lemma tendsto_symmetricAverage_translate_sub (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) :
    Tendsto (fun k => symmetricAverage (translateBCF f r) k - symmetricAverage f k)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_symmetricAverage_translate_sub_le f r)
  have hk : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith [Nat.cast_nonneg (α := ℝ) k])
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
  simpa only [zero_mul, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hk).mul_const (2*‖f‖*|r|)

lemma fixedMean_translate (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop)
    (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) :
    fixedMean omega (translateBCF f r) = fixedMean omega f := by
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique
    ((tendsto_symmetricAverage_mean omega (translateBCF f r)).sub
      (tendsto_symmetricAverage_mean omega f))
    ((tendsto_symmetricAverage_translate_sub f r).mono_left hω)

lemma exists_lt_of_lt_fixedMean (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop)
    (f : BoundedContinuousFunction ℝ ℝ) {c : ℝ} (hc : c < fixedMean omega f) :
    ∃ t, c < f t := by
  by_contra! hn
  have hm := fixedMean_mono omega f (BoundedContinuousFunction.const ℝ c) hn
  rw [show (BoundedContinuousFunction.const ℝ c : ℝ → ℝ) = (fun _ => c) from rfl,
    fixedMean_const omega hω c] at hm
  exact (not_le_of_gt hc) hm

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

def orbitDefect (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h : H) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => ‖T (D.unitary t h)‖ ^ 2)
    ((T.continuous.comp (D.continuous_unitary_apply h)).norm.pow 2) (‖T‖ ^ 2 * ‖h‖ ^ 2) (by
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := T.le_opNorm (D.unitary t h)
      rw [D.norm_unitary_apply] at hb
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2)

@[simp] lemma orbitDefect_apply (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h : H) (t : ℝ) :
    D.orbitDefect T h t = ‖T (D.unitary t h)‖ ^ 2 := rfl

lemma norm_orbitDefect_le (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h : H) :
    ‖D.orbitDefect T h‖ ≤ ‖T‖ ^ 2 * ‖h‖ ^ 2 := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  rw [orbitDefect_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [D.norm_unitary_apply, mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (D.unitary t h)) 2

lemma orbitDefect_unitary (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (r : ℝ) (h : H) :
    D.orbitDefect T (D.unitary r h) = translateBCF (D.orbitDefect T h) r := by
  ext t
  simp only [orbitDefect_apply, translateBCF_apply, D.unitary_add]
  rfl

lemma norm_orbitDefect_sub_le (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h k : H) :
    ‖D.orbitDefect T h - D.orbitDefect T k‖ ≤ ‖T‖ ^ 2 * (‖h‖+‖k‖) * ‖h-k‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖‖T (D.unitary t h)‖ ^ 2 - ‖T (D.unitary t k)‖ ^ 2‖ ≤ _
  have hb (v : H) : ‖T (D.unitary t v)‖ ≤ ‖T‖ * ‖v‖ := by
    simpa only [D.norm_unitary_apply] using T.le_opNorm (D.unitary t v)
  have hd : |‖T (D.unitary t h)‖ - ‖T (D.unitary t k)‖| ≤ ‖T‖ * ‖h-k‖ := by
    exact (abs_norm_sub_norm_le _ _).trans (by simpa only [map_sub] using hb (h-k))
  rw [Real.norm_eq_abs, sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm]
  calc
    _ ≤ (‖T‖ * ‖h-k‖) * (‖T‖ * ‖h‖ + ‖T‖ * ‖k‖) :=
      mul_le_mul hd (add_le_add (hb h) (hb k)) (by positivity) (by positivity)
    _ = _ := by ring

lemma abs_mean_orbitDefect_sub_le (D : RealSpectralCalculus H) (omega : Ultrafilter ℕ)
    (T : H →L[ℂ] H) (h k : H) :
    |fixedMean omega (D.orbitDefect T h) - fixedMean omega (D.orbitDefect T k)| ≤
      ‖T‖ ^ 2 * (‖h‖+‖k‖) * ‖h-k‖ := by
  have hm := norm_fixedMean_le omega (D.orbitDefect T h - D.orbitDefect T k)
  change ‖meanCLM omega (D.orbitDefect T h - D.orbitDefect T k)‖ ≤ _ at hm
  rw [map_sub] at hm
  exact hm.trans (D.norm_orbitDefect_sub_le T h k)

lemma mean_orbitDefect_nonneg (D : RealSpectralCalculus H) (omega : Ultrafilter ℕ)
    (T : H →L[ℂ] H) (h : H) : 0 ≤ fixedMean omega (D.orbitDefect T h) := by
  have hh := fixedMean_mono omega 0 (D.orbitDefect T h) (fun t => sq_nonneg _)
  have hz : fixedMean omega (0 : BoundedContinuousFunction ℝ ℝ) = 0 :=
    (meanCLM omega).map_zero
  rwa [hz] at hh

lemma mean_orbitDefect_le (D : RealSpectralCalculus H) (omega : Ultrafilter ℕ)
    (T : H →L[ℂ] H) (h : H) :
    fixedMean omega (D.orbitDefect T h) ≤ ‖T‖ ^ 2 * ‖h‖ ^ 2 :=
  (le_abs_self _).trans ((norm_fixedMean_le omega _).trans (D.norm_orbitDefect_le T h))

end RealSpectralCalculus
end BoundedRecovery

end
end

end OAI
