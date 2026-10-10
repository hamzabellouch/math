import Mathlib

namespace OAI

/-! Real-frequency fast averaging on the compact slow circle. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace ThreeTorus

private abbrev fastHaar : Measure UnitAddCircle := AddCircle.haarAddCircle
private abbrev fastProduct : Measure (UnitAddTorus (Fin 2)) :=
  Measure.pi (fun _ => fastHaar)

private lemma fast_integral_character (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z ∂fastHaar) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := fastHaar)
      (fourier_add_half_inv_index hk (by norm_num))

private lemma fast_integral_mFourier (nu : Fin 2 → ℤ) :
    (∫ z : UnitAddTorus (Fin 2), UnitAddTorus.mFourier nu z ∂fastProduct) =
      if nu = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) 0 nu
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    eq_comm, MeasureSpace.pi, instMeasureSpaceUnitAddCircle] using! h

def fastOrbit (n : ℕ) (beta : UnitAddCircle) (z : UnitAddCircle) : UnitAddTorus (Fin 2) :=
  ![z,(n:ℤ) • z+beta]

lemma continuous_fastOrbit (n : ℕ) (beta : UnitAddCircle) : Continuous (fastOrbit n beta) := by
  unfold fastOrbit
  fun_prop

private lemma fast_integrable_diag (F : C(UnitAddTorus (Fin 2),ℂ)) (n : ℕ) (beta : UnitAddCircle) :
    Integrable (fun z => F (fastOrbit n beta z)) fastHaar :=
  (F.continuous.comp (continuous_fastOrbit n beta)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private lemma fast_integrable_prod (F : C(UnitAddTorus (Fin 2),ℂ)) :
    Integrable F fastProduct := F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma fast_mFourier_diagonal (nu : Fin 2 → ℤ) (n : ℕ) (beta z : UnitAddCircle) :
    UnitAddTorus.mFourier nu (fastOrbit n beta z) =
      fourier (nu 1) beta * fourier (nu 0+nu 1*(n:ℤ)) z := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,
    fastOrbit,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [fourier_apply,zsmul_add,smul_smul,AddCircle.toCircle_add,Circle.coe_mul,
    add_zsmul]
  ring

lemma fast_mFourier_limit (nu : Fin 2 → ℤ) (beta : ℕ → UnitAddCircle) :
    Tendsto (fun n => ∫ z, UnitAddTorus.mFourier nu (fastOrbit n (beta n) z) ∂fastHaar)
      atTop (𝓝 (∫ z, UnitAddTorus.mFourier nu z ∂fastProduct)) := by
  classical
  simp_rw [fast_mFourier_diagonal,integral_const_mul,fast_integral_character]
  rw [fast_integral_mFourier]
  by_cases hz : nu = 0
  · subst nu
    simp
  · rw [ite_eq_right hz]
    have hf : ∀ᶠ n : ℕ in atTop, nu 0+nu 1*(n:ℤ) ≠ 0 := by
      by_cases h1 : nu 1 = 0
      · have h0 : nu 0 ≠ 0 := by
          intro h0
          apply hz
          ext i
          fin_cases i <;> assumption
        exact Eventually.of_forall (fun n => by simpa [h1] using h0)
      · have hinj : Function.Injective (fun n : ℕ => nu 0+nu 1*(n:ℤ)) := by
          intro a b hab
          exact_mod_cast mul_left_cancel₀ h1 (add_left_cancel hab)
        have ht := hinj.tendsto_cofinite
        rw [Nat.cofinite_eq_atTop] at ht
        exact ht.eventually (eventually_cofinite_ne 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [hf] with n hn
    simp [hn]

lemma fast_polynomial_limit (F : C(UnitAddTorus (Fin 2),ℂ))
    (hF : F ∈ Submodule.span ℂ (range (UnitAddTorus.mFourier (d := Fin 2))))
    (beta : ℕ → UnitAddCircle) :
    Tendsto (fun n => ∫ z, F (fastOrbit n (beta n) z) ∂fastHaar)
      atTop (𝓝 (∫ z, F z ∂fastProduct)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨nu,rfl⟩ := h
    exact fast_mFourier_limit nu beta
  | zero => simp
  | add F G _ _ ihF ihG =>
    simp only [ContinuousMap.add_apply]
    simp_rw [integral_add (fast_integrable_diag F _ _) (fast_integrable_diag G _ _)]
    rw [integral_add (fast_integrable_prod F) (fast_integrable_prod G)]
    exact ihF.add ihG
  | smul a F _ ih =>
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    simp_rw [integral_const_mul]
    exact tendsto_const_nhds.mul ih

lemma fast_average_diagonal_dist (F G : C(UnitAddTorus (Fin 2),ℂ))
    (n : ℕ) (beta : UnitAddCircle) :
    dist (∫ z, F (fastOrbit n beta z) ∂fastHaar) (∫ z, G (fastOrbit n beta z) ∂fastHaar) ≤
      dist F G := by
  rw [dist_eq_norm,dist_eq_norm,← integral_sub (fast_integrable_diag F n beta)
    (fast_integrable_diag G n beta)]
  apply (norm_integral_le_of_norm_le_const (C := ‖F-G‖) ?_).trans_eq (by simp)
  exact Eventually.of_forall (fun z => (F-G).norm_coe_le_norm (fastOrbit n beta z))

lemma fast_average_product_dist (F G : C(UnitAddTorus (Fin 2),ℂ)) :
    dist (∫ z, F z ∂fastProduct) (∫ z, G z ∂fastProduct) ≤ dist F G := by
  rw [dist_eq_norm,dist_eq_norm,← integral_sub (fast_integrable_prod F) (fast_integrable_prod G)]
  apply (norm_integral_le_of_norm_le_const (C := ‖F-G‖) ?_).trans_eq (by simp)
  exact Eventually.of_forall (fun z => (F-G).norm_coe_le_norm z)

/-- Fast averaging on the two-torus, uniform over any sequence of offsets.
This is the compact quotient form of source Lemma `fast-average`. -/
lemma fast_average_torus (F : C(UnitAddTorus (Fin 2),ℂ)) (beta : ℕ → UnitAddCircle) :
    Tendsto (fun n => ∫ z, F (fastOrbit n (beta n) z) ∂fastHaar)
      atTop (𝓝 (∫ z, F z ∂fastProduct)) := by
  have hd : F ∈ closure (↑(Submodule.span ℂ (range
      (UnitAddTorus.mFourier (d := Fin 2)))) : Set C(UnitAddTorus (Fin 2),ℂ)) := by
    rw [← Submodule.topologicalClosure_coe,UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨G,hG,hdist⟩ := Metric.mem_closure_iff.mp hd (eps/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (fast_polynomial_limit G hG beta) (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 := fast_average_diagonal_dist F G n (beta n)
  have h2 := fast_average_product_dist G F
  have h3 := hN n hn
  have h4 := dist_triangle (∫ z, F (fastOrbit n (beta n) z) ∂fastHaar)
    (∫ z, G (fastOrbit n (beta n) z) ∂fastHaar) (∫ z, F z ∂fastProduct)
  have h5 := dist_triangle (∫ z, G (fastOrbit n (beta n) z) ∂fastHaar)
    (∫ z, G z ∂fastProduct) (∫ z, F z ∂fastProduct)
  rw [dist_comm G F] at h2
  linarith

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Filter Set Function
open scoped Topology BigOperators

/-- Rescale a compactly supported real frequency variable to one fundamental
interval. Its endpoints vanish, so the quotient is genuinely continuous. -/
def compactRealTorus (H : ℝ × UnitAddCircle → ℂ) (hH : Continuous H) (M : ℕ) :
    UnitAddCircle → C(UnitAddCircle,ℂ) :=
  AddCircle.liftIoc 1 0 (fun x : ℝ =>
    (ContinuousMap.curry ⟨H,hH⟩) ((2*(M:ℝ))*x-M))

lemma continuous_compactRealTorus {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0) :
    Continuous (compactRealTorus H hH M) := by
  apply AddCircle.liftIoc_zero_continuous
  · ext y
    change H ((2*(M:ℝ))*0-M,y) = H ((2*(M:ℝ))*1-M,y)
    rw [show (2*(M:ℝ))*0-M = -(M:ℝ) by ring,
      show (2*(M:ℝ))*1-M = (M:ℝ) by ring]
    rw [hS _ _ (by simp),hS _ _ (by simp)]
  · exact ((ContinuousMap.curry ⟨H,hH⟩).continuous.comp
      ((continuous_const.mul continuous_id).sub continuous_const)).continuousOn

lemma compactRealTorus_coe {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    (M : ℕ) {x : ℝ} (hx : x ∈ Ioc 0 1) (y : UnitAddCircle) :
    compactRealTorus H hH M (x:UnitAddCircle) y = H ((2*(M:ℝ))*x-M,y) := by
  rw [compactRealTorus,AddCircle.liftIoc_coe_apply (by simpa using hx)]
  rfl

lemma compact_rescale_integral {f : ℝ → ℂ} {M : ℕ} (hM : 0 < M)
    (hS : ∀ s, (M:ℝ) ≤ |s| → f s = 0) :
    (2*(M:ℝ)) • (∫ x in Ioc (0:ℝ) 1, f ((2*(M:ℝ))*x-M)) = ∫ s, f s := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have he := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) f
    (by positivity : 2*(M:ℝ) ≠ 0) (-(M:ℝ))
  simp only [mul_zero,zero_add,mul_one,show 2*(M:ℝ)+ -(M:ℝ) = (M:ℝ) by ring] at he
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  simp_rw [sub_eq_add_neg]
  rw [he,smul_smul,mul_inv_cancel₀ (by positivity : 2*(M:ℝ) ≠ 0),one_smul,
    intervalIntegral.integral_of_le (by linarith : -(M:ℝ) ≤ M)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs
  apply hS
  by_contra hn
  have hh := abs_lt.mp (lt_of_not_ge hn)
  exact hs ⟨hh.1,hh.2.le⟩

lemma circle_fast_rescale (n M : ℕ) (x : ℝ) :
    (((n:ℝ)*((2*(M:ℝ))*x-M) : ℝ):UnitAddCircle) =
      ((n*(2*M):ℕ):ℤ) • (x:UnitAddCircle) := by
  have he : (n:ℝ)*((2*(M:ℝ))*x-M) = ((n*(2*M):ℕ):ℝ)*x-((n*M:ℕ):ℝ) := by
    push_cast
    ring
  rw [he,AddCircle.coe_sub]
  have hz : (((n*M:ℕ):ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨(n*M:ℕ),by simp⟩
  rw [hz,sub_zero]
  simpa only [zsmul_eq_mul,Int.cast_natCast] using
    (AddCircle.coe_zsmul (p := (1:ℝ)) (n := ((n*(2*M):ℕ):ℤ)) (x := x))

lemma compactRealTorus_integral {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0)
    (n : ℕ) (β : UnitAddCircle) :
    (2*(M:ℝ)) • (∫ x, compactRealTorus H hH M x
      (((n*(2*M):ℕ):ℤ) • x+β) ∂AddCircle.haarAddCircle) =
      ∫ s, H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β) := by
  have he := AddCircle.integral_preimage 1 0 (fun x => compactRealTorus H hH M x
    (((n*(2*M):ℕ):ℤ) • x+β))
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  convert compact_rescale_integral (M := M) hM
    (f := fun s => H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β)) (fun s hs => hS s _ hs) using 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [compactRealTorus_coe hH M hx,circle_fast_rescale]

lemma compactRealTorus_marginal {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0) :
    (2*(M:ℝ)) • (∫ x, ∫ y, compactRealTorus H hH M x y
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle) =
      ∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle := by
  have he := AddCircle.integral_preimage 1 0 (fun x => ∫ y, compactRealTorus H hH M x y
    ∂AddCircle.haarAddCircle)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  convert compact_rescale_integral (M := M) hM
    (f := fun s => ∫ y, H (s,y) ∂AddCircle.haarAddCircle)
    (fun s hs => by simp only [hS s _ hs,integral_zero]) using 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply integral_congr_ae
  exact ae_of_all _ (fun y => compactRealTorus_coe hH M hx y)

/-- Source fast averaging on the real frequency axis, for compactly supported
continuous data and every sequence of circle offsets. The frequency parameter
is the actual passage integer, not a synthetic independent variable. -/
lemma fast_average_real_compact {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0)
    (β : ℕ → UnitAddCircle) :
    Tendsto (fun n : ℕ => ∫ s, H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β n)) atTop
      (𝓝 (∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle)) := by
  have hc := continuous_compactRealTorus hH hS
  let G : C(UnitAddTorus (Fin 2),ℂ) := ⟨fun z => compactRealTorus H hH M (z 0) (z 1),
    (hc.comp (continuous_apply 0)).eval (continuous_apply 1)⟩
  have hfreq : Tendsto (fun n : ℕ => n*(2*M)) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n (by omega)) tendsto_id
  have ht := ((fast_average_torus G (fun k => β (k/(2*M)))).comp hfreq).const_smul (2*(M:ℝ))
  have hi : (∫ z, G z ∂(Measure.pi fun _ : Fin 2 => AddCircle.haarAddCircle)) =
      ∫ x, ∫ y, compactRealTorus H hH M x y
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
    calc
      _ = ∫ p : UnitAddCircle × UnitAddCircle, compactRealTorus H hH M p.1 p.2
          ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle :=
        (measurePreserving_finTwoArrow AddCircle.haarAddCircle).integral_comp
          MeasurableEquiv.finTwoArrow.measurableEmbedding _
      _ = _ := integral_prod _ (((hc.comp continuous_fst).eval continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have htarget : (2*(M:ℝ)) • (∫ z, G z ∂(Measure.pi fun _ : Fin 2 => AddCircle.haarAddCircle)) =
      ∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle := by
    rw [hi]
    exact compactRealTorus_marginal hH hM hS
  rw [← htarget]
  apply ht.congr'
  filter_upwards [] with n
  change (2*(M:ℝ)) • (∫ x, compactRealTorus H hH M x
    (((n*(2*M):ℕ):ℤ) • x+β (n*(2*M)/(2*M))) ∂AddCircle.haarAddCircle) = _
  rw [Nat.mul_div_left n (by omega : 0 < 2*M)]
  exact compactRealTorus_integral hH hM hS n (β n)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter
open scoped Topology

lemma fast_average_real_compact_real {H : ℝ × UnitAddCircle → ℝ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0)
    (β : ℕ → UnitAddCircle) :
    Tendsto (fun n : ℕ => ∫ s, H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β n)) atTop
      (𝓝 (∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle)) := by
  have ht := fast_average_real_compact (Complex.continuous_ofReal.comp hH) hM
    (fun s y hs => by simp only [Function.comp_apply,hS s y hs,Complex.ofReal_zero]) β
  simp only [Function.comp_apply,integral_complex_ofReal] at ht
  simpa only [Function.comp_def,Complex.ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

end ThreeTorus

end

end

end OAI
