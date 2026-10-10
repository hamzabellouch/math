import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEulerTail
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.NumberTheory.LSeries.Deriv

namespace OAI

/-! Real-sigma integration of the logarithmic derivative. The real
logarithm of the norm is differentiated through normSq, so no branch
choice for the complex logarithm is needed. -/

namespace TwoPointCorrelations

open Set
open scoped Classical LSeries.notation

lemma mrt_hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x≠0) :
    HasDerivAt (fun y => Real.log ‖f y‖) (f'/f x).re x := by
  have hre : HasDerivAt (fun y => (f y).re) f'.re x := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun y => (f y).im) f'.im x := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hsq : HasDerivAt (fun y => Complex.normSq (f y))
      ((f'.re*(f x).re+(f x).re*f'.re)+(f'.im*(f x).im+(f x).im*f'.im)) x := by
    simpa only [Complex.normSq_apply, Pi.mul_apply, Pi.add_apply] using!
      (hre.mul hre).add (him.mul him)
  have hsq0 : Complex.normSq (f x)≠0 := by
    exact fun h => hne (Complex.normSq_eq_zero.mp h)
  have hh := (hsq.log hsq0).div_const 2
  have he : (fun y => Real.log (Complex.normSq (f y))/2) =
      (fun y => Real.log ‖f y‖) := by
    funext y
    rw [Complex.normSq_eq_norm_sq,Real.log_pow]
    ring
  rw [he] at hh
  convert hh using 1
  rw [Complex.div_re]
  ring

lemma mrt_log_norm_sigma_bound {f f' : ℝ → ℂ} {a b K : ℝ}
    (hab : a≤b) (hf : ∀x∈Icc a b,HasDerivAt f (f' x) x)
    (hne : ∀x∈Icc a b,f x≠0)
    (hbound : ∀x∈Ico a b,‖f' x/f x‖≤K) :
    |Real.log ‖f b‖-Real.log ‖f a‖|≤K*(b-a) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun x => Real.log ‖f x‖)
    (f' := fun x => (f' x/f x).re)
    (fun x hx => (mrt_hasDerivAt_log_norm (hf x hx) (hne x hx)).hasDerivWithinAt)
    (fun x hx => (by
      simpa only [Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (f' x/f x)).trans (hbound x hx))) b (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs] using hh

lemma mrt_log_norm_sigma_upper {f f' : ℝ → ℂ} {a b K : ℝ}
    (hab : a≤b) (hf : ∀x∈Icc a b,HasDerivAt f (f' x) x)
    (hne : ∀x∈Icc a b,f x≠0)
    (hbound : ∀x∈Ioo a b,(f' x/f x).re≤K) :
    Real.log ‖f b‖-Real.log ‖f a‖≤K*(b-a) := by
  by_cases heq : a=b
  · simp [heq]
  have hab' : a<b := lt_of_le_of_ne hab heq
  have hder (x : ℝ) (hx : x∈Icc a b) := mrt_hasDerivAt_log_norm (hf x hx) (hne x hx)
  have hc : ContinuousOn (fun x => Real.log ‖f x‖) (Icc a b) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope (fun x => Real.log ‖f x‖)
    (fun x => (f' x/f x).re) hab' hc
    (fun x hx => hder x (Ioo_subset_Icc_self hx))
  have hh := hbound c hc
  rw [he] at hh
  exact (div_le_iff₀ (sub_pos.mpr hab')).mp hh

lemma mrt_character_LSeries_real_deriv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0<q) (t : ℝ) {σ : ℝ} (hσ : 1<σ) :
    HasDerivAt (fun x : ℝ => L ↗χ ((x:ℂ)-(t:ℂ)*Complex.I))
      (deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)) σ := by
  have hs : 1<((σ:ℂ)-(t:ℂ)*Complex.I).re := by simpa using hσ
  have hconv : LSeries.abscissaOfAbsConv ↗χ<((σ:ℂ)-(t:ℂ)*Complex.I).re := by
    rw [χ.absicssaOfAbsConv_eq_one (Nat.ne_of_gt hq)]
    exact_mod_cast hs
  have hc := (LSeries_hasDerivAt hconv).differentiableAt.hasDerivAt
  have hh := hc.comp (σ:ℂ) ((hasDerivAt_id (σ:ℂ)).sub_const ((t:ℂ)*Complex.I))
  simpa only [mul_one, Function.comp_apply, id_eq] using! hh.comp_ofReal

theorem mrt_character_LSeries_sigma_ratio {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0<q) (t : ℝ) {Y X : ℕ} (hY : 1≤Real.log (Y:ℝ)) (hYX : Y≤X)
    {K : ℝ} (hK : 0≤K)
    (hbound : ∀ σ ∈ Ico (1+1/Real.log (X:ℝ)) (1+1/Real.log (Y:ℝ)),
      ‖logDeriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)‖≤K*Real.log (Y:ℝ)) :
    |Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
      Real.log ‖L ↗χ (1+(1/Real.log (Y:ℝ):ℝ)-(t:ℂ)*Complex.I)‖|≤K := by
  have hY0 : (0:ℝ)<Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hYXr : (Y:ℝ)≤X := by exact_mod_cast hYX
  have hlog : Real.log (Y:ℝ)≤Real.log (X:ℝ) := Real.log_le_log hY0 hYXr
  have hX : 1≤Real.log (X:ℝ) := hY.trans hlog
  have hLY : 0<Real.log (Y:ℝ) := by linarith
  have hLX : 0<Real.log (X:ℝ) := by linarith
  let a := 1+1/Real.log (X:ℝ)
  let b := 1+1/Real.log (Y:ℝ)
  have hab : a≤b := add_le_add_right (one_div_le_one_div_of_le hLY hlog) 1
  have ha : 1<a := by dsimp only [a]; linarith [one_div_pos.mpr hLX]
  have hf : ∀σ∈Icc a b,HasDerivAt
      (fun x : ℝ => L ↗χ ((x:ℂ)-(t:ℂ)*Complex.I))
      (deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)) σ :=
    fun σ hσ => mrt_character_LSeries_real_deriv χ hq t (ha.trans_le hσ.1)
  have hne : ∀σ∈Icc a b,L ↗χ ((σ:ℂ)-(t:ℂ)*Complex.I)≠0 := by
    intro σ hσ
    apply χ.LSeries_ne_zero_of_one_lt_re
    simpa using ha.trans_le hσ.1
  have hbnd : ∀σ∈Ico a b,
      ‖deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)/
        L ↗χ ((σ:ℂ)-(t:ℂ)*Complex.I)‖≤K*Real.log (Y:ℝ) := by
    intro σ hσ
    exact hbound σ hσ
  have hh := mrt_log_norm_sigma_bound hab hf hne hbnd
  have hwidth : b-a≤1/Real.log (Y:ℝ) := by
    dsimp only [a,b]
    linarith [one_div_pos.mpr hLX]
  have hcost : (K*Real.log (Y:ℝ))*(b-a)≤K := by
    calc
      _ ≤ (K*Real.log (Y:ℝ))*(1/Real.log (Y:ℝ)) :=
        mul_le_mul_of_nonneg_left hwidth (mul_nonneg hK hLY.le)
      _ = K := by field_simp
  have hh' := hh.trans hcost
  rw [abs_sub_comm] at hh'
  simpa only [a,b,Complex.ofReal_add,Complex.ofReal_one] using hh'

/-- The one-sided version is compatible with the principal-character
pole: only an upper bound for the real logarithmic derivative is used. -/
theorem mrt_character_LSeries_sigma_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0<q) (t : ℝ) {Y X : ℕ} (hY : 1≤Real.log (Y:ℝ)) (hYX : Y≤X)
    {K : ℝ} (hK : 0≤K)
    (hbound : ∀ σ ∈ Ioo (1+1/Real.log (X:ℝ)) (1+1/Real.log (Y:ℝ)),
      (logDeriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)).re≤K*Real.log (Y:ℝ)) :
    -K≤Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
      Real.log ‖L ↗χ (1+(1/Real.log (Y:ℝ):ℝ)-(t:ℂ)*Complex.I)‖ := by
  have hY0 : (0:ℝ)<Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hYXr : (Y:ℝ)≤X := by exact_mod_cast hYX
  have hlog : Real.log (Y:ℝ)≤Real.log (X:ℝ) := Real.log_le_log hY0 hYXr
  have hX : 1≤Real.log (X:ℝ) := hY.trans hlog
  have hLY : 0<Real.log (Y:ℝ) := by linarith
  have hLX : 0<Real.log (X:ℝ) := by linarith
  let a := 1+1/Real.log (X:ℝ)
  let b := 1+1/Real.log (Y:ℝ)
  have hab : a≤b := add_le_add_right (one_div_le_one_div_of_le hLY hlog) 1
  have ha : 1<a := by dsimp only [a]; linarith [one_div_pos.mpr hLX]
  have hf : ∀σ∈Icc a b,HasDerivAt
      (fun x : ℝ => L ↗χ ((x:ℂ)-(t:ℂ)*Complex.I))
      (deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)) σ :=
    fun σ hσ => mrt_character_LSeries_real_deriv χ hq t (ha.trans_le hσ.1)
  have hne : ∀σ∈Icc a b,L ↗χ ((σ:ℂ)-(t:ℂ)*Complex.I)≠0 := by
    intro σ hσ
    apply χ.LSeries_ne_zero_of_one_lt_re
    simpa using ha.trans_le hσ.1
  have hbnd : ∀σ∈Ioo a b,
      (deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)/
        L ↗χ ((σ:ℂ)-(t:ℂ)*Complex.I)).re≤K*Real.log (Y:ℝ) := by
    intro σ hσ
    exact hbound σ hσ
  have hh := mrt_log_norm_sigma_upper hab hf hne hbnd
  have hwidth : b-a≤1/Real.log (Y:ℝ) := by
    dsimp only [a,b]
    linarith [one_div_pos.mpr hLX]
  have hcost : (K*Real.log (Y:ℝ))*(b-a)≤K := by
    calc
      _ ≤ (K*Real.log (Y:ℝ))*(1/Real.log (Y:ℝ)) :=
        mul_le_mul_of_nonneg_left hwidth (mul_nonneg hK hLY.le)
      _ = K := by field_simp
  have hh' := hh.trans hcost
  simp only [a,b,Complex.ofReal_add,Complex.ofReal_one] at hh'
  linarith

end TwoPointCorrelations

end OAI
