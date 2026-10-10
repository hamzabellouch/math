import OAI.Geometry.RCD.Transport.RenyiLocalVariation

namespace OAI

/-! # Integrable tails for localized Rényi secants -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates

theorem exp_increment_bound (a b : ℝ) :
    |Real.exp b-Real.exp a|≤Real.exp (max a b)*|b-a| := by
  have hd (r : ℝ) (_ : r∈uIcc a b) :
      HasDerivWithinAt Real.exp (Real.exp r) (uIcc a b) r :=
    (Real.hasDerivAt_exp r).hasDerivWithinAt
  have hb (r : ℝ) (hr : r∈uIcc a b) : ‖Real.exp r‖≤Real.exp (max a b) := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hr.2
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_uIcc a b)
    (left_mem_uIcc : a∈uIcc a b) (right_mem_uIcc : b∈uIcc a b)
  simpa only [Real.norm_eq_abs] using hh

variable {X : Type*} [MetricSpace X]

def renyiPathMajorant (L : ℝ≥0) (q : ℝ) (g : X → ℝ) (γ : C(Time,X)) : ℝ :=
  (1-q)*(L:ℝ)*dist (γ 0) (γ 1)*
    Real.exp ((1-q)*(|g (γ 0)|+(L:ℝ)/8*dist (γ 0) (γ 1)))

theorem renyiPathMajorant_nonneg (L : ℝ≥0) {q : ℝ} (hq : q≤1)
    (g : X → ℝ) (γ : C(Time,X)) : 0≤renyiPathMajorant L q g γ := by
  unfold renyiPathMajorant
  positivity

theorem renyi_exp_path_increment {L : ℝ≥0} {g : X → ℝ} (hg : LipschitzWith L g)
    {q : ℝ} (hq : q≤1) {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (t : Time) (ht : (t:ℝ)≤1/8) :
    |Real.exp ((q-1)*g (γ t))-Real.exp ((q-1)*g (γ 0))|≤
      (t:ℝ)*renyiPathMajorant L q g γ := by
  have hc : 0≤1-q := sub_nonneg.mpr hq
  have hi := lipschitz_geodesic_increment hg hγ t
  have hd0 : 0≤dist (γ 0) (γ 1) := dist_nonneg
  have hi' : |g (γ t)-g (γ 0)|≤(L:ℝ)/8*dist (γ 0) (γ 1) := by
    exact hi.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left ht L.coe_nonneg]) hd0)
  have hg' : |g (γ t)|≤|g (γ 0)|+(L:ℝ)/8*dist (γ 0) (γ 1) := by
    have hh := abs_add_le (g (γ t)-g (γ 0)) (g (γ 0))
    simp only [sub_add_cancel] at hh
    linarith
  have hb : max ((q-1)*g (γ 0)) ((q-1)*g (γ t))≤
      (1-q)*(|g (γ 0)|+(L:ℝ)/8*dist (γ 0) (γ 1)) := by
    apply max_le
    · nlinarith [neg_le_abs (g (γ 0)),mul_nonneg L.coe_nonneg hd0]
    · nlinarith [neg_le_abs (g (γ t))]
  have he : |(q-1)*g (γ t)-(q-1)*g (γ 0)|=
      (1-q)*|g (γ t)-g (γ 0)| := by
    rw [←mul_sub,abs_mul,abs_of_nonpos (sub_nonpos.mpr hq)]
    ring
  calc
    _ ≤ Real.exp (max ((q-1)*g (γ 0)) ((q-1)*g (γ t)))*
        |(q-1)*g (γ t)-(q-1)*g (γ 0)| := exp_increment_bound _ _
    _ ≤ Real.exp ((1-q)*(|g (γ 0)|+(L:ℝ)/8*dist (γ 0) (γ 1)))*
        ((1-q)*((L:ℝ)*(t:ℝ)*dist (γ 0) (γ 1))) := by
      rw [he]
      exact mul_le_mul (Real.exp_le_exp.mpr hb) (mul_le_mul_of_nonneg_left hi hc)
        (mul_nonneg hc (abs_nonneg _)) (Real.exp_pos _).le
    _ = _ := by unfold renyiPathMajorant; ring

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem planInitialSecant_restrict_error_of_majorant (π : Measure C(Time,X))
    {f : X → ℝ} (hf : Measurable f) {H : C(Time,X) → ℝ} (hH : Integrable H π)
    {A : Set C(Time,X)} (hA : MeasurableSet A) (t : Time) (ht : 0<(t:ℝ))
    (hb : ∀ᵐ γ ∂π, |f (γ t)-f (γ 0)|≤(t:ℝ)*H γ) :
    |planInitialSecant π f t-planInitialSecant (π.restrict A) f t|≤∫γ in Aᶜ,H γ ∂π := by
  have hi : Integrable (fun γ : C(Time,X) => f (γ t)-f (γ 0)) π :=
    (hH.const_mul (t:ℝ)).mono'
      ((hf.comp (measurable_path_eval t)).sub (hf.comp (measurable_path_eval 0))).aestronglyMeasurable hb
  have hs := integral_add_compl hA hi
  simp only [planInitialSecant,geodesicExtension_eq]
  rw [←sub_div,←hs]
  have he : ((∫γ in A,f (γ t)-f (γ 0) ∂π)+
      (∫γ in Aᶜ,f (γ t)-f (γ 0) ∂π))-(∫γ in A,f (γ t)-f (γ 0) ∂π)=
      ∫γ in Aᶜ,f (γ t)-f (γ 0) ∂π := by ring
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  calc
    _ ≤ ∫γ in Aᶜ,|f (γ t)-f (γ 0)| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫γ in Aᶜ,(t:ℝ)*H γ ∂π :=
      integral_mono_ae hi.abs.integrableOn (hH.const_mul _).integrableOn (ae_restrict_of_ae hb)
    _ = _ := by rw [integral_const_mul]; ring

end RegularPointCoordinates

end

end OAI
