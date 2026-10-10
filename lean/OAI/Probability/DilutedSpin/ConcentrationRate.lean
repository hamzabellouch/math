import Mathlib

namespace OAI

section
section
namespace DilutedSpinGlass
open Filter
open scoped Topology

/-- The scale prescribed by the manuscript; no enlarged moment hypothesis is
used in the bounded-model concentration step. -/
noncomputable def scoreScale (N : ℕ) : ℝ := (N:ℝ)^((3:ℝ)/4)
noncomputable def scoreMargin (N : ℕ) : ℝ := (N:ℝ)^(-(1:ℝ)/8)

lemma sqrt_scoreScale_div {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x^((3:ℝ)/4))/(x^((3:ℝ)/4)) = x^(-(3:ℝ)/8) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hx.le,← Real.rpow_sub hx]
  congr 1
  norm_num

lemma sqrt_div_scoreMargin_scale {x : ℝ} (hx : 0 < x) :
    Real.sqrt x/(x^(-(1:ℝ)/8)*x^((3:ℝ)/4)) = x^(-(1:ℝ)/8) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_add hx,← Real.rpow_sub hx]
  congr 1
  norm_num

/-- Exact normalization of the four-term concentration envelope. -/
theorem score_envelope_normalize {x K T ell w : ℝ} (hx : 0 < x) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hell : 0 < ell) (hw : 0 < w) :
    (Real.sqrt (T*x^((3:ℝ)/4))/ell+
      4*Real.sqrt (K*x)/(x^(-(1:ℝ)/8))+
      12*(x^(-(1:ℝ)/8))*(x^((3:ℝ)/4))/ell+
      Real.sqrt (x^((3:ℝ)/4)))/(w*x^((3:ℝ)/4)) =
    ((Real.sqrt T/ell+1)/w)*x^(-(3:ℝ)/8)+
      ((4*Real.sqrt K+12/ell)/w)*x^(-(1:ℝ)/8) := by
  have hs : x^((3:ℝ)/4) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hr : x^(-(1:ℝ)/8) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  rw [Real.sqrt_mul hT,Real.sqrt_mul hK]
  have h1 := sqrt_scoreScale_div hx
  have h2 := sqrt_div_scoreMargin_scale hx
  field_simp at h1 h2 ⊢
  rw [h1,h2]
  ring

/-- Monotonicity version used with the physical variance envelope. -/
theorem score_envelope_bound {x K T ell w v R : ℝ} (hx : 0 < x) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hell : 0 < ell) (hw : 0 < w) (hR : R ≤ K*x)
    (hv : v ≤ Real.sqrt (T*x^((3:ℝ)/4))/ell+
      4*Real.sqrt R/(x^(-(1:ℝ)/8))+
      12*(x^(-(1:ℝ)/8))*(x^((3:ℝ)/4))/ell+Real.sqrt (x^((3:ℝ)/4))) :
    v/(w*x^((3:ℝ)/4)) ≤
      ((Real.sqrt T/ell+1)/w)*x^(-(3:ℝ)/8)+
      ((4*Real.sqrt K+12/ell)/w)*x^(-(1:ℝ)/8) := by
  rw [← score_envelope_normalize hx hK hT hell hw]
  apply div_le_div_of_nonneg_right _ (mul_nonneg hw.le (Real.rpow_nonneg hx.le _))
  exact hv.trans (by gcongr)

lemma scoreScale_le {N : ℕ} (hN : 1 ≤ N) : scoreScale N ≤ (N:ℝ) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  simpa only [scoreScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (3:ℝ)/4 ≤ 1)

/-- The variance bound required in normalization holds for any reservoir
with interaction rate at most linear in N, and for s_N=N^(3/4). -/
lemma physical_score_variance_linear {N : ℕ} (hN : 1 ≤ N) {r C H R : ℝ}
    (hr : r ≤ R*N) :
    3*C^2*r+4*scoreScale N+2*H^2*N ≤ (3*C^2*R+4+2*H^2)*N := by
  have hh := mul_le_mul_of_nonneg_left hr (by positivity : (0:ℝ) ≤ 3*C^2)
  have hs := scoreScale_le hN
  nlinarith

/-- Both prescribed normalized score rates vanish, including the thermal
term; the constants may depend on the fixed type and depth. -/
theorem tendsto_score_rate (A B : ℝ) :
    Tendsto (fun N : ℕ => A*(N:ℝ)^(-(3:ℝ)/8)+B*(N:ℝ)^(-(1:ℝ)/8))
      atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/8)).comp tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  convert (h1.const_mul A).add (h2.const_mul B) using 1 <;> norm_num [neg_div]

end DilutedSpinGlass
end

end

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

lemma unit_limsup_nonneg {f : ℕ → ℝ} (h0 : ∀ n, 0≤f n) (h1 : ∀ n, f n≤1) :
    0≤limsup f atTop := by
  apply le_limsup_of_le (show IsBoundedUnder (·≤·) atTop f from
    isBoundedUnder_of_eventually_le (Eventually.of_forall h1))
  intro b hb
  obtain ⟨n,hn⟩ := hb.exists
  exact (h0 n).trans hn

lemma unit_limsup_le_one {f : ℕ → ℝ} (h0 : ∀ n, 0≤f n) (h1 : ∀ n, f n≤1) :
    limsup f atTop≤1 :=
  limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall h0).frequently))
    (Eventually.of_forall h1)

/-- A finite-family limsup estimate, proved by taking the size limit before
removing the positive scalar slack. No uniform size rate is used. -/
lemma limsup_finite_sqrt_bound {ι : Type*} [Fintype ι]
    (a e : ℕ → ℝ) (f : ι → ℕ → ℝ) {η b c k : ℝ}
    (hη : 0<η) (hc : 0≤c) (hk : 0≤k)
    (ha0 : ∀ n, 0≤a n) (ha1 : ∀ n, a n≤1)
    (hf1 : ∀ j n, f j n≤1) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ n, η*a n≤b+2*e n+c*Real.sqrt (k*∑ j, Real.sqrt (f j n))) :
    η*limsup a atTop≤b+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop)) := by
  classical
  have hcap (t : ℝ) (ht : 0<t) :
      η*limsup a atTop≤b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t)) := by
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    have hff : ∀ᶠ n in atTop, ∀ j, f j n<limsup (f j) atTop+t := by
      apply eventually_all.mpr
      intro j
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall (hf1 j)))
    have hab : ∀ᶠ n in atTop, a n≤
        (b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t)))/η := by
      filter_upwards [hef,hff] with n hen hfn
      apply (le_div_iff₀ hη).mpr
      rw [mul_comm]
      apply (hbound n).trans
      apply add_le_add
      · linarith
      · apply mul_le_mul_of_nonneg_left _ hc
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left _ hk
        exact Finset.sum_le_sum (fun j _ => Real.sqrt_le_sqrt (hfn j).le)
    have hl := (limsup_le_iff
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha0).frequently))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall ha1))).mpr
        (fun bound hbound => hab.mono (fun _ hle => hle.trans_lt hbound))
    simpa only [mul_comm η] using (le_div_iff₀ hη).mp hl
  have htend : Tendsto
      (fun t : ℝ => b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t)))
      (𝓝[>] 0) (𝓝 (b+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop)))) := by
    have hcont : ContinuousAt
        (fun t : ℝ => b+2*t+c*Real.sqrt (k*∑ j, Real.sqrt (limsup (f j) atTop+t))) 0 := by
      fun_prop
    simpa using hcont.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall (fun t ht => hcap t ht))

end DilutedSpinGlass

end

section
open MeasureTheory

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : _root_.MeasureTheory.Measure X) (ν : _root_.MeasureTheory.Measure Y) (ρ : _root_.MeasureTheory.Measure Z) [_root_.MeasureTheory.SFinite μ] [_root_.MeasureTheory.SFinite ν] [_root_.MeasureTheory.SFinite ρ]

lemma integrable_triple_rotate (F : (X×Y)×Z → ℝ) (hF : _root_.MeasureTheory.Integrable F ((μ.prod ν).prod ρ)) :
    _root_.MeasureTheory.Integrable (fun yz : Y×Z => ∫ x,F ((x,yz.1),yz.2) ∂μ) (ν.prod ρ) := by
  let G := F ∘ (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  have hG : _root_.MeasureTheory.Integrable G (μ.prod (ν.prod ρ)) :=
    (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc |>.integrable_comp_of_integrable hF
  exact hG.integral_prod_right

lemma integrable_triple_middle_swap (F : X×(Y×Z) → ℝ) (hF : _root_.MeasureTheory.Integrable F (μ.prod (ν.prod ρ))) :
    _root_.MeasureTheory.Integrable (fun xz : X×Z => ∫ y,F (xz.1,(y,xz.2)) ∂ν) (μ.prod ρ) := by
  have hid : _root_.MeasureTheory.MeasurePreserving (id : X → X) μ μ := ⟨measurable_id,_root_.MeasureTheory.Measure.map_id⟩
  have hG : _root_.MeasureTheory.Integrable (fun a : X×(Z×Y) => F (a.1,(a.2.2,a.2.1))) (μ.prod (ρ.prod ν)) :=
    (hid.prod (_root_.MeasureTheory.Measure.measurePreserving_swap (μ := ρ) (ν := ν))).integrable_comp_of_integrable hF
  have hH := (_root_.MeasureTheory.measurePreserving_prodAssoc μ ρ ν).integrable_comp_of_integrable hG
  exact hH.integral_prod_left

lemma integral_triple_rotate (F : (X×Y)×Z → ℝ) (hF : _root_.MeasureTheory.Integrable F ((μ.prod ν).prod ρ)) :
    (∫ a,∫ z,F (a,z) ∂ρ ∂μ.prod ν) =
      ∫ y,∫ z,∫ x,F ((x,y),z) ∂μ ∂ρ ∂ν := by
  let G := F ∘ (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  have hG : _root_.MeasureTheory.Integrable G (μ.prod (ν.prod ρ)) :=
    (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc |>.integrable_comp_of_integrable hF
  rw [← _root_.MeasureTheory.integral_prod _ hF]
  have he := (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).integral_comp' G
  change (∫ a,G (MeasurableEquiv.prodAssoc a) ∂(μ.prod ν).prod ρ)=_
  rw [he,_root_.MeasureTheory.integral_prod _ hG]
  rw [_root_.MeasureTheory.integral_integral_swap (f := fun x yz => G (x,yz)) hG]
  exact _root_.MeasureTheory.integral_prod _ hG.integral_prod_right

lemma integral_triple_middle_swap (F : X×(Y×Z) → ℝ) (hF : _root_.MeasureTheory.Integrable F (μ.prod (ν.prod ρ))) :
    (∫ x,∫ a,F (x,a) ∂ν.prod ρ ∂μ) =
      ∫ x,∫ z,∫ y,F (x,(y,z)) ∂ν ∂ρ ∂μ := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [hF.prod_right_ae] with x hx
  rw [_root_.MeasureTheory.integral_prod _ hx,_root_.MeasureTheory.integral_integral_swap hx]

end MeasureTheory

end

end OAI
