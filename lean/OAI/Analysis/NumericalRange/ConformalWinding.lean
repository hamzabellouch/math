import OAI.Analysis.NumericalRange.ConformalJacobian

namespace OAI

noncomputable section

namespace CompleteCrouzeix


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real
section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma circle_convex_integral_zero {K : Set ℂ} (hK : Convex ℝ K)
    {J G : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J K)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*
      J (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = 0 := by
  have hF : AnalyticOnNhd ℂ (fun z => (z-a)*J z) K := by
    intro z hz; exact (analyticAt_id.sub analyticAt_const).mul (hJ z hz)
  have he := circle_convex_cauchy hK hF hG hcurve ha hne hmass
  simpa only [sub_self, zero_mul] using
    (show (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = (a-a)*J a from by
      calc
        _ = ∫ t : UnitAddCircle,
          ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))*
            ((G (t.toCircle : ℂ)-a)*J (G (t.toCircle : ℂ)))
              ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards [] with t
          have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
            simp [Circle.norm_coe]
          field_simp [sub_ne_zero.mpr (hne _ ht)]
        _ = _ := he)

lemma logarithmic_dslope_derivative {f : ℂ → ℂ} {a z : ℂ}
    (hfa : f z ≠ f a) (hza : z ≠ a) (hf : DifferentiableAt ℂ f z) :
    deriv f z / (f z-f a) = 1/(z-a) + deriv (dslope f a) z / dslope f a z := by
  have hd : deriv (dslope f a) z =
      (deriv f z*(z-a)-(f z-f a))/(z-a)^2 := by
    rw [(dslope_eventuallyEq_slope_of_ne f hza).deriv_eq]
    rw [show slope f a = (fun w => (f w-f a)/(w-a)) from
      funext (fun w => slope_def_field f a w)]
    simpa only [Pi.div_apply, id_eq, mul_one] using
      ((hf.hasDerivAt.sub_const (f a)).fun_div
        ((hasDerivAt_id z).sub_const a) (sub_ne_zero.mpr hza)).deriv
  rw [hd, dslope_of_ne _ hza, slope_def_field]
  field_simp
  ring

theorem conformal_circle_mass {K V : Set ℂ} (hK : Convex ℝ K)
    (hV : IsOpen V) (hKV : K ⊆ V) {f G : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hfi : InjOn f V)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hfa : deriv f a ≠ 0)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (f ∘ G) (t.toCircle : ℂ) /
        (f (G (t.toCircle : ℂ))-f a) ∂AddCircle.haarAddCircle) = 1 := by
  let J : ℂ → ℂ := fun z => deriv (dslope f a) z / dslope f a z
  have hq := analyticOnNhd_dslope hV hf (hKV ha)
  have hJ : AnalyticOnNhd ℂ J K := by
    intro z hz
    exact (hq.deriv z (hKV hz)).div (hq z (hKV hz))
      (dslope_ne_zero_of_injOn hfi (hKV ha) (hKV hz) hfa)
  have hz := circle_convex_integral_zero hK hJ hG hcurve ha hne hmass
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
    simp [Circle.norm_coe]
  have htc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    by fun_prop
  have hgc : Continuous (fun t : UnitAddCircle => G (t.toCircle : ℂ)) :=
    hG.continuousOn.comp_continuous htc ht
  have hdgc : Continuous (fun t : UnitAddCircle => deriv G (t.toCircle : ℂ)) :=
    hG.deriv.continuousOn.comp_continuous htc ht
  have h₁ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).div (hgc.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hne _ (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).mul
      (hJ.continuousOn.comp_continuous hgc (fun t => hcurve (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a) +
        (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      have he : f (G (t.toCircle : ℂ)) ≠ f a :=
        fun he => hne _ (ht t) (hfi (hKV (hcurve (ht t))) (hKV ha) he)
      rw [deriv_comp _ (hf _ (hKV (hcurve (ht t)))).differentiableAt
        (hG _ (ht t)).differentiableAt]
      have heq := logarithmic_dslope_derivative he (hne _ (ht t))
        (hf _ (hKV (hcurve (ht t)))).differentiableAt
      change _ = _ + _*J _
      dsimp [J]
      linear_combination ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ))*heq
    _ = 1 := by rw [integral_add h₁ h₂, hmass, hz, add_zero]


end CompleteCrouzeix

end

end OAI
