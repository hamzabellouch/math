import OAI.Geometry.RCD.Heat.CompactTimePairing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace OAI

/-! # Actual time derivatives of Lipschitz compact pairings

Compact spatial pairings of a Lipschitz cylinder are Lipschitz in time.
Their absolutely continuous representatives admit integration by parts.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal Interval
noncomputable section
namespace RegularPointCoordinates

theorem compact_cylinder_pairing_lipschitz
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) (U : ℝ → Y → ℝ) {T : Set ℝ} {L : ℝ≥0}
    (hU : LipschitzOnWith L (Function.uncurry U) (T ×ˢ univ))
    (φ : Y → ℝ) (hφ : Integrable φ μ) :
    LipschitzOnWith ⟨(L:ℝ)*(∫ x, |φ x| ∂μ),mul_nonneg L.coe_nonneg
      (integral_nonneg fun x => abs_nonneg (φ x))⟩
      (fun t => ∫ x, φ x*U t x ∂μ) T := by
  have hc (t : ℝ) (ht : t ∈ T) : Continuous (U t) := by
    apply continuousOn_univ.mp
    exact hU.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨ht,mem_univ x⟩)
  have hi (t : ℝ) (ht : t ∈ T) : Integrable (fun x => φ x*U t x) μ :=
    compact_weighted_integrable μ φ hφ (U t) (hc t ht)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [Real.dist_eq,← integral_sub (hi s hs) (hi t ht)]
  change |∫ x, φ x*U s x-φ x*U t x ∂μ| ≤ (L:ℝ)*(∫ x, |φ x| ∂μ)*dist s t
  calc
    _ ≤ ∫ x, |φ x*U s x-φ x*U t x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((L:ℝ)*dist s t)*|φ x| ∂μ := by
      apply integral_mono_ae ((hi s hs).sub (hi t ht)).abs (hφ.abs.const_mul _)
      exact Eventually.of_forall fun x => by
        have hb := hU.dist_le_mul (s,x) ⟨hs,mem_univ x⟩ (t,x) ⟨ht,mem_univ x⟩
        simp only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg,Function.uncurry] at hb
        have hb' : |U s x-U t x| ≤ (L:ℝ)*dist s t := by simpa only [Real.dist_eq] using hb
        change |φ x*U s x-φ x*U t x| ≤ ((L:ℝ)*dist s t)*|φ x|
        rw [← mul_sub,abs_mul,mul_comm ((L:ℝ)*dist s t)]
        exact mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

theorem compact_set_pairing_lipschitz
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {Ω : Set X} (hΩ : IsCompact Ω) (U : ℝ → X → ℝ)
    {T : Set ℝ} {L : ℝ≥0}
    (hU : LipschitzOnWith L (Function.uncurry U) (T ×ˢ Ω))
    (φ : X → ℝ) (hφ : IntegrableOn φ Ω μ) :
    LipschitzOnWith ⟨(L:ℝ)*(∫ x in Ω, |φ x| ∂μ),mul_nonneg L.coe_nonneg
      (integral_nonneg fun x => abs_nonneg (φ x))⟩
      (fun t => ∫ x in Ω, φ x*U t x ∂μ) T := by
  let : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩ
  have hU' : LipschitzOnWith L (fun q : ℝ × Ω => U q.1 q.2) (T ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro q hq q' hq'
    exact hU.dist_le_mul (q.1,q.2) ⟨hq.1,q.2.property⟩
      (q'.1,q'.2) ⟨hq'.1,q'.2.property⟩
  have hi : Integrable (fun x : Ω => φ x) (μ.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal hΩ.measurableSet).mp hφ
  have hh := compact_cylinder_pairing_lipschitz (μ.comap Subtype.val)
    (fun t (x : Ω) => U t x) hU' (fun x => φ x) hi
  have heP (t : ℝ) : (∫ x : Ω, φ x*U t x ∂μ.comap Subtype.val) =
      ∫ x in Ω, φ x*U t x ∂μ :=
    integral_subtype_comap hΩ.measurableSet (fun x => φ x*U t x)
  have heA : (∫ x : Ω, |φ x| ∂μ.comap Subtype.val) = ∫ x in Ω, |φ x| ∂μ :=
    integral_subtype_comap hΩ.measurableSet (fun x => |φ x|)
  simpa only [heP,heA] using hh

theorem lipschitz_time_pairing_integration_by_parts
    (P θ θ' : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) {L A : ℝ≥0}
    (hP : LipschitzOnWith L P (Icc a b)) (hθ : LipschitzOnWith A θ (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt θ (θ' t) t)
    (hθa : θ a = 0) (hθb : θ b = 0) :
    -(∫ t in Ioo a b, θ' t*P t) = ∫ t in Ioo a b, θ t*deriv P t := by
  have hPa := (show LipschitzOnWith L P (uIcc a b) by simpa only [uIcc_of_le hab] using hP).absolutelyContinuousOnInterval
  have hθa' := (show LipschitzOnWith A θ (uIcc a b) by simpa only [uIcc_of_le hab] using hθ).absolutelyContinuousOnInterval
  have he := hθa'.integral_mul_deriv_eq_deriv_mul hPa
  rw [hθa,hθb,zero_mul,zero_mul,sub_zero,zero_sub] at he
  simp only [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo] at he
  have he' : (∫ t in Ioo a b, deriv θ t*P t) = ∫ t in Ioo a b, θ' t*P t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change deriv θ t*P t = θ' t*P t
    rw [(hder t ht).deriv]
  rw [he'] at he
  exact he.symm

end RegularPointCoordinates

end

end OAI
