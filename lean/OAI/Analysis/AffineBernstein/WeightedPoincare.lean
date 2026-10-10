import Mathlib
import OAI.Analysis.AffineBernstein.SegmentEnergy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section WeightedPoincare

lemma compact_integrable_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts (μ.prod ν)]
    {K : Set X} {S : Set Y} (hK : IsCompact K) (hS : IsCompact S)
    {F : X × Y → ℝ} (hF : Continuous F) :
    Integrable F ((μ.restrict K).prod (ν.restrict S)) := by
  rw [Measure.prod_restrict K S]
  exact ContinuousOn.integrableOn_compact (hK.prod hS) hF.continuousOn

lemma integral_affine_convex_le {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {E : Space n → ℝ}
    (hE : Continuous E) (hEp : ∀ x, 0 ≤ E x) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {a : Space n} (ha : a ∈ K) :
    (∫ x in K, E ((1-t) • a + t • x)) ≤
      (t^n)⁻¹ * ∫ x in K, E x := by
  let F := K.indicator E
  have hFi : Integrable F := (ContinuousOn.integrableOn_compact hK hE.continuousOn).integrable_indicator hK.measurableSet
  have hFa : Integrable (fun x => F ((1-t) • a+x)) :=
    (measurePreserving_add_left volume ((1-t) • a)).integrable_comp_of_integrable hFi
  have hFat : Integrable (fun x => F ((1-t) • a+t • x)) := hFa.comp_smul ht.ne'
  have hFp (x : Space n) : 0 ≤ F x := Set.indicator_nonneg (fun point _ => hEp point) x
  have he : (∫ x in K, E ((1-t) • a+t • x)) = ∫ x in K, F ((1-t) • a+t • x) := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    exact (Set.indicator_of_mem (hc ha hx (sub_nonneg.mpr ht1) ht.le (by ring)) E).symm
  rw [he]
  calc
    _ ≤ ∫ x, F ((1-t) • a+t • x) := setIntegral_le_integral hFat (Filter.Eventually.of_forall fun x => hFp _)
    _ = (t^n)⁻¹ * ∫ x in K, E x := by
      rw [Measure.integral_comp_smul_of_nonneg volume (fun x => F ((1-t) • a+x)) t (hR := ht.le),
        integral_add_left_eq_self F ((1-t) • a)]
      simp only [Space,finrank_euclideanSpace, Fintype.card_fin,smul_eq_mul]
      rw [integral_indicator hK.measurableSet]

lemma double_integral_segment_le {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {E : Space n → ℝ}
    (hE : Continuous E) (hEp : ∀ x, 0 ≤ E x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (∫ x in K, ∫ y in K, E ((1-t) • x+t • y)) ≤
      (volume K).toReal * (2:ℝ)^n * ∫ x in K, E x := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hEc (r : ℝ) : Continuous (fun p : Space n × Space n => E ((1-r) • p.1+r • p.2)) :=
    by fun_prop
  have hEi (r : ℝ) := compact_integrable_pair (μ := volume) (ν := volume) hK hK (hEc r)
  have hIn : 0 ≤ ∫ x in K, E x := MeasureTheory.integral_nonneg hEp
  have hlarge (r : ℝ) (hr : (1/2:ℝ) ≤ r) (hr1 : r ≤ 1) :
      (∫ x in K, ∫ y in K, E ((1-r) • x+r • y)) ≤
        (volume K).toReal * (2:ℝ)^n * ∫ x in K, E x := by
    have hrp : 0 < r := by linarith
    have hinv : (r^n)⁻¹ ≤ (2:ℝ)^n := by
      rw [← inv_pow]
      apply pow_le_pow_left₀ (inv_nonneg.mpr hrp.le)
      exact (inv_le_iff_one_le_mul₀ hrp).mpr (by linarith)
    have hi := setIntegral_mono_on (hEi r).integral_prod_left
      (integrable_const ((2:ℝ)^n * ∫ x in K, E x)) hK.measurableSet (fun x hx =>
        (integral_affine_convex_le hK hc hE hEp hrp hr1 hx).trans
          (mul_le_mul_of_nonneg_right hinv hIn))
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_assoc] using hi
  by_cases hth : (1/2:ℝ) ≤ t
  · exact hlarge t hth ht.2
  · rw [integral_integral_swap (hEi t)]
    have he : (fun y => ∫ x in K, E ((1-t) • x+t • y)) =
        (fun y => ∫ x in K, E ((1-(1-t)) • y+(1-t) • x)) := by
      funext y
      apply setIntegral_congr_fun hK.measurableSet
      intro point _
      simp only [sub_sub_cancel,add_comm]
    rw [he]
    exact hlarge (1-t) (by linarith) (by linarith [ht.1])

lemma average_segment_energy_le {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {E : Space n → ℝ}
    (hE : Continuous E) (hEp : ∀ x, 0 ≤ E x) :
    (∫ x in K, ∫ y in K, ∫ t in Icc (0:ℝ) 1, E ((1-t) • x+t • y)) ≤
      (volume K).toReal * (2:ℝ)^n * ∫ x in K, E x := by
  have hG : Continuous (fun p : Space n × ℝ => ∫ y in K, E ((1-p.2) • p.1+p.2 • y)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) hK
  have hswap1 (x : Space n) :
      (∫ y in K, ∫ t in Icc (0:ℝ) 1, E ((1-t) • x+t • y)) =
        ∫ t in Icc (0:ℝ) 1, ∫ y in K, E ((1-t) • x+t • y) := by
    apply integral_integral_swap
    exact compact_integrable_pair (μ := volume) (ν := volume) hK isCompact_Icc (by fun_prop)
  simp_rw [hswap1]
  rw [integral_integral_swap (compact_integrable_pair (μ := volume) (ν := volume) hK isCompact_Icc hG)]
  have hi := setIntegral_mono_on
    (compact_integrable_pair (μ := volume) (ν := volume) hK isCompact_Icc hG).integral_prod_right
    (integrable_const ((volume K).toReal * (2:ℝ)^n * ∫ x in K, E x)) measurableSet_Icc
    (fun t ht => double_integral_segment_le hK hc hE hEp ht)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul] using hi

/-- Weighted Poincare in a compact convex set. The constant uses only chordal
oscillation of the convex gradient, not pointwise ellipticity. -/
theorem weighted_poincare {n : ℕ} {u f : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hp : ∀ x, (hessian u x).PosDef)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) {A : ℝ} (hA : 0 ≤ A)
    (hchord : ∀ x ∈ K, ∀ y ∈ K, (fderiv ℝ u y-fderiv ℝ u x) (y-x) ≤ A) :
    (∫ x in K, ∫ y in K, (f y-f x)^2) ≤
      A*((volume K).toReal * (2:ℝ)^n * ∫ x in K, inverseHessianPair u f f x) := by
  let E := inverseHessianPair u f f
  have hE : Continuous E := (contDiff_inverseHessianPair_global hu hp hf hf).continuous
  have hEp (x : Space n) : 0 ≤ E x := inverseHessianPair_self_nonneg (hp x) f
  let F := fun p : Space n × Space n => ∫ t in Icc (0:ℝ) 1, E ((1-t) • p.1+t • p.2)
  have hF : Continuous F := continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have hFi := compact_integrable_pair (μ := volume) (ν := volume) hK hK hF
  have hdiff : Continuous (fun p : Space n × Space n => (f p.2-f p.1)^2) := by fun_prop
  have hdiffi := compact_integrable_pair (μ := volume) (ν := volume) hK hK hdiff
  have hpoint (x : Space n) (hx : x ∈ K) (y : Space n) (hy : y ∈ K) :
      (f y-f x)^2 ≤ A*F (x,y) := by
    have hh := segment_energy_bound hu hf hp x y
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))] at hh
    have he : (fun t : ℝ => E (x+t • (y-x))) = (fun t => E ((1-t) • x+t • y)) := by
      funext t
      congr 1
      module
    change (f y-f x)^2 ≤ _*(∫ t in Icc (0:ℝ) 1, E (x+t • (y-x))) at hh
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hchord x hx y hy)
      (MeasureTheory.integral_nonneg fun t => hEp _))
  have hi := setIntegral_mono_on hdiffi.integral_prod_left
    ((hFi.const_mul A).integral_prod_left) hK.measurableSet (fun x hx => by
      apply setIntegral_mono_on
        (ContinuousOn.integrableOn_compact hK (hdiff.comp (continuous_const.prodMk continuous_id)).continuousOn)
        (ContinuousOn.integrableOn_compact hK ((hF.comp (continuous_const.prodMk continuous_id)).const_mul A).continuousOn)
        hK.measurableSet
      exact hpoint x hx)
  simp_rw [integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (average_segment_energy_le hK hc hE hEp) hA)

end WeightedPoincare



end
end AffineBernstein
end

end OAI
