import Mathlib
import OAI.Geometry.CAT0Fillings.Geometry.Comparison
import OAI.Geometry.CAT0Fillings.Tangent.CurrentDensity

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
lemma moment_lt_two (μ : Measure X) (U : X → ℝ) (hU : Measurable U)
    (hU0 : ∀ x, 0 ≤ U x) (n : ℕ) {β : ℝ} (y : X)
    (hi : Integrable (fun x => U x^(2*(n:ℝ)*β)) μ)
    (hW : 0 < ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β)))
    (hWs : ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β)) < sphereArea n)
    (ht : HasTangentBound μ U n β y)
    (hd : ∀ a : ℝ, 0 ≤ a →
      ChordTransform.transform (ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β))) n
        (fun x => (U y^β*dist y x*U x^β)^2) a ≤
      (1+2*(∫ x, (U y^β*dist y x*U x^β)^2
        ∂ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β)))*a)^(-(n:ℝ)/2)) :
    (∫ x, (U y^β*dist y x*U x^β)^2
      ∂ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β))) < 2 := by
  by_contra hh
  have hm : 2 ≤ ∫ x, (U y^β*dist y x*U x^β)^2
      ∂ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β)) := le_of_not_gt hh
  let ε (j : ℕ) : ℝ := ((j:ℝ)+1)⁻¹
  have he : ∀ j, 0 < ε j := fun j => inv_pos.mpr (by positivity)
  have he0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let W := ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β))
  have hb := ht ε he he0
    (fun j => ENNReal.ofReal ((ε j^n)⁻¹*W*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2)))
    (ENNReal.ofReal (W/(2:ℝ)^n)) (fun j => ?_)
    (rescaled_spherical_limit n he he0 W)
  · have hreal : sphereArea n/(2:ℝ)^n ≤ W/(2:ℝ)^n :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
    exact (not_le_of_gt hWs) ((div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<2^n)).mp hreal)
  · rw [rescaled_transform_identity μ U hU hU0 n β (U y^β) (ε j) y hi hW,
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ (ε j^n)⁻¹)]
    apply ENNReal.ofReal_le_ofReal
    conv_rhs => rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (he j).le n))
    apply mul_le_mul_of_nonneg_left _ hW.le
    refine (hd _ (by positivity)).trans ?_
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · have ha : 0 ≤ (ε j^2)⁻¹ := by positivity
      nlinarith
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num)
end CAT0Fillings.TangentDensity
end

section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def squaredPotential (μ : Measure X) (y : X) : ℝ := ∫ x, dist y x ^ 2 ∂μ

lemma integrable_dist_sq {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) [IsFiniteMeasure μ] (y : X) :
    Integrable (fun x => dist y x ^ 2) μ :=
  (by fun_prop : Continuous (fun x => dist y x ^ 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma continuous_squaredPotential {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (squaredPotential μ) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := μ) (by fun_prop : Continuous (Function.uncurry (fun y x : X => dist y x ^ 2)))
    (isCompact_univ : IsCompact (univ : Set X))
  change Continuous (fun y => ∫ x, dist y x ^ 2 ∂μ)
  simpa only [Measure.restrict_univ] using h

theorem exists_barycenter_variance (hX : IsCAT0 X) (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ o : X, ∀ y : X,
      squaredPotential μ o + μ.real univ * dist o y ^ 2 ≤ squaredPotential μ y := by
  obtain ⟨o,_,ho⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set X).Nonempty)
    (continuous_squaredPotential μ).continuousOn
  obtain ⟨seg,_,hs⟩ := hX.exists_squared_distance_convex
  refine ⟨o,fun y => ?_⟩
  have hbound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
      squaredPotential μ o + (1-t)*μ.real univ*dist o y^2 ≤ squaredPotential μ y := by
    have hI : Integrable (fun x => (1-t)*dist o x^2+t*dist y x^2) μ :=
      ((integrable_dist_sq μ o).const_mul (1-t)).add ((integrable_dist_sq μ y).const_mul t)
    have hh := integral_mono (integrable_dist_sq μ (seg o y t))
      (((integrable_dist_sq μ o).const_mul (1-t)).add ((integrable_dist_sq μ y).const_mul t) |>.sub (integrable_const _))
      (fun x => hs o y x t ⟨ht.le,ht1⟩)
    simp only [Pi.sub_apply,Pi.add_apply] at hh
    rw [integral_sub hI
      (integrable_const _),integral_add ((integrable_dist_sq μ o).const_mul (1-t))
      ((integrable_dist_sq μ y).const_mul t),integral_const_mul,integral_const_mul,integral_const,smul_eq_mul] at hh
    have hmin := ho (mem_univ (seg o y t))
    change squaredPotential μ o ≤ squaredPotential μ (seg o y t) at hmin
    change squaredPotential μ (seg o y t) ≤ (1-t)*squaredPotential μ o+t*squaredPotential μ y-
      μ.real univ*(t*(1-t)*dist o y^2) at hh
    have hm : t*(squaredPotential μ o+(1-t)*μ.real univ*dist o y^2-squaredPotential μ y) ≤ 0 := by
      nlinarith [hmin.trans hh]
    nlinarith
  have hlim : Tendsto (fun t : ℝ => squaredPotential μ o+(1-t)*μ.real univ*dist o y^2)
      (𝓝[>] (0:ℝ)) (𝓝 (squaredPotential μ o+μ.real univ*dist o y^2)) := by
    have h : Continuous (fun t : ℝ => squaredPotential μ o+(1-t)*μ.real univ*dist o y^2) := by fun_prop
    simpa only [sub_zero,one_mul] using (h.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
  exact hbound ht ht1.le

theorem double_distance_lower_bound (hX : IsCAT0 X) (μ : Measure X) [IsFiniteMeasure μ]
    {W : ℝ} (hall : ∀ y, W^2 ≤ μ.real univ * squaredPotential μ y) :
    2*W^2 ≤ ∫ y, squaredPotential μ y ∂μ := by
  obtain ⟨o,ho⟩ := exists_barycenter_variance hX μ
  have hi : Integrable (squaredPotential μ) μ := (continuous_squaredPotential μ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h := integral_mono ((integrable_const _).add ((integrable_dist_sq μ o).const_mul (μ.real univ))) hi ho
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((integrable_dist_sq μ o).const_mul (μ.real univ)),
    integral_const,smul_eq_mul,integral_const_mul] at h
  change μ.real univ*squaredPotential μ o+μ.real univ*squaredPotential μ o ≤ _ at h
  linarith [hall o]
end CAT0Fillings
end

end OAI
