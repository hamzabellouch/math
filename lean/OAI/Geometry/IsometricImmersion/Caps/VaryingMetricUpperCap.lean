import OAI.Geometry.IsometricImmersion.Caps.UpperCapMetricJets

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation
  SmoothLocal.Model

theorem reflected_capInductionHeight {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} {Z c e0 : ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hh : CapInductionHeight g U Z c e0 z) :
    CapInductionHeight (reflectedMetric g) (reflectPoint ⁻¹' U) Z c e0 (reflectedScalar z) := by
  have hmem {p : Coord} (hp : p ∈ modelSquare) : reflectPoint p ∈ U :=
    hSU ((reflectPoint_mem_modelSquare p).mpr hp)
  refine ⟨reflectedScalar_contDiffOn hh.smooth, reflectedScalar_C8 hh.lowJet, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [reflectedMetric_hessian_entry hg hh.smooth hU (hmem hp)]
    simp only [ite_true]
    exact hh.denominator _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_energy hh.smooth hU (hmem hp)]
    exact hh.energy _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_quotient hg hh.smooth hU (hmem hp), abs_neg]
    exact hh.quotient _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_hessian_det hg hh.smooth hU (hmem hp),
      reflectedMetric_curvature hg hU (hmem hp), reflectedMetric_energy hh.smooth hU (hmem hp)]
    exact hh.darboux _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem varying_metric_upper_cap_chosen_family {ι : Type*}
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (hk : 0 < kappa)
    {floor : ℝ} (J : UpperCapMetricJetBudget floor) (hJ : ∀ N r, 0 ≤ J N r) :
    ∃ (B : ℕ → UpperCapRectangle floor → ℝ)
      (H : ℕ → UpperCapRectangle floor → ℝ≥0),
      (∀ n r, 0 ≤ B n r) ∧
      ∀ (g0 eta : ι → MetricField) (z : ι → Coord → ℝ) (U : ι → Set Coord),
        (∀ a, SmoothPositiveOn (g0 a) (U a)) →
        (∀ a, SmoothPositiveOn (g0 a + eta a) (U a)) →
        (∀ a, IsOpen (U a)) → (∀ a, modelSquare ⊆ U a) →
        (∀ a i j, ∀ k ≤ 8, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => (g0 a + eta a) q i j) p‖ ≤ G) →
        (∀ a, ∀ p ∈ modelSquare, d ≤ |((g0 a + eta a) p).det|) →
        (∀ a, ∀ p ∈ U a, gaussianCurvature (g0 a) p = modelCurvature kappa p) →
        (∀ a, tsupport (eta a) ⊆ patchBox) →
        (∀ a, ∀ p ∈ centralBox, gaussianCurvature (g0 a + eta a) p < -kappa/2) →
        (∀ a, ContDiffOn ℝ ∞ (z a) (U a)) →
        (∀ a, ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (z a) p‖ ≤ Z) →
        (∀ a, ∀ p ∈ modelSquare, c ≤ |covHessian (g0 a + eta a) (z a) p 1 1|) →
        (∀ a, ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0 a + eta a) (z a) p) →
        (∀ a, ∀ p ∈ modelSquare, |hessianQuotient (g0 a + eta a) (z a) p| ≤ (1 : ℝ)/100) →
        (∀ a, ∀ p ∈ modelSquare,
          (covHessian (g0 a + eta a) (z a) p).det =
            gaussianCurvature (g0 a + eta a) p*heightEnergy (g0 a + eta a) (z a) p) →
        ∃ Y : ι → ℝ → ℝ → ℝ,
          (∀ a, ContDiffOn ℝ ∞ (capChart (Y a)) capChartDomain ∧
            (∀ s ∈ Icc (-2 : ℝ) 2, Y a s 0 = s) ∧
            (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
              HasDerivWithinAt (Y a s)
                (-hessianQuotient (g0 a + eta a) (z a) (coordinatePoint t (Y a s t)))
                (Ioo (-2 : ℝ) 2) t) ∧
            (∀ p ∈ capChartDomain, |capFlowHeight (Y a) p-p 1| ≤ (1 : ℝ)/50)) ∧
          ((∀ a, LocalUpperCapMetricJets (g0 a + eta a) (Y a) J) →
            ∀ a (n : ℕ) (r : UpperCapRectangle floor),
              CoordinateBound (z a) (r.image (Y a)) n (B n r) ∧
              CoordinateL2Bound (z a) (r.image (Y a)) n (H n r)) := by
  obtain ⟨BL, _, hBL, hall⟩ := varying_metric_lower_cap_chosen_family (ι := ι)
    G Z d c e0 kappa hG hZ hd hc he0 hk (reflectedUpperBudget J)
    (fun N r => hJ N (reflectedUpperRectangle r))
  let B : ℕ → UpperCapRectangle floor → ℝ := fun n r => BL n r.lower
  let H : ℕ → UpperCapRectangle floor → ℝ≥0 := fun n r => originalC8L2Budget (B n r)
  have hB : ∀ n r, 0 ≤ B n r := fun n r => hBL n r.lower
  refine ⟨B, H, hB, ?_⟩
  intro g0 eta z U hg0 hg hU hSU hgB hdet hbackground hsupport hcentral hz hzB hyy hE hsmall hD
  have hsum (a : ι) : reflectedMetric (g0 a)+reflectedMetric (eta a) =
      reflectedMetric (g0 a+eta a) := (reflectedMetric_add (g0 a) (eta a)).symm
  have hgR (a : ι) : SmoothPositiveOn (reflectedMetric (g0 a)+reflectedMetric (eta a))
      (reflectPoint ⁻¹' U a) := by
    rw [hsum]
    exact reflectedMetric_smoothPositive (hg a)
  have hgBR : ∀ a i j, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (reflectedMetric (g0 a)+reflectedMetric (eta a)) q i j) p‖ ≤ G := by
    intro a
    rw [hsum]
    exact reflectedMetric_C8 (hgB a)
  have hdetR : ∀ a, ∀ p ∈ modelSquare,
      d ≤ |((reflectedMetric (g0 a)+reflectedMetric (eta a)) p).det| := by
    intro a p hp
    rw [hsum, reflectedMetric_det]
    exact hdet a _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcentralR : ∀ a, ∀ p ∈ centralBox,
      gaussianCurvature (reflectedMetric (g0 a)+reflectedMetric (eta a)) p < -kappa/2 := by
    intro a p hp
    have hpc : reflectPoint p ∈ centralBox := (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    have hps : reflectPoint p ∈ modelSquare := by
      constructor <;> intro i <;> linarith [hpc.1 i, hpc.2 i]
    rw [hsum, reflectedMetric_curvature (hg a) (hU a) (hSU a hps)]
    exact hcentral a _ hpc
  have hhR (a : ι) : CapInductionHeight (reflectedMetric (g0 a)+reflectedMetric (eta a))
      (reflectPoint ⁻¹' U a) Z c e0 (reflectedScalar (z a)) := by
    rw [hsum]
    exact reflected_capInductionHeight (hg a) (hU a) (hSU a)
      ⟨hz a, hzB a, hyy a, hE a, hsmall a, hD a⟩
  obtain ⟨YL, hYL, hboundsL⟩ := hall (fun a => reflectedMetric (g0 a))
    (fun a => reflectedMetric (eta a)) (fun a => reflectedScalar (z a))
    (fun a => reflectPoint ⁻¹' U a) hgR (fun a => reflectedDomain_isOpen (hU a))
    (fun a => reflectedDomain_contains_modelSquare (hSU a)) hgBR hdetR
    (fun a => reflectedMetric_model (hg0 a) (hU a) (hbackground a))
    (fun a => reflectedMetric_support_patch (hsupport a)) hcentralR
    (fun a => (hhR a).smooth) (fun a => (hhR a).lowJet) (fun a => (hhR a).denominator)
    (fun a => (hhR a).energy) (fun a => (hhR a).quotient) (fun a => (hhR a).darboux)
  let Y : ι → ℝ → ℝ → ℝ := fun a => conjugateFlow (YL a)
  have hchart (a : ι) : ContDiffOn ℝ ∞ (capChart (Y a)) capChartDomain :=
    conjugateFlow_chart_contDiffOn (hYL a).1
  have hdisp (a : ι) : ∀ p ∈ capChartDomain, |capFlowHeight (Y a) p-p 1| ≤ (1 : ℝ)/50 :=
    conjugateFlow_displacement (hYL a).2.2.2
  refine ⟨Y, ?_, ?_⟩
  · intro a
    have hmap : MapsTo (capChart (YL a)) capChartDomain (reflectPoint ⁻¹' U a) := by
      intro p hp
      apply reflectedDomain_contains_modelSquare (hSU a)
      exact modelOpenSquare_subset (capChart_mem_modelOpenSquare hp ((hYL a).2.2.2 p hp))
    have hodeR : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (YL a s)
          (-hessianQuotient (reflectedMetric (g0 a+eta a)) (reflectedScalar (z a))
            (coordinatePoint t (YL a s t))) (Icc (-2 : ℝ) 2) t := by
      simpa only [hsum] using (hYL a).2.2.1
    exact ⟨hchart a, conjugateFlow_start (hYL a).2.1,
      conjugateFlow_ode (hg a) (hz a) (hU a) hmap hodeR, hdisp a⟩
  · intro hlocal
    have hlocalR : ∀ a, LocalCapMetricJets (reflectedMetric (g0 a)+reflectedMetric (eta a))
        (YL a) (reflectedUpperBudget J) := by
      intro a
      rw [hsum]
      exact reflectedMetric_localCapJets (hlocal a)
    intro a n r
    have hrU : r.image (Y a) ⊆ U a := ((r.image_properties (hchart a) (hdisp a)).2.2).trans (hSU a)
    have hpoint : CoordinateBound (z a) (r.image (Y a)) n (B n r) :=
      r.coordinateBound_of_reflected (hz a) (hU a) hrU (hboundsL hlocalR a n r.lower).1
    exact ⟨hpoint, r.coordinateL2Bound_of_pointwise (hchart a) (hdisp a) (hB n r) hpoint⟩

end SmoothLocal.Flow.Reflection

end

end OAI
