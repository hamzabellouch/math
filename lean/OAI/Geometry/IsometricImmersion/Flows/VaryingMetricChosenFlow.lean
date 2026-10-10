import OAI.Geometry.IsometricImmersion.Caps.VaryingMetricLowerCap

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

theorem varying_metric_lower_cap_chosen_family {ι : Type*}
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (hk : 0 < kappa)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) (hJ : ∀ N r, 0 ≤ J N r) :
    ∃ (B : ℕ → LowerCapRectangle bStar → ℝ)
      (H : ℕ → LowerCapRectangle bStar → ℝ≥0),
      (∀ n r, 0 ≤ B n r) ∧
      ∀ (g0 eta : ι → MetricField) (z : ι → Coord → ℝ) (U : ι → Set Coord),
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
          (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
            HasDerivWithinAt (Y a s)
              (-hessianQuotient (g0 a + eta a) (z a) (coordinatePoint t (Y a s t)))
              (Icc (-2 : ℝ) 2) t) ∧
          (∀ p ∈ capChartDomain, |capFlowHeight (Y a) p-p 1| ≤ (1 : ℝ)/50)) ∧
          ((∀ a, LocalCapMetricJets (g0 a + eta a) (Y a) J) →
            ∀ a (n : ℕ) (r : LowerCapRectangle bStar),
              CoordinateBound (z a) (r.image (Y a)) n (B n r) ∧
              CoordinateL2Bound (z a) (r.image (Y a)) n (H n r)) := by
  classical
  have hpoint : ∀ n : ℕ, ∀ r : LowerCapRectangle bStar, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        LocalCapMetricJets g Y J → CoordinateBound z (r.image Y) n B :=
    fun n r => uniform_varying_lowerCap_pointwise G Z d c e0 kappa hG hZ hd hc J hJ n r
  choose B hB hBest using hpoint
  have hnorm : ∀ n : ℕ, ∀ r : LowerCapRectangle bStar, ∃ H : ℝ≥0,
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        LocalCapMetricJets g Y J → CoordinateL2Bound z (r.image Y) (n+8) H :=
    fun n r => uniform_varying_lowerCap_L2 G Z d c e0 kappa hG hZ hd hc J hJ n r
  choose H hHest using hnorm
  refine ⟨B, H, hB, ?_⟩
  intro g0 eta z U hg hU hSU hgB hdet hbackground hsupport hcentral hz hzB hyy hE hsmall hD
  have hh (a : ι) : CapInductionHeight (g0 a + eta a) (U a) Z c e0 (z a) :=
    ⟨hz a, hzB a, hyy a, hE a, hsmall a, hD a⟩
  have hflow : ∀ a : ι, ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ),
      CapInductionFlow (g0 a + eta a) (U a) G Z d c e0 kappa (z a) Y W :=
    fun a => exists_capInductionFlow (hg a) (hU a) (hSU a) hG hZ hd hc he0
      (hgB a) (hdet a) (hh a) hk (hbackground a) (hsupport a) (hcentral a)
  choose W Y hf using hflow
  refine ⟨Y, ?_, ?_⟩
  · intro a
    exact ⟨capChart_contDiffOn (hf a).jointSmooth, (hf a).start, (hf a).ode, (hf a).displacement⟩
  · intro hlocal a n r
    have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => (g0 a + eta a) q i j) p‖ ≤ G :=
      fun row column order horder point hpoint =>
        hgB a row column order (horder.trans (by norm_num)) point hpoint
    exact ⟨hBest n r (g0 a + eta a) (U a) (z a) (Y a) (W a)
        (hg a) (hU a) (hSU a) hg4 (hdet a) (hh a) (hf a) (hlocal a),
      (hHest n r (g0 a + eta a) (U a) (z a) (Y a) (W a)
        (hg a) (hU a) (hSU a) hg4 (hdet a) (hh a) (hf a) (hlocal a)).mono
          (Nat.le_add_right n 8) le_rfl⟩

end SmoothLocal.Flow

end

end OAI
