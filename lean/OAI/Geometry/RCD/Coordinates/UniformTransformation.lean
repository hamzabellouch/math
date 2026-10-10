import OAI.Geometry.RCD.Coordinates.FirstFailingSequence

namespace OAI

/-! # Uniform transformation from the first-failure contradiction -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.uniform_transformation_of_measured {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) [(hausdorff (m+1) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (hMeasured : LocalMeasuredCoordinateInput hX) (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -δ ≤ K*R^2 → a*(3*R) ≤ 1 →
      ∀ (u : Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic) (v : X → Euclidean (m+1)),
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic p (2*R) δ u v →
      (∀ t : ℝ, 0 < t → t ≤ R →
        ∃ f : X → Euclidean (m+1), IsPointedApproximation p 0 t 1 δ f) →
      ∀ t : ℝ, 0 < t → t ≤ R → ∃ A : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1),
        FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic p t β
          (transformedColumn (hausdorff (m+1) X) hX.quadratic u A)
          (fun x => (A : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u) (ball p t) measurableSet_ball A := by
  classical
  let C := ((m+1 : ℕ) : ℝ)^2*normalizationVolumeRatio m
  have hC : 0 ≤ C := by
    dsimp only [C,normalizationVolumeRatio]
    positivity
  let κ := 1/(4*(C+1))
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκid : 4*(C+1)*κ=1 := by dsimp only [κ]; field_simp
  have hκ1 : κ ≤ 1 := by nlinarith [mul_nonneg hC hκ.le]
  have hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2 := by
    calc
      _ = C*κ := by dsimp only [C]; ring
      _ ≤ 1/2 := by nlinarith [mul_nonneg hC hκ.le]
  obtain ⟨γ₀,hγ₀,hno⟩ := hX.no_first_failing_sequence m hm ha hBG hMeasured hκ hκ1 hsmall
  obtain ⟨η,hη,_,hfail⟩ := hX.first_failing_dyadic_scale hm β hβ
  let γ := min γ₀ η
  have hγ : 0 < γ := lt_min hγ₀ hη
  let c := min γ (1/4)
  have hc : 0 < c := lt_min hγ (by norm_num)
  by_contra hnot
  push Not at hnot
  let ε := fun k : ℕ => min c (1/((k : ℝ)+1))
  have hεpos (k : ℕ) : 0 < ε k := lt_min hc (by positivity)
  have hεγ (k : ℕ) : ε k ≤ γ := (min_le_left _ _).trans (min_le_left _ _)
  have hεquarter (k : ℕ) : ε k ≤ 1/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hεlim : Tendsto ε atTop (𝓝 0) := squeeze_zero (fun k => (hεpos k).le)
    (fun _ => min_le_right _ _) tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (k : ℕ) := hnot (ε k) (hεpos k)
  choose p R hR hK hscale u v hfirst hflat t ht htR hbad using hex
  have hK2 (k : ℕ) : -1 ≤ K*(2*R k)^2 := by
    nlinarith [hK k,hεquarter k]
  have hγfirst (k : ℕ) : FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic
      (p k) (2*R k) γ (u k) (v k) :=
    (hfirst k).mono_error _ _ (hεpos k).le (hεγ k)
  have hdfail (k : ℕ) := hfail γ hγ.le (min_le_right _ _) (p k) (R k) (hR k) (hK2 k)
    (u k) (v k) (hγfirst k) ⟨t k,ht k,htR k,by
      rintro ⟨A,hA,hAn⟩
      exact hbad k A hA hAn⟩
  choose d hd hbefore using hdfail
  have hdlim := hX.failing_depth_tends_to_infinity hm γ hγ p R ε u v d hR hK2
    (fun k => (hεpos k).le) hεlim hfirst hd
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hdlim.eventually (eventually_ge_atTop 2))
  let α := fun k : ℕ => k+N
  have hα : Tendsto α atTop atTop := tendsto_add_atTop_nat N
  apply hno γ hγ (min_le_left _ _) (p∘α) (R∘α) (ε∘α) (d∘α)
    (fun k => hR (α k)) (fun k => hN (α k) (Nat.le_add_left N k)) (hdlim.comp hα)
    (fun k => hK2 (α k)) _ (fun k => hscale (α k)) (hεlim.comp hα)
    (fun k => hflat (α k)) (u∘α) (v∘α) (fun k => hfirst (α k))
    (fun k => hbefore (α k)) (fun k => hd (α k))
  intro δ hδ
  filter_upwards [(hεlim.comp hα).eventually (eventually_lt_nhds hδ)] with k hk
  have hh := hK (α k)
  change ε (α k) < δ at hk
  change -δ ≤ K*(R (α k))^2
  linarith

end RegularPointCoordinates

end

end OAI
