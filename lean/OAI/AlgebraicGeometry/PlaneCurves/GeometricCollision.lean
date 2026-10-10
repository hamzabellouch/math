import OAI.AlgebraicGeometry.PlaneCurves.BasisNoncancellation
import OAI.AlgebraicGeometry.PlaneCurves.MarkedDisplacements
import OAI.AlgebraicGeometry.PlaneCurves.UniversalSections

namespace OAI

/-!
# Collision for geometric section families and necessary sections
-/

section

/-!
## Source collision on the actual Wτ
-/

noncomputable section
namespace Nagata.W20
open scoped BigOperators Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.FiniteExponents
open Nagata.CoefficientSpaces Nagata.W22

/-- The manuscript collision conclusion for the literal source section space
and actual jet map. Finite basis and all analytic coefficient premises have been
discharged. Only the universal necessary-W geometric input remains. -/
theorem source_collision_of_every_configuration
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a delta x0 : ℝ) (d : ℤ) (m q : ℕ)
    (hs : (∑ i, marks i) = 9 * x0 - delta)
    (hd : 3 * (m : ℤ) < d)
    (hfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
      firstLower d (m : ℤ) j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
    (hsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
      secondLower d j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hEvery : ∀ p : Fin q → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
      ∃ F : genuineSourceSections hτ hτone marks a d m, F ≠ 0 ∧
        ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
          (fun x : ℂ × ℂ => localScalar F (tauPower τ x0) x.1 x.2) (p i, 0) m) :
    ∃ F₀ : genuineSourceSections hτ hτone marks a d m,
      F₀ ≠ 0 ∧ genuineSourceJetMap hτ hτone marks a x0 d m q F₀ = 0 := by
  exact actual_kernel_of_every_configuration
    (fun z hz => (rayMarkedSection_analyticOnNhd hτ hτone marks z hz).differentiableAt)
    (tauPower_ne_zero hτ x0)
    (genuineSourceBasis hτ hτone marks a delta x0 d m hs hd hfirst hsecond)
    hU h0 hEvery

/-- The actual source jet rows are the manuscript's mixed derivatives in one
fixed covering frame. Row first coordinate is b, second is ell. -/
theorem genuineSourceJetMap_eq_mixed_derivative
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a x0 : ℝ) (d : ℤ) (m q : ℕ)
    (F : genuineSourceSections hτ hτone marks a d m)
    (row : Nagata.Workers.W30.JetIndex q m) :
    genuineSourceJetMap hτ hτone marks a x0 d m q F row =
      iteratedDeriv row.2.val
        (fun x => iteratedDeriv row.1.val
          (fun y => localScalar F (tauPower τ x0) x y) 0) 0 := by
  exact actualJetMap_apply_eq_mixed_derivative _ _ F row

end Nagata.W20

end
end

section

noncomputable section
namespace Nagata.W20
open scoped BigOperators Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.CoefficientSpaces
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- Genuine universal-support specialization, transported to the exact Wτ used
by the source basis and collision map, with all scalar identifications discharged. -/
theorem source_necessary_W_of_cubic_geometry {q d m : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1)
    (hUniversal : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m))
    (marks : Fin 9 → ℝ) (a x0 : ℝ)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ,
      ((τ ^ marks i : ℝ) : ℂ) ≠ ((τ ^ marks j : ℝ) : ℂ) * (τ : ℂ) ^ k))
    (ξ : Fin q → ℂ)
    (hpP : ∀ i, (Nagata.W22.rayMarkedSection hτ hτone marks).val
      (tauPower τ x0 * Complex.exp (ξ i)) ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections (τ : ℂ) 3
      (tauPower τ (((∑ i, marks i) + a) / 3)))
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val
      (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
        (logarithmicPoints (tauPower τ x0) ξ) b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
        (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
          (logarithmicPoints (tauPower τ x0) ξ) b)))))
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (chart b) C))
      (normalizedCurvePoint (fun i => (X i).val) (chart b)
        (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
          (logarithmicPoints (tauPower τ x0) ξ) b)) ≠ 0) :
    ∃ F : genuineSourceSections hτ hτone marks a (d : ℤ) m, F ≠ 0 ∧
      ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun x : ℂ × ℂ => localScalar F (tauPower τ x0) x.1 x.2) (ξ i, 0) m := by
  have ht : ‖(τ : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
  have ht0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have hm : ∀ i, ((τ ^ marks i : ℝ) : ℂ) ≠ 0 :=
    fun i => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ (marks i)).ne'
  have heq := nineThetaSection_ray_eq hτ hτone ht ht0 marks hm
  have hp : ∀ i, (nineThetaSection ht ht0 (fun i => ((τ ^ marks i : ℝ) : ℂ)) hm).val
      ((logarithmicPoints (tauPower τ x0) ξ) i).1 ≠ 0 := by
    simpa only [heq, logarithmicPoints] using hpP
  have hW := universalSupport_necessary_W_local hUniversal ht ht0
    (tauPower_ne_zero hτ (((∑ i, marks i) + a) / 3))
    (fun i => ((τ ^ marks i : ℝ) : ℂ)) hm hdisjoint
    (tauPower τ x0) (tauPower_ne_zero hτ x0) ξ hp C hC X hrelations chart hc hbase hpartial
  change ∃ F : ActualSection (τ : ℂ)
    (tauPower τ (((∑ i, marks i) + a) / 3)) (∏ i, -((τ ^ marks i : ℝ) : ℂ))
    (d : ℤ) m (Nagata.W22.rayMarkedSection hτ hτone marks).val, F ≠ 0 ∧
    ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => localScalar F (tauPower τ x0) x.1 x.2) (ξ i, 0) m at hW
  exact Eq.mp (congrArg (fun γ : ℂ =>
    ∃ F : ActualSection (τ : ℂ) (tauPower τ (((∑ i, marks i) + a) / 3)) γ
      (d : ℤ) m (Nagata.W22.rayMarkedSection hτ hτone marks).val, F ≠ 0 ∧
      ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun x : ℂ × ℂ => localScalar F (tauPower τ x0) x.1 x.2) (ξ i, 0) m)
    (rayMarkedMultiplier hτ marks)) hW

end Nagata.W20

end
end

section

/-! Exact fixed-τ source collision from universal support and concrete cubic
chart geometry. The common marked-point disk and Pi nonvanishing are supplied
by the proved fixed-period configuration construction, not by caller assumptions. -/
noncomputable section
namespace Nagata.W20
open scoped BigOperators Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.CoefficientSpaces
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry
open Nagata.FiniteExponents

/-- Equality of the actual source marked section with the actual marked product
on the common exponential chart. -/
theorem source_markedPi_cover_eq {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (x0 : ℝ) (x : ℂ) :
    (Nagata.W22.rayMarkedSection hτ hτone marks).val
      (tauPower τ x0 * Complex.exp x) =
    Nagata.W06.TorusConfiguration.markedPi τ marks
      (Nagata.Workers.W05.chartPoint τ x0 x : ℂ) := by
  have hz : tauPower τ x0 * Complex.exp x ≠ 0 :=
    mul_ne_zero (tauPower_ne_zero hτ x0) (Complex.exp_ne_zero x)
  unfold Nagata.W22.rayMarkedSection
  rw [Nagata.W08.markedThetaSection_apply _ _ _ _ hz]
  unfold Nagata.W06.TorusConfiguration.markedPi
  simp only [Nagata.Workers.W05.chartPoint_eq_real_rpow hτ,
    Nagata.Workers.W05.rayPoint_eq_real_rpow hτ, tauPower]

/-- The actual marked ray lifts occupy pairwise disjoint period orbits. -/
theorem source_marked_orbits_disjoint {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (hinj : Function.Injective marks)
    (hb : ∀ i, 0 < marks i ∧ marks i < 1 / 2) :
    Pairwise (fun i j => ∀ k : ℤ,
      ((τ ^ marks i : ℝ) : ℂ) ≠ ((τ ^ marks j : ℝ) : ℂ) * (τ : ℂ) ^ k) := by
  intro i j hij k he
  apply hij
  apply hinj
  have heq : Nagata.W21.torusPointMk (Nagata.Workers.W05.positivePeriod τ hτ)
      (Nagata.Workers.W05.rayPoint τ (marks j)) =
      Nagata.W21.torusPointMk (Nagata.Workers.W05.positivePeriod τ hτ)
        (Nagata.Workers.W05.rayPoint τ (marks i)) := by
    apply Quotient.sound
    apply (Nagata.W21.torusOrbitSetoid_iff_coe _ _ _).mpr
    refine ⟨k, ?_⟩
    simpa only [Nagata.Workers.W05.rayPoint_eq_real_rpow hτ,
      Nagata.Workers.W05.positivePeriod, Units.val_mk0, mul_comm] using he
  have hj : marks j ∈ Set.Ioo (0 : ℝ) 1 := ⟨(hb j).1, by linarith [(hb j).2]⟩
  have hi : marks i ∈ Set.Ioo (0 : ℝ) 1 := ⟨(hb i).1, by linarith [(hb i).2]⟩
  exact (Nagata.W06.TorusConfiguration.rayTorusPoint_injective_on_unit_interval
    hτ hτone hj hi heq).symm

/-- Fixed-period source collision from genuine universal support and concrete
cubic chart geometry. No finite basis, analytic section, Pi-nonvanishing, local
multiplicity, or moving-sequence hypothesis remains. -/
theorem source_collision_of_universalSupport_and_cubic_geometry
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (hmarks : Function.Injective marks)
    (hmbounds : ∀ i, 0 < marks i ∧ marks i < 1 / 2)
    (a delta : ℝ) (d m q : ℕ)
    (hs : (∑ i, marks i) = 9 * (1 / 2 : ℝ) - delta)
    (hd : 3 * (m : ℤ) < (d : ℤ))
    (hfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
      firstLower (d : ℤ) (m : ℤ) j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
    (hsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ (d : ℤ) / 3 → 0 < (d : ℤ) - 3 * j →
      secondLower (d : ℤ) j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
    (hUniversal : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m))
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections (τ : ℂ) 3
      (tauPower τ (((∑ i, marks i) + a) / 3)))
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (hcharts : ∀ ξ : Fin q → ℂ,
      Function.Injective (Nagata.W06.TorusConfiguration.torusTuple τ hτ (1 / 2) marks ξ) →
      ∃ chart : Fin (9 + q) → Fin 3,
        (∀ b, (X (chart b)).val
          (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
            (logarithmicPoints (tauPower τ (1 / 2)) ξ) b) ≠ 0) ∧
        Function.Injective (fun b => chartPoint₂ (chart b)
          (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
            (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
              (logarithmicPoints (tauPower τ (1 / 2)) ξ) b)))) ∧
        (∀ b, planePolynomialEval
          (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (chart b) C))
          (normalizedCurvePoint (fun i => (X i).val) (chart b)
            (markedNormalBase (fun i => ((τ ^ marks i : ℝ) : ℂ))
              (logarithmicPoints (tauPower τ (1 / 2)) ξ) b)) ≠ 0)) :
    ∃ F₀ : genuineSourceSections hτ hτone marks a (d : ℤ) m,
      F₀ ≠ 0 ∧ genuineSourceJetMap hτ hτone marks a (1 / 2) (d : ℤ) m q F₀ = 0 := by
  obtain ⟨R, hR, hcfg⟩ := Nagata.W06.TorusConfiguration.exists_disk_for_fixed_period
    hτ hτone marks hmarks hmbounds
  apply source_collision_of_every_configuration hτ hτone marks a delta (1 / 2)
    (d : ℤ) m q hs hd hfirst hsecond Metric.isOpen_ball (Metric.mem_ball_self hR)
  intro ξ hξ hξU
  have hnorm : ∀ i, ‖ξ i‖ < R := by
    intro i
    simpa only [Metric.mem_ball, dist_zero_right] using hξU i
  obtain ⟨hinj, hPi⟩ := hcfg q ξ hξ hnorm
  obtain ⟨chart, hc, hbase, hpartial⟩ := hcharts ξ hinj
  apply source_necessary_W_of_cubic_geometry hτ hτone hUniversal marks a (1 / 2)
    (source_marked_orbits_disjoint hτ hτone marks hmarks hmbounds) ξ ?_
    C hC X hrelations chart hc hbase hpartial
  intro i
  rw [source_markedPi_cover_eq]
  exact hPi i

end Nagata.W20

end
end

end OAI
