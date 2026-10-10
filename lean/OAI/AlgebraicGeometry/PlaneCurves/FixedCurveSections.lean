import OAI.AlgebraicGeometry.PlaneCurves.GeometricCollision
import OAI.AlgebraicGeometry.PlaneCurves.MarkedCubic

namespace OAI

/-!
# Necessary-section constructions for fixed smooth curves
-/

section

noncomputable section
namespace Nagata.CoefficientSpaces
open scoped BigOperators Topology
open Nagata.W20 Nagata.Workers.W12 Nagata.Workers.W10 Nagata.CoefficientSpaces
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- Genuine universal-support specialization, transported to the exact Wτ used
by the source basis and collision map, with all scalar identifications discharged. -/
theorem source_necessary_W_of_smooth_cubic_geometry {q d m : ℕ} {τ : ℝ}
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
    (hdifferential : ∀ b, polynomialGradient (Nagata.W27.directChartHom (chart b) C)
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
  have hW := universalSupport_necessary_W_smooth_local hUniversal ht ht0
    (tauPower_ne_zero hτ (((∑ i, marks i) + a) / 3))
    (fun i => ((τ ^ marks i : ℝ) : ℂ)) hm hdisjoint
    (tauPower τ x0) (tauPower_ne_zero hτ x0) ξ hp C hC X hrelations chart hc hbase hdifferential
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

end Nagata.CoefficientSpaces

end
end

section

/-! The supplied Proposition necessary-W, on the exact caller-supplied fixed
marked exponents and source multiplier. No cubic, frame, section, gradient,
normal-polynomial or quotient-existence assumption remains. -/
noncomputable section
namespace Nagata.CoefficientSpaces
open scoped BigOperators Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.W20
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- For every fixed period, all distinct nearby moving configurations have an
actual nonzero section with the required multiplicities, with the source's
fixed marks and eta=(sum marks+a)/3 retained literally. -/
theorem source_fixed_necessary_W {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (hmarks : Function.Injective marks)
    (hmbounds : ∀ i, 0 < marks i ∧ marks i < 1 / 2)
    (a : ℝ) (d m q : ℕ)
    (hUniversal : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m)) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ ξ : Fin q → ℂ, Function.Injective ξ → (∀ i, ξ i ∈ U) →
        ∃ F : genuineSourceSections hτ hτone marks a (d : ℤ) m, F ≠ 0 ∧
          ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
            (fun x : ℂ × ℂ => localScalar F (tauPower τ (1 / 2)) x.1 x.2) (ξ i, 0) m := by
  obtain ⟨C, _hprime, hC, X, hrelations, hcharts⟩ :=
    Nagata.W06.TorusConfiguration.exists_actual_source_smooth_geometry hτ hτone marks a
  obtain ⟨R, hR, hcfg⟩ := Nagata.W06.TorusConfiguration.exists_disk_for_fixed_period
    hτ hτone marks hmarks hmbounds
  refine ⟨Metric.ball 0 R, Metric.isOpen_ball, Metric.mem_ball_self hR, ?_⟩
  intro ξ hξ hξU
  have hnorm : ∀ i, ‖ξ i‖ < R := by
    intro i
    simpa only [Metric.mem_ball, dist_zero_right] using hξU i
  obtain ⟨hinj,hPi⟩ := hcfg q ξ hξ hnorm
  obtain ⟨chart,hc,hbase,hdifferential⟩ := hcharts q ξ hinj
  apply source_necessary_W_of_smooth_cubic_geometry hτ hτone hUniversal marks a (1 / 2)
    (source_marked_orbits_disjoint hτ hτone marks hmarks hmbounds) ξ ?_
    C hC X hrelations chart hc hbase hdifferential
  intro i
  rw [source_markedPi_cover_eq]
  exact hPi i

end Nagata.CoefficientSpaces

end
end

section

/-! Exact scaled/reindexed construction interface for the full target assembly.
Every original fixed marked exponent and source a is preserved. Neither a basis
nor any geometric existence premise appears. -/
noncomputable section
namespace Nagata.CoefficientSpaces
open Filter Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W28

/-- Scaling the actual universal plane equations gives the source construction
for the same fixed marks at every period, hence on the required punctured limit. -/
theorem source_fixed_scaled_construction {r d m : ℕ} (hr : 9 ≤ r)
    (hUniversal : Nagata.W13.UniversalSupport r d (fun _ => m))
    (n : ℕ) (marks : Fin 9 → ℝ) (hmarks : Function.Injective marks)
    (hmbounds : ∀ i, 0 < marks i ∧ marks i < 1 / 2) (a : ℝ) :
    ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
      ∃ (hτ : 0 < τ) (hτone : τ < 1) (U : Set ℂ),
        IsOpen U ∧ (0 : ℂ) ∈ U ∧
        ∀ ξ : Fin (r - 9) → ℂ, Function.Injective ξ → (∀ i, ξ i ∈ U) →
          ∃ F : genuineSourceSections hτ hτone marks a ((n * d : ℕ) : ℤ) (n * m),
            F ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
              (fun x : ℂ × ℂ => localScalar F (tauPower τ (1 / 2)) x.1 x.2)
              (ξ i, 0) (n * m) := by
  have hrEq : r = 9 + (r - 9) := by omega
  have hscaled : Nagata.W13.UniversalSupport (9 + (r - 9)) (n * d) (fun _ => n * m) := by
    have hu : Nagata.W13.UniversalSupport r (n * d) (fun _ => n * m) := by
      simpa only [Nat.mul_comm] using Nagata.W13.universalSupport_pow hUniversal n
    exact Eq.mp (congrArg (fun R : ℕ =>
      Nagata.W13.UniversalSupport R (n * d) (fun _ => n * m)) hrEq) hu
  have hone : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ < 1 :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hone] with τ hτ hτone
  obtain ⟨U,hU,h0,hEvery⟩ := source_fixed_necessary_W hτ hτone marks hmarks hmbounds
    a (n * d) (n * m) (r - 9) hscaled
  exact ⟨hτ,hτone,U,hU,h0,hEvery⟩

end Nagata.CoefficientSpaces

end
end

end OAI
