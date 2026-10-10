import OAI.Analysis.NumericalRange.PositiveDensity

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_255} {m : Type u_256} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
lemma densityField_block_bound (E : C(UnitAddCircle,Matrix n n ℂ))
    (hE : ∀ t, (E t).PosSemidef) (X Y : Matrix n m ℂ) :
    2 * ‖densityField (μ := AddCircle.haarAddCircle) E X Y‖^2 ≤
      ‖densityField (μ := AddCircle.haarAddCircle) E X X‖^2 +
      ‖densityField (μ := AddCircle.haarAddCircle) E Y Y‖^2 := by
  apply block_density_l2
  filter_upwards [densityField_ae (μ := AddCircle.haarAddCircle) E X X,
    densityField_ae (μ := AddCircle.haarAddCircle) E Y Y,
    densityField_ae (μ := AddCircle.haarAddCircle) E X Y] with t hp hq hr
  rw [hp,hq,hr,fromHS_toHS,fromHS_toHS,fromHS_toHS]
  exact weightedDensity_block_pos (hE t) X Y
lemma densityField_ordered_adjoints (Λ : C(UnitAddCircle,Matrix n n ℂ))
    (F : C(UnitAddCircle,Matrix m m ℂ)) (X Y : Matrix n m ℂ)
    (L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hL : ∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (F t * fromHS (u t)))
    (hR : ∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t) * F t))
    (hord : ∀ᵐ t ∂AddCircle.haarAddCircle,
      weightedDensity (Λ t) X X = (F t)ᴴ * weightedDensity (Λ t) X Y ∧
      weightedDensity (Λ t) X Y = F t * weightedDensity (Λ t) X X ∧
      weightedDensity (Λ t) Y Y = weightedDensity (Λ t) X Y * (F t)ᴴ) :
    densityField (μ := AddCircle.haarAddCircle) Λ X X = L.adjoint (densityField Λ X Y) ∧
    densityField (μ := AddCircle.haarAddCircle) Λ Y Y = R.adjoint (densityField Λ X Y) := by
  constructor
  · apply left_adjoint_of_ae L hL
    filter_upwards [hord,densityField_ae (μ := AddCircle.haarAddCircle) Λ X X,
      densityField_ae (μ := AddCircle.haarAddCircle) Λ X Y] with t ho hp hr
    rw [hp,hr,fromHS_toHS,ho.1]
  · apply right_adjoint_of_ae R hR
    filter_upwards [hord,densityField_ae (μ := AddCircle.haarAddCircle) Λ Y Y,
      densityField_ae (μ := AddCircle.haarAddCircle) Λ X Y] with t ho hq hr
    rw [hq,hr,fromHS_toHS,ho.2.2]
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
lemma ordered_modules {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1) :
    ∃ L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m),
      ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
      (∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (D.trace F hF t*fromHS (u t))) ∧
      (∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*D.trace F hF t)) ∧
      D.cauchy.comp (L.comp D.cauchy) = L.comp D.cauchy ∧
      D.cauchy.comp (R.comp D.cauchy) = R.comp D.cauchy :=
  actualExteriorCauchy_ordered_modules D.exterior.radius_gt D.exterior.leading_ne
    D.exterior.analytic_regular D.exterior.injective D.exterior.noncritical D.support_circle
    D.isOpen D.convex D.exterior.boundary_image D.outside_imp D.inner_maps hF
    (fun t => hn _ (D.G_boundary (by simp [Circle.norm_coe])).1)
lemma positive_ordered [Nonempty n] (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
    {X Y : Matrix n m ℂ} (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1)
    (he : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (completeAnalyticEval A F)
      (vectorize X) = vectorize Y) :
    ∀ᵐ t ∂AddCircle.haarAddCircle,
      weightedDensity (D.positiveDensity A hA t) X X = (D.trace F hF t)ᴴ * weightedDensity (D.positiveDensity A hA t) X Y ∧
      weightedDensity (D.positiveDensity A hA t) X Y = D.trace F hF t * weightedDensity (D.positiveDensity A hA t) X X ∧
      weightedDensity (D.positiveDensity A hA t) Y Y = weightedDensity (D.positiveDensity A hA t) X Y * (D.trace F hF t)ᴴ := by
  apply actual_density_ordered (D.positiveDensity A hA) (D.positiveDensity_nonneg A hA hc)
    (D.positiveDensity_mass A hA) (D.trace F hF)
    (fun t => hn _ (D.G_boundary (by simp [Circle.norm_coe])).1) hx hy
  rw [← D.positiveDensity_operator_representation A hA hF]
  exact he
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
