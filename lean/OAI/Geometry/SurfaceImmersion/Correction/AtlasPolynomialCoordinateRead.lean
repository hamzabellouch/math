import OAI.Geometry.SurfaceImmersion.Atlas.LocalizedCoordinatePullback
import OAI.Geometry.SurfaceImmersion.Atlas.CompactCoordinatePullback
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetCoordinateRelation

namespace OAI

/-! A polynomial in one localized atlas map has an actual finite jet
expression in another chart, on the nonzero partition-weight locus. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_polynomial_coordinate_read (i j : A.centers) {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {K : Set Base} (hK : IsCompact K)
    (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
        ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
          ∀ (x : Base), x ∈ U → A.weight i ((chart (i : M)).symm x) ≠ 0 →
            ∀ ε t : ℝ,
              coordinatePolynomialValue P' ε (A.jetChartMap i F) t (JetPolynomial.planeCoordinateIsometry x) =
                coordinatePolynomialValue P ε (A.jetChartMap j F) t
                  (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x)) := by
  let e := transition (i : M) (j : M)
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    have hs : e.symm = transition (j : M) (i : M) := by
      simp [e,transition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rw [hs]
    exact transition_smooth (j : M) (i : M)
  obtain ⟨U₁,hU₁,hKU₁,hU₁e,T,S,hT,hS,hTe,hST,hTS⟩ :=
    JetPolynomial.compact_coordinate_representatives e (transition_smooth (i : M) (j : M)) hei hK hKe
  obtain ⟨U₂,hU₂,hKU₂,hU₂e,a,ha,hae,_,hrel⟩ := A.compact_jetChartMap_transition i j hK hKe
  let U := U₁ ∩ U₂
  refine ⟨U,hU₁.inter hU₂,fun x hx => ⟨hKU₁ hx,hKU₂ hx⟩,
    fun x hx => hU₁e hx.1,localizedPolynomialPullback P T S a,
    localizedPolynomialPullback_smooth hP hT hS ha,?_⟩
  intro F hF x hx hw ε t
  have hgerm : (fun y => a y • A.jetChartMap i F y) =ᶠ[𝓝 x]
      (A.jetChartMap j F ∘ T) := by
    filter_upwards [hrel F x hx.2 hw,hU₁.mem_nhds hx.1] with y hy hyU
    change a y • A.jetChartMap i F y = A.jetChartMap j F (T y)
    rw [hTe hyU]
    exact hy.symm
  have hv := localizedPolynomialPullback_eval P hT hS ha hU₁ hST hTS
    (A.jetChartMap_smooth j hF) (A.jetChartMap_smooth i hF) hx.1 hgerm ε t
  simpa only [hTe hx.1] using hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
