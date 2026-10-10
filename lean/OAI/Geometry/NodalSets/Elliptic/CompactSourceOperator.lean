import OAI.Geometry.NodalSets.Elliptic.CompactSourceRepresentatives
import OAI.Geometry.NodalSets.Elliptic.FiniteLinearity

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def smoothFluxOperator (v : Coord → ℂ) (F : Fin 4 → Fin 4 → Coord → ℂ)
    (u : Coord → ℂ) (x : Coord) : ℂ :=
  v x * ∑ i, coordPartial i (fun z ↦ ∑ j, F i j z*coordPartial j u z) x

lemma smoothFluxOperator_smooth (v : Coord → ℂ) (F : Fin 4 → Fin 4 → Coord → ℂ)
    (hv : ContDiff ℝ ∞ v) (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (smoothFluxOperator v F u) :=
  hv.mul (ContDiff.sum (fun i _ ↦ coordPartial_contDiff
    (ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))) i))

theorem compact_source_operator_coefficients {Q U : Set Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (v : Coord → ℂ) (F : Fin 4 → Fin 4 → Coord → ℂ),
      ContDiff ℝ ∞ v ∧ (∀ i j, ContDiff ℝ ∞ (F i j)) ∧
      ∀ x ∈ Q, ∀ u : Coord → ℂ,
        sourceWeightedOperator g w u =ᶠ[𝓝 x] smoothFluxOperator v F u := by
  obtain ⟨G,W,A,E,hG,hW,_,hGs,hGp,hE,hQE,hEU,hWp,he⟩ :=
    compact_source_representatives hQ hU hQU hUn g hg hs hp w (fun _ ↦ 0) hw contDiffOn_const hwp
  have hWi : ContDiffOn ℝ ∞ (fun x ↦ (W x)⁻¹) E :=
    hW.contDiffOn.inv (fun x hx ↦ ne_of_gt (hWp x hx))
  obtain ⟨V,hV,_,_,hVe⟩ := compact_smooth_extension hQ hE hQE _ hWi
  let F : Fin 4 → Fin 4 → Coord → ℂ := fun i j x ↦ (W x:ℂ)*(sourcePrincipal G i j x:ℂ)
  have hF (i j : Fin 4) : ContDiff ℝ ∞ (F i j) := by
    have ha : ContDiff ℝ ∞ (sourcePrincipal G i j) :=
      contDiff_iff_contDiffAt.mpr (fun x ↦ sourcePrincipal_smooth_at G hG x (hGp x) i j)
    exact (Complex.ofRealCLM.contDiff.comp hW).mul (Complex.ofRealCLM.contDiff.comp ha)
  refine ⟨fun x ↦ (V x:ℂ),F,Complex.ofRealCLM.contDiff.comp hV,hF,?_⟩
  intro x hx u
  have hcoef := sourceOperator_coefficients_eventuallyEq (he x (hQE hx)).1.symm
    (he x (hQE hx)).2.1.symm u
  filter_upwards [hcoef,hVe x hx] with z hz hvz
  rw [hz]
  simp only [smoothFluxOperator,sourceWeightedOperator,complexDivergence,F,hvz,
    Complex.ofReal_inv]
  rfl

end
end Yau.Geometry

end OAI
