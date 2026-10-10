import Mathlib
import OAI.Geometry.SplitTangent.AmbientLeafSections
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveJetFiltration
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.TensorSectionSpace

namespace OAI

/-! Ambient Leaf Section Bound. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AmbientTransition
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X} {d : ℕ}
  (T : AmbientTransition g d) (A : LeafJetAtlas S)

 
abbrev GermSpace := SeparatedQuotientFiltration.Space (T.contact A)

theorem germ_finite_and_bound (hg : PointedGenerated g S.first) :
    Module.Finite ℂ (T.GermSpace A) ∧ Module.finrank ℂ (T.GermSpace A) ≤
      (d+Module.finrank ℂ (S.first (g.finite 1))).choose
        (Module.finrank ℂ (S.first (g.finite 1)))*(d+1) := by
  let : ∀m,AddCommGroup (symmetricSupportedTensors g S (d : ℤ) m) :=
    fun _ => Module.addCommMonoidToAddCommGroup ℂ
  let F := T.contact A
  let L := T.leading A
  let G := SeparatedQuotientFiltration.stage F
  let D := SeparatedQuotientFiltration.leading F L (T.leading_kernel A)
  have hker : ∀m v,D m v=0 ↔ v.val∈G (m+1) :=
    SeparatedQuotientFiltration.leading_kernel F L (T.leading_kernel A)
  have hsep : ∀v,(∀m,v∈G m) → v=0 := SeparatedQuotientFiltration.separated F
  obtain ⟨hf,hb⟩ := PositiveJetFiltration.polynomial_bound G
    (SeparatedQuotientFiltration.stage_antitone F (T.contact_antitone A)) D hker hg hsep
  have hzero : G 0=⊤ := by
    change (T.contact A 0).map (SeparatedQuotientFiltration.zeroPart F).mkQ=⊤
    rw [T.contact_zero A,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)
  let E : G 0 ≃ₗ[ℂ] T.GermSpace A := LinearEquiv.ofTop _ hzero
  let : Module.Finite ℂ (G 0) := hf
  refine ⟨Module.Finite.equiv E,?_⟩
  rw [←E.finrank_eq]
  exact hb

end SplitTangent.AmbientTransition

end

end OAI
