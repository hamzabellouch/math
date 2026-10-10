import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RawNormal

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X] {k : ℕ}
lemma form_eq_of_chart_pullback (p : X) (a b : Form X k) {x : X}
    (hx : x ∈ (extChartAt Model p).source)
    (h : pullback a (extChartAt Model p).symm (extChartAt Model p x) =
      pullback b (extChartAt Model p).symm (extChartAt Model p x)) : a x = b x := by
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model) hx
  simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at hi
  have hh := congrArg (fun c : Space [⋀^Fin k]→L[ℝ] ℝ =>
    c.compContinuousLinearMap (mfderiv Model Model (extChartAt Model p) x)) h
  simp only [pullback] at hh
  erw [(extChartAt Model p).left_inv hx] at hh
  change (a x).compContinuousLinearMap
      (mfderiv Model Model (extChartAt Model p).symm (extChartAt Model p x) ∘L
        mfderiv Model Model (extChartAt Model p) x) =
    (b x).compContinuousLinearMap
      (mfderiv Model Model (extChartAt Model p).symm (extChartAt Model p x) ∘L
        mfderiv Model Model (extChartAt Model p) x) at hh
  erw [hi] at hh
  exact hh
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma manifoldTest_eq {b : TwoForm X} (hb : antiInvariantPart J b = b)
    (q : Space → EuclideanEnergy.Pair) (hqD : tsupport q ⊆ D.domain)
    (hraw : ∀ z ∈ D.domain, q z = rawPair J α ht p D b z)
    (hbzero : ∀ x ∉ (extChartAt Model p).symm '' D.domain, b x = 0) :
    manifoldTest J α ht p D q = b := by
  funext x
  by_cases hx : x ∈ (extChartAt Model p).symm '' D.domain
  · obtain ⟨z,hz,rfl⟩ := hx
    apply form_eq_of_chart_pullback p _ _ ((extChartAt Model p).map_target (D.domain_subset hz))
    rw [(extChartAt Model p).right_inv (D.domain_subset hz)]
    change TamingCompatibility.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      TamingCompatibility.pullback b (extChartAt Model p).symm z
    rw [pullback_manifoldTest J α ht p D hqD (D.domain_subset hz)]
    have he : TamingCompatibility.pullback b (extChartAt Model p).symm z =
        coordinateTest J α ht p D (rawPair J α ht p D b) z :=
      rawScalar_expansion J α ht p D hb hz
    rw [he]
    simp only [coordinateTest,LocalMatrixOperator.frameTest,hraw z hz]
  · rw [hbzero x hx,manifoldTest_zero_off J α ht p D q]
    exact fun h => hx ((image_mono hqD) h)
end TamingCompatibility.GeometricChart

end

end OAI
