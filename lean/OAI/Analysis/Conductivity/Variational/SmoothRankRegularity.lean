import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

lemma smoothPair_gradientColumns_continuous {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    Continuous (fun x => (gradientColumns (fderiv ℝ u x)).col) := by
  apply continuous_pi; intro j
  apply continuous_pi; intro i
  exact (continuous_apply j).comp ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma smoothPair_mem_regularRegion {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {x : Coord3} (hxrank : LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) : x∈regularRegion u A U := by
  let O := {y : Coord3 | LinearIndependent ℝ (gradientColumns (fderiv ℝ u y)).col}
  have hO : IsOpen O := isOpen_setOfPred_linearIndependent.preimage (smoothPair_gradientColumns_continuous hu)
  exact mem_regularRegion_iff.mpr ⟨U∩O,inter_subset_left,
    ⟨hU.inter hO,hu.contDiffOn,hA.contDiffOn,Or.inl (fun y hy => hy.2)⟩,hx,hxrank⟩

lemma smoothPair_regularRegion_ae {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {U : Set Coord3} (hU : IsOpen U)
    (hrank : ∀ᵐ x : Coord3,x∈U → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion u A U := by
  filter_upwards [hrank] with x hx
  intro hxU
  exact smoothPair_mem_regularRegion hu hA (hx hxU) hU hxU

end ScalarConductivity

end
end

end OAI
