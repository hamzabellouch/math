import Mathlib

namespace OAI


                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {X Y : Scheme.{0}}

lemma integral_scheme_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  let (chart : f.ker.subschemeCover.openCover.I₀) :
      AlgebraicGeometry.IsReduced (f.ker.subschemeCover.openCover.X chart) := by
    change Y.affineOpens at chart
    let : _root_.IsReduced (Γ(Y,chart.1) ⧸ f.ker.ideal chart) := by
      rw [Scheme.Hom.ker_apply]
      exact isReduced_of_injective (RingHom.kerLift (f.app chart.1).hom)
        (RingHom.kerLift_injective (f.app chart.1).hom)
    change IsReduced (Spec (.of (Γ(Y,chart.1) ⧸ f.ker.ideal chart)))
    infer_instance
  let : IsReduced f.image := IsReduced.of_openCover f.image f.ker.subschemeCover.openCover
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image f.toImage
        f.toImage.continuous.continuousOn
  let : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

lemma residue_image_integral (X : Scheme.{0}) (x : X) :
    IsIntegral (X.fromSpecResidueField x).image := integral_scheme_image _

lemma residue_image_range (X : Scheme.{0}) (x : X) :
    Set.range (X.fromSpecResidueField x).imageι = closure {x} := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι,
    Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]

end
end MaximalSeshadri.Geometry

end

end OAI
