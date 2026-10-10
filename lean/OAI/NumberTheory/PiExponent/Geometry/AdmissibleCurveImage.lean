import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry
import OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.AdmissibleCurveImage
open AdmissibleBlowupGeometry CurveBlowupImage
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem center_point_isClosed (x : compactification d)
    (hx : x ∈ (centerIdeal d).support) : IsClosed ({x} : Set (compactification d)) := by
  change x ∈ ((centerIdeal d).support : Set (compactification d)) at hx
  rw [centerIdeal_support d] at hx
  obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
  let q := CompactLogJetIdeal.point (d.curveCenters j) ≫ affineChart d
  let : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion
    (compactificationStructureMap d) q (by
      dsimp [q]
      rw [Category.assoc, affineChart_over, CompactLogJetIdeal.point_section])
  have he : Set.range q = {q z} := by
    ext x
    constructor
    · rintro ⟨z',rfl⟩
      exact congrArg q (Subsingleton.elim z' z)
    · rintro rfl
      exact ⟨z,rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

theorem meets_center_complement (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (centerIdeal d).support.compl :=
  exists_image_outside_closed_points (C.embedding ≫ projection d)
    (centerIdeal d).support (center_point_isClosed d) hn

instance projection_restrict_isIso :
    IsIso (projection d ∣_ (centerIdeal d).support.compl) :=
  blowup_restrict_isIso (isBlowup d)

abbrev imageCurve (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :=
  CurveBlowupImage.imageCurve (projection d) C hn

def functionFieldIso (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    (imageCurve d C hn).scheme.functionField ≅ C.scheme.functionField :=
  imageFunctionFieldIso (projection d) C hn (centerIdeal d).support.compl
    (meets_center_complement d C hn)

theorem functionFieldIso_generic (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    Spec.map (functionFieldIso d C hn).hom ≫
      (imageCurve d C hn).scheme.fromSpecStalk (genericPoint (imageCurve d C hn).scheme) ≫
      (imageCurve d C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ projection d :=
  imageFunctionFieldIso_generic (projection d) C hn (centerIdeal d).support.compl
    (meets_center_complement d C hn)

theorem image_meets_chart (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    ∃ c : (imageCurve d C hn).scheme,
      (imageCurve d C hn).embedding c ∈ (affineChart d).opensRange := by
  obtain ⟨c,hc⟩ := hm
  refine ⟨CurveBlowupImage.imageMap (projection d) C hn c, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, CurveBlowupImage.imageMap_comp] using hc

end PiExponent.AdmissibleCurveImage

end

end OAI
