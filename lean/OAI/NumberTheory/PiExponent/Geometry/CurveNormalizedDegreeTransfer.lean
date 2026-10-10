import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective
import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizedDegreeTransfer
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness CurveNormalizationModel
variable {B X : Scheme.{0}} {E : Type} [Field E] [Algebra ℂ E]

theorem curveDegree_eq_normalized
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle B) :
    curveDegree p L C =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (L.pullback (g ≫ C.embedding)).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) := by
  have h := CurveNormalizationDegree.parameterCurve_pullback_euler_degree_of_ample
    (C.embedding ≫ p) (H.pullback C.embedding)
    (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    C.dimension.le f hf g hg W hW (L.pullback C.embedding)
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g C.embedding).app L.sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
    ((L.pullback C.embedding).pullback g).sheaf = _ at he
  rw [he] at h
  exact h.symm

theorem curveDegree_pullback_eq_normalized
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)]
    (π : B ⟶ X) (L : LineBundle X) :
    curveDegree p (L.pullback π) C =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (L.pullback (g ≫ C.embedding ≫ π)).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) := by
  rw [curveDegree_eq_normalized p H hH C f hf g hg W hW]
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp (g ≫ C.embedding) π).app L.sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
    ((L.pullback π).pullback (g ≫ C.embedding)).sheaf = _ at he
  rw [he]
  simp only [Category.assoc, LineBundle.pullback]

theorem weighted_curveDegree
    {ι σ : Type} [Fintype ι] [Fintype σ]
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ j, a (coordinate j) = Finsupp.single j 1)
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)]
    (π : B ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) a))
    (hcoord : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ π) =
      CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x)
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    (curveDegree p ((WeightedCompactification.lineBundle (R := ℂ) a).pullback π) C : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  rw [curveDegree_pullback_eq_normalized p H hH C f hf g hg W hW]
  exact WeightedProjectiveCurveDegree.weighted_pullback_degree f hf a x z hz
    coordinate hcoordinate (g ≫ C.embedding ≫ π) hcoord w hw hR powers hpowers
    pure hpure hbudget hfinite

end PiExponent.CurveNormalizedDegreeTransfer

end

end OAI
