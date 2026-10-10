import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FixedChartTables
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SpatialChartGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TangentChartTemplates

def slopeDirection (d : Fin 2) : Fin 4 := ⟨d.val+2,by omega⟩
def slopeTestIndex (d : Fin 2) : Fin 5 := ⟨d.val+3,by omega⟩

@[simp] theorem initialTest_slope (a : ℕ) (r : CutRing) (d : Fin 2) :
    initialTest a r (slopeTestIndex d) = clippedSlopePrimitive a r (slopeDirection d) := by
  fin_cases d <;> rfl

noncomputable def tangentOffset (a : ℕ) (d : Fin 2) (e : CutRing) : CutRing × CutRing :=
  if d=0 then (e,cutTau^a*e) else (cutTau^a*e,e)

@[simp] theorem tangentOffset_zero (a : ℕ) (d : Fin 2) : tangentOffset a d 0 = 0 := by
  simp [tangentOffset]

@[simp] theorem tangentOffset_add (a : ℕ) (d : Fin 2) (e f : CutRing) :
    tangentOffset a d (e+f) = tangentOffset a d e+tangentOffset a d f := by
  fin_cases d <;> simp [tangentOffset,mul_add]

@[simp] theorem integralCutForm_tangentOffset (a : ℕ) (d : Fin 2) (e : CutRing) :
    integralCutForm a (slopeDirection d) (tangentOffset a d e) = 0 := by
  fin_cases d <;> simp [slopeDirection,tangentOffset,integralCutForm]

noncomputable def tangentChartTemplate (a k : ℕ) (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) :
    Fin 2 ⊕ (Fin 2 × Fin (k-1)) → Fin 5 × (CutRing × CutRing)
  | Sum.inl i => (slopeTestIndex d,if i=0 then 0 else tangentOffset a d e)
  | Sum.inr i => coordinateWindowPrimitives k p i

noncomputable def translatedTemplate {ι : Type*}
    (P : ι → Fin 5 × (CutRing × CutRing)) (z : CutRing × CutRing) :
    ι → Fin 5 × (CutRing × CutRing) := fun i => ((P i).1,z+(P i).2)

noncomputable def signedShortSteps (u : CutRing) : Fin 5 → CutRing := ![0,u,-u,cutTau*u,-(cutTau*u)]

theorem tangentChartTables_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ d e z I b hb, B.PrimitiveFamilyLaw I b hb
        (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) := by
  exact fixedChartTables_eventually hr hm'
    (fun de : Fin 2 × Fin 5 => tangentChartTemplate a k p de.1 (signedShortSteps u de.2)) |>.imp
    (fun L hL M hM B d e z I b hb => hL M hM B (d,e) z I b hb)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

def TangentChartLaws (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) : Prop :=
  ∀ d e z I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)

noncomputable def tangentSign (hlarge : 15 < m+1) (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing)
    (h : B.TangentChartLaws k p u) (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u 0)) z)
    (h d 0 z) (if positive then spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))
      else (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d)))ᶜ)

theorem tangentSign_first (hlarge : 15 < m+1) (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing)
    (h : B.TangentChartLaws k p u) (d : Fin 2) (z : CutRing × CutRing) (e : Fin 5) (positive : Bool) :
    B.tangentSign hlarge k p u h d z positive =
      B.fullGeometricSector hlarge
        (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) (h d e z)
        (if positive then spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))
          else (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d)))ᶜ) := by
  unfold tangentSign
  refine B.fullGeometricSector_shared_primitive hlarge
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u 0)) z)
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
    (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2)) ?_ (h d 0 z) (h d e z) _ ?_
  · simp only [translatedTemplate,tangentChartTemplate,ite_true]
  · intro x y he
    have hh := he ()
    change x ∈ (spatialTranslate (z+0) (initialTest a r (slopeTestIndex d))).val ↔
      y ∈ (spatialTranslate (z+0) (initialTest a r (slopeTestIndex d))).val at hh
    simp only [add_zero,initialTest_slope] at hh
    cases positive with
    | false => simpa using (not_congr hh)
    | true => simpa using hh

theorem tangentSign_second (hlarge : 15 < m+1) (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing)
    (h : B.TangentChartLaws k p u) (d : Fin 2) (z : CutRing × CutRing) (e : Fin 5) (positive : Bool) :
    B.tangentSign hlarge k p u h d (z+tangentOffset a d (signedShortSteps u e)) positive =
      B.fullGeometricSector hlarge
        (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) (h d e z)
        (if positive then spatialTranslate (z+tangentOffset a d (signedShortSteps u e))
            (clippedSlopePrimitive a r (slopeDirection d))
          else (spatialTranslate (z+tangentOffset a d (signedShortSteps u e))
            (clippedSlopePrimitive a r (slopeDirection d)))ᶜ) := by
  unfold tangentSign
  refine B.fullGeometricSector_shared_primitive hlarge
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u 0))
      (z+tangentOffset a d (signedShortSteps u e)))
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) ?_ (h d 0 _) (h d e z) _ ?_
  · simp [translatedTemplate,tangentChartTemplate]
  · intro x y he
    have hh := he ()
    change x ∈ (spatialTranslate ((z+tangentOffset a d (signedShortSteps u e))+0)
        (initialTest a r (slopeTestIndex d))).val ↔
      y ∈ (spatialTranslate ((z+tangentOffset a d (signedShortSteps u e))+0)
        (initialTest a r (slopeTestIndex d))).val at hh
    simp only [add_zero,initialTest_slope] at hh
    cases positive with
    | false => simpa using (not_congr hh)
    | true => simpa using hh

end InitialCoverSystem
end TangentChartTemplates

section TangentChartAction

@[simp] theorem integralCutForm_zero (a : ℕ) (j : Fin 4) :
    integralCutForm a j (0 : CutRing × CutRing) = 0 := by
  fin_cases j <;> simp [integralCutForm]

@[simp] theorem integralCutForm_add (a : ℕ) (j : Fin 4) (u v : CutRing × CutRing) :
    integralCutForm a j (u+v) = integralCutForm a j u+integralCutForm a j v := by
  fin_cases j <;> simp [integralCutForm,mul_add] <;> ring

theorem translatedTemplate_resolved {a : ℕ} {r : CutRing} {ι : Type*}
    (P : ι → Fin 5 × (CutRing × CutRing)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r) P i).val) V.val)
    (z : CutRing × CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (translatedTemplate P z) i).val) (spatialTranslate z V).val := by
  simpa only [InitialCoverSystem.primitiveTests,primitiveFamilyTests,translatedTemplate,
    ← spatialTranslate_add] using spatialTranslate_resolved
      (InitialCoverSystem.primitiveTests (a := a) (r := r) P) V hV z

theorem tangentChart_first_resolved {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) (z : CutRing × CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (translatedTemplate (tangentChartTemplate a k p d e) z) i).val)
      (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))).val := by
  intro x y he
  have hh := he (Sum.inl 0)
  simpa [InitialCoverSystem.primitiveTests,primitiveFamilyTests,translatedTemplate,
    tangentChartTemplate] using hh

theorem tangentChart_second_resolved {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) (z : CutRing × CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (translatedTemplate (tangentChartTemplate a k p d e) z) i).val)
      (spatialTranslate (z+tangentOffset a d e) (clippedSlopePrimitive a r (slopeDirection d))).val := by
  intro x y he
  have hh := he (Sum.inl 1)
  simpa [InitialCoverSystem.primitiveTests,primitiveFamilyTests,translatedTemplate,
    tangentChartTemplate] using hh

theorem tangentChart_rectangle_resolved {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (translatedTemplate (tangentChartTemplate a k p d e) z) i).val)
      (spatialTranslate z (coordinateRectangle a l v)).val := by
  apply translatedTemplate_resolved
  intro x y he
  exact and_congr
    (coordinateLabelWindow_resolved k p 0 (l 0) (v 0) (hl 0) (hv 0) x y
      (fun i => he (Sum.inr i)))
    (coordinateLabelWindow_resolved k p 1 (l 1) (v 1) (hl 1) (hv 1) x y
      (fun i => he (Sum.inr i)))

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentSign_step_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ j, -ordinary r < ordinary (l j)-ordinary
          (if j=0 then (tangentOffset a d (signedShortSteps u e)).1
           else (tangentOffset a d (signedShortSteps u e)).2) ∧
        ordinary (v j)-ordinary
          (if j=0 then (tangentOffset a d (signedShortSteps u e)).1
           else (tangentOffset a d (signedShortSteps u e)).2) < ordinary r)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega)
      (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
        (h d e z) (spatialTranslate z (coordinateRectangle a l v))))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.tangentSign (by omega) k p u h d (z+tangentOffset a d (signedShortSteps u e)) true
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z+tangentOffset a d (signedShortSteps u e)) true
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  rw [B.tangentSign_first (by omega) k p u h d z e true,
    B.tangentSign_second (by omega) k p u h d z e true]
  apply B.chart_action_transfer hlarge _ (h d e z) _ _ _
    (tangentChart_first_resolved p d _ z) (tangentChart_second_resolved p d _ z)
    (tangentChart_rectangle_resolved p d _ z l v hl hv) _ f hf hc I s
  have he := clippedSlope_agree_on_rectangle (a := a) r (slopeDirection d) hr
    (0 : CutRing × CutRing) (tangentOffset a d (signedShortSteps u e)) l v hlv hlen
    (by simpa using hbox) hbox' (by simp only [integralCutForm_zero,integralCutForm_tangentOffset])
  have he' := congrArg (spatialTranslate z) he
  simpa only [spatialTranslate_inter,← spatialTranslate_add,add_zero] using he'

theorem tangentSign_opposite_commute (hlarge : 15 < m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (z : CutRing × CutRing) (s t : TrackStar (Fin (m+1))) :
    Commute (B.tangentSign hlarge k p u h d z true s)
      (B.tangentSign hlarge k p u h d z false t) := by
  unfold tangentSign
  apply B.fullGeometricSector_commute
  · exact tangentChart_first_resolved p d _ z
  · exact disjoint_compl_right

end InitialCoverSystem
end TangentChartAction

end SimpleAmenable
end
end

end OAI
