import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileFrame
import OAI.Geometry.SurfaceImmersion.Geometry.OrderedBoundaryInvariant
import OAI.Geometry.Immersion.ClosedSurface.ProjectionBounds

namespace OAI

/-! Unscaled five-jets encode the actual second form and ordered crossings.
These expressions are used for exterior C2 stability. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetSecond (J : BoundaryProfile) (v w : Base) : Vec :=
  realNormalPart (J 0) (J 1)
    ((v.1*w.1) • J 4+(v.1*w.2+v.2*w.1) • J 3+(v.2*w.2) • J 2)

def boundaryJetCrossing (J : BoundaryProfile) (v w : Base) (κ : ℝ) : ℝ :=
  (boundaryJetSecond J v w ⬝ᵥ normalize (boundaryJetSecond J v v))^2+
    κ*NormalFrame.gramDet (v.1 • J 0+v.2 • J 1) (w.1 • J 0+w.2 • J 1)

lemma boundaryJetSecond_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p v w : Base) :
    boundaryJetSecond (realBoundaryProfile F 1 p) v w = realSecondForm F v w p := by
  unfold boundaryJetSecond realBoundaryProfile realSecondForm
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,one_smul]
  rw [second_coordDeriv_bilinear hF v w p]

lemma boundaryJetCrossing_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p v w : Base) (κ : ℝ) :
    boundaryJetCrossing (realBoundaryProfile F 1 p) v w κ = orderedCrossing F v w p κ := by
  unfold boundaryJetCrossing orderedCrossing
  rw [boundaryJetSecond_actual hF,boundaryJetSecond_actual hF]
  simp only [realBoundaryProfile,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← coordDeriv_eq_basis F v,← coordDeriv_eq_basis F w]

lemma continuousAt_boundaryJetSecond {J : BoundaryProfile} (v w : Base)
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0) :
    ContinuousAt (fun a : BoundaryProfile × (Base × Base) => boundaryJetSecond a.1 a.2.1 a.2.2)
      (J,v,w) := by
  have h0 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) => a.1 0) :=
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.comp contDiff_fst
  have h1 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) => a.1 1) :=
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) =>
      (a.2.1.1*a.2.2.1) • a.1 4+(a.2.1.1*a.2.2.2+a.2.1.2*a.2.2.1) • a.1 3+
        (a.2.1.2*a.2.2.2) • a.1 2) := by fun_prop
  exact (contDiffAt_realNormalPart h0.contDiffAt h1.contDiffAt h2.contDiffAt hD).continuousAt

lemma continuousAt_boundaryJetCrossing {J : BoundaryProfile} {v w : Base} {κ : ℝ}
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0) (hP : boundaryJetSecond J v v ≠ 0) :
    ContinuousAt (fun a : BoundaryProfile × (Base × (Base × ℝ)) =>
      boundaryJetCrossing a.1 a.2.1 a.2.2.1 a.2.2.2) (J,v,w,κ) := by
  let Z := BoundaryProfile × (Base × (Base × ℝ))
  have hm : Continuous (fun a : Z => (a.1,a.2.1,a.2.2.1)) := by fun_prop
  have hp : Continuous (fun a : Z => (a.1,a.2.1,a.2.1)) := by fun_prop
  have hM := (continuousAt_boundaryJetSecond v w hD).comp
    (f := fun a : Z => (a.1,a.2.1,a.2.2.1)) (x := (J,v,w,κ)) hm.continuousAt
  have hV := (continuousAt_boundaryJetSecond v v hD).comp
    (f := fun a : Z => (a.1,a.2.1,a.2.1)) (x := (J,v,w,κ)) hp.continuousAt
  have hn := (normalize_smoothAt contDiffAt_id hP).continuousAt.comp
    (f := fun a : Z => boundaryJetSecond a.1 a.2.1 a.2.1) (x := (J,v,w,κ)) hV
  have hdot : ContinuousAt (fun a : Z => boundaryJetSecond a.1 a.2.1 a.2.2.1 ⬝ᵥ
      normalize (boundaryJetSecond a.1 a.2.1 a.2.1)) (J,v,w,κ) := by
    have hd : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
      unfold dotProduct
      fun_prop
    exact hd.continuousAt.comp (f := fun a : Z =>
      (boundaryJetSecond a.1 a.2.1 a.2.2.1,normalize (boundaryJetSecond a.1 a.2.1 a.2.1)))
      (x := (J,v,w,κ)) (hM.prodMk hn)
  have hgram : Continuous (fun a : Z => a.2.2.2*
      NormalFrame.gramDet (a.2.1.1 • a.1 0+a.2.1.2 • a.1 1) (a.2.2.1.1 • a.1 0+a.2.2.1.2 • a.1 1)) := by
    have hp : Continuous (fun a : Z =>
        (a.2.1.1 • a.1 0+a.2.1.2 • a.1 1,a.2.2.1.1 • a.1 0+a.2.2.1.2 • a.1 1)) := by
      dsimp [Z]
      fun_prop
    exact (show Continuous (fun a : Z => a.2.2.2) by fun_prop).mul
      (contDiff_gram_pair.continuous.comp hp)
  exact (hdot.pow 2).add hgram.continuousAt

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
