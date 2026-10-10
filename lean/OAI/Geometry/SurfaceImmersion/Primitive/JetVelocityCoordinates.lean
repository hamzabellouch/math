import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceJetCoordinates
import OAI.Geometry.Immersion.ClosedSurface.ChartModel
import OAI.Geometry.SurfaceImmersion.Correction.PeriodicCorrector

namespace OAI

/-! Euclidean coordinates for the geometric velocity and the actual ordered
jets used in the finite periodic expansion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetVelocityCoordinates
open RealModes JetPolynomial

abbrev Euclidean := EuclideanSpace ℝ (Fin 4)

def toEuclidean : RVec 4 ≃L[ℝ] Euclidean := spaceCoordinates.symm

lemma inner_toEuclidean (v w : RVec 4) :
    inner ℝ (toEuclidean v) (toEuclidean w) = v ⬝ᵥ w := by
  simpa [toEuclidean] using (spaceCoordinates_dot (spaceCoordinates.symm v)
    (spaceCoordinates.symm w)).symm

lemma gram_toEuclidean (v w : RVec 4) :
    PeriodicCorrector.gramDet (toEuclidean v) (toEuclidean w) =
      NormalFrame.gramDet v w := by
  simp only [PeriodicCorrector.gramDet, NormalFrame.gramDet, inner_toEuclidean]

def slot (i : Fin 7) (J : LowJet) : RVec 4 := fun a => J (.inr (i, a))

lemma slot_smooth (i : Fin 7) : ContDiff ℝ ∞ (slot i) := by
  apply contDiff_pi.mpr
  intro a
  exact (ContinuousLinearMap.proj (.inr (i, a)) : LowJet →L[ℝ] ℝ).contDiff

lemma slot_decode_x (J : LowJet) : (SurfaceJetCoordinates.decode J).2 0 = slot 1 J := rfl
lemma slot_decode_y (J : LowJet) : (SurfaceJetCoordinates.decode J).2 1 = slot 2 J := rfl
lemma slot_decode_yy (J : LowJet) : (SurfaceJetCoordinates.decode J).2 4 = slot 6 J := rfl

lemma slot_y_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => slot 2 (lowJet G q)) p (coordinateVector 1) = slot 6 (lowJet G p) := by
  funext a
  have hs := (slot_smooth 2).comp (lowJet_smooth hG)
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector 1))
    (fderiv_apply (hs.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => lowJet G q (.inr (2, a))) p (coordinateVector 1) := he.symm
    _ = lowDerivative G 1 p (.inr (2, a)) := lowJet_coordinate_derivative G 1 _ p
    _ = slot 6 (lowJet G p) a := rfl

lemma euclidean_y_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => toEuclidean (slot 2 (lowJet G q))) p (coordinateVector 1) =
      toEuclidean (slot 6 (lowJet G p)) := by
  have hs := (slot_smooth 2).comp (lowJet_smooth hG)
  have hd := (toEuclidean.hasFDerivAt.comp p
    (hs.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = toEuclidean (fderiv ℝ (fun q => slot 2 (lowJet G q)) p (coordinateVector 1)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector 1)) hd
    _ = _ := congrArg toEuclidean (slot_y_derivative hG p)

lemma tangential_part_perp (X Y C w : RVec 4)
    (hY : Y ⬝ᵥ w = 0) (hC : C ⬝ᵥ w = 0) :
    (X - realNormalPart Y C X) ⬝ᵥ w = 0 := by
  simp only [realNormalPart, sub_dotProduct, smul_dotProduct, hY, hC,
    smul_eq_mul, mul_zero, sub_zero, sub_self]

end ClosedSurfaceR4.JetVelocityCoordinates

end

end OAI
