import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityFamily

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion
local notation "ι" => JetVelocityCoordinates.toEuclidean

lemma first_slot {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    slot (![1, 2] i) (lowJet G p) = fderiv ℝ G p (coordinateVector i) := by
  funext a
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_apply (hG.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => G q a) p (coordinateVector i) := by fin_cases i <;> rfl
    _ = _ := he

lemma euclidean_first_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector i) =
      ι (slot (![1, 2] i) (lowJet G p)) := by
  have hd := (JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp p
    (hG.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = ι (fderiv ℝ G p (coordinateVector i)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector i)) hd
    _ = _ := congrArg ι (first_slot hG i p).symm

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma leading_xx {J : LowJet} (hJ : J ∈ O) :
    inner ℝ (ι (tangent J)) (ι (tangent J)) + l.q J =
      inner ℝ (ι (slot 1 J)) (ι (slot 1 J)) + l.amplitude J ^ 2 := by
  have hp := realNormalPart_perp (slot 2 J) (slot 6 J) (slot 1 J) (l.gram_ne J hJ)
  have ht : tangent J ⬝ᵥ normal J = 0 := tangential_part_perp _ _ _ _ hp.1 hp.2
  have hx : slot 1 J = tangent J + normal J := by dsimp [tangent]; abel
  simp only [inner_toEuclidean, q]
  conv_rhs => rw [hx]
  simp only [add_dotProduct, dotProduct_add, ht, dotProduct_comm (normal J) (tangent J)]
  ring

include l in
lemma leading_xy {J : LowJet} (hJ : J ∈ O) :
    inner ℝ (ι (tangent J)) (ι (slot 2 J)) =
      inner ℝ (ι (slot 1 J)) (ι (slot 2 J)) := by
  have hp := realNormalPart_perp (slot 2 J) (slot 6 J) (slot 1 J) (l.gram_ne J hJ)
  simp only [inner_toEuclidean, tangent, sub_dotProduct]
  rw [dotProduct_comm (normal J) (slot 2 J), show slot 2 J ⬝ᵥ normal J = 0 from hp.1, sub_zero]

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

lemma geometry_mean {p : JetPolynomial.Base} (hp : p ∈ S) :
    average ((l.geometry G hG hGO).V.val p) = ι (normal (lowJet G p)) := by
  rw [l.geometry_velocity hG hGO hp]
  exact l.euclideanVelocity_mean (hGO hp)

lemma geometry_dx {p : JetPolynomial.Base} (hp : p ∈ S) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 0) =
      (l.geometry G hG hGO).X₀ p + average ((l.geometry G hG hGO).V.val p) := by
  rw [euclidean_first_derivative hG, l.geometry_mean hG hGO hp]
  change ι (slot 1 (lowJet G p)) = ι (tangent (lowJet G p)) + ι (normal (lowJet G p))
  rw [← map_add]
  congr 1
  dsimp [tangent]
  abel

lemma geometry_dy (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 1) = (l.geometry G hG hGO).Y p :=
  euclidean_first_derivative hG 1 p

lemma geometry_initial_zero {p : JetPolynomial.Base} (hp : p ∈ S)
    (hz : ∀ t, l.velocity (lowJet G p, t) = normal (lowJet G p)) :
    (l.geometry G hG hGO).initial.val p = 0 := by
  apply Family.primitive_zero_at _ _ hp
  apply ContinuousMap.ext
  intro t
  rw [Family.sub_apply, Family.vectorMean_apply, l.geometry_mean hG hGO hp,
    l.geometry_velocity hG hGO hp]
  refine Quotient.inductionOn' t ?_
  intro t
  rw [l.euclideanVelocity_apply (hGO hp), hz, sub_self]
  rfl

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
