import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanPolynomial

namespace OAI

/-! A prescribed spatial amplitude is independent of the varying immersion,
even though the coefficient calculus stores it as a function of the full jet. -/

noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

/-- The position slots of an actual low jet. -/
def lowJetPosition : LowJet →L[ℝ] Base :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (.inl i))

@[simp] lemma lowJetPosition_apply (J : LowJet) (i : Fin 2) :
    lowJetPosition J i = J (.inl i) := rfl

@[simp] lemma lowJetPosition_lowJet (G : Base → Space) (p : Base) :
    lowJetPosition (lowJet G p) = p := by
  ext i
  rfl

@[simp] lemma lowJetPosition_variationLowJet (H : Base → Space) (p : Base) :
    lowJetPosition (variationLowJet H p) = 0 := by
  ext i
  rfl

/-- Store a fixed function of position in the existing low-jet coefficient API. -/
def spatialAmplitude (a : Base → ℝ) : LowJet → ℝ := fun J => a (lowJetPosition J)

lemma spatialAmplitude_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialAmplitude a) := ha.comp lowJetPosition.contDiff

@[simp] lemma spatialAmplitude_lowJet (a : Base → ℝ) (G : Base → Space) (p : Base) :
    spatialAmplitude a (lowJet G p) = a p := by
  simp only [spatialAmplitude,lowJetPosition_lowJet]

/-- The spatial coefficient has zero derivative in every actual map-variation
direction: none of the position slots changes with the immersion. -/
lemma spatialAmplitude_variation_zero {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (J : LowJet) (H : Base → Space) (p : Base) :
    fderiv ℝ (spatialAmplitude a) J (variationLowJet H p) = 0 := by
  change fderiv ℝ (a ∘ lowJetPosition) J (variationLowJet H p) = 0
  rw [fderiv_comp J (ha.differentiable (by simp) (lowJetPosition J))
    lowJetPosition.differentiableAt,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.fderiv,lowJetPosition_variationLowJet,map_zero]

end ClosedSurfaceR4.JetPolynomial

namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

/-- The given amplitude is fixed as a function of the base point, throughout
the whole open jet domain used for nearby immersions. -/
def HasSpatialAmplitude (a : Base → ℝ) : Prop :=
  ∀ J ∈ O, l.amplitude J = a (lowJetPosition J)

lemma amplitude_at_lowJet {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    (G : JetPolynomial.Base → JetPolynomial.Space) {p : JetPolynomial.Base}
    (hp : lowJet G p ∈ O) :
    l.amplitude (lowJet G p) = a p := by
  simpa only [lowJetPosition_lowJet] using ha (lowJet G p) hp

/-- In particular, changing the immersion does not change the primitive
amplitude at the same spatial point. -/
lemma amplitude_independent_of_map {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    (G H : JetPolynomial.Base → JetPolynomial.Space) {p : JetPolynomial.Base}
    (hG : lowJet G p ∈ O) (hH : lowJet H p ∈ O) :
    l.amplitude (lowJet G p) = l.amplitude (lowJet H p) :=
  (l.amplitude_at_lowJet ha G hG).trans (l.amplitude_at_lowJet ha H hH).symm

/-- Normalize the record field itself to the fixed spatial function while
preserving the same velocity loop and its proved geometric identities. -/
def withSpatialAmplitude (a : Base → ℝ) (ha : ContDiff ℝ ∞ a)
    (he : l.HasSpatialAmplitude a) : SurfaceVelocityFamily.Loop O where
  amplitude := spatialAmplitude a
  smoothAmplitude := (spatialAmplitude_smooth ha).contDiffOn
  velocity := l.velocity
  smoothVelocity := l.smoothVelocity
  periodic := l.periodic
  gram_ne := l.gram_ne
  nonzero J hJ := by
    rw [show spatialAmplitude a J = l.amplitude J from (he J hJ).symm]
    exact l.nonzero J hJ
  perpY := l.perpY
  perpC := l.perpC
  length J hJ t := by
    rw [show spatialAmplitude a J = l.amplitude J from (he J hJ).symm]
    exact l.length J hJ t
  mean := l.mean

@[simp] lemma withSpatialAmplitude_amplitude (a : Base → ℝ) (ha : ContDiff ℝ ∞ a)
    (he : l.HasSpatialAmplitude a) (J : LowJet) :
    (l.withSpatialAmplitude a ha he).amplitude J = a (lowJetPosition J) := rfl

lemma withSpatialAmplitude_fixed (a : Base → ℝ) (ha : ContDiff ℝ ∞ a)
    (he : l.HasSpatialAmplitude a) : (l.withSpatialAmplitude a ha he).HasSpatialAmplitude a :=
  fun _ _ => rfl

/-- The existing mean-polynomial theorem with its primitive rank-one term
written as the prescribed spatial amplitude, uniformly for all nearby maps. -/
theorem meanMetric_eq_spatial_polynomial {a : Base → ℝ} (ha : l.HasSpatialAmplitude a)
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (n : ℕ) (b c : Bool)
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i))
    (z : ℝ) {p : JetPolynomial.Base} (hp : p ∈ S) :
    MetricPolynomial.meanMetric (l.geometry G hG hGO) (coordinateVector 0) U n b c z p =
      inner ℝ
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
      (if b && c then a p^2 else 0) +
        Perturbation.eval (l.meanPolynomial n b c) z G (p,0) := by
  rw [l.meanMetric_eq_polynomial hG hGO n b c U hU z hp,
    l.amplitude_at_lowJet ha G (hGO hp)]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
