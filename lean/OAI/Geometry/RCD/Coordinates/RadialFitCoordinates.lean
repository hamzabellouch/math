import OAI.Geometry.RCD.Coordinates.ActualCovectorFit
import OAI.Geometry.RCD.Harmonic.AffineChange

namespace OAI

/-! # Canonical local radial fits and their change of coordinates -/

open Set MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The actual radial pairing, as an element of the local L2 space. -/
def radialPairingLp (s : Set X) (q a : SobolevSpace μ hQ) {B : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ a a x ≤ B) : Lp ℝ 2 (μ.restrict s) :=
  (localGamma_memLp_two_of_bound μ hQ s q a ha).toLp (localGamma μ hQ q a)

theorem radialPairingLp_representative (s : Set X) (q a : SobolevSpace μ hQ) {B : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ a a x ≤ B) :
    radialPairingLp μ hQ s q a ha =ᵐ[μ.restrict s] localGamma μ hQ q a :=
  MemLp.coeFn_toLp _

/-- Locality identifies the L2 targets even when their cutoffs and their
bounds were chosen at different scales. -/
theorem radialPairingLp_congr (s : Set X) (q a q' a' : SobolevSpace μ hQ) {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ a a x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ a' a' x ≤ B')
    (h : localGamma μ hQ q a =ᵐ[μ.restrict s] localGamma μ hQ q' a') :
    radialPairingLp μ hQ s q a ha = radialPairingLp μ hQ s q' a' ha' := by
  apply Lp.ext
  exact (radialPairingLp_representative μ hQ s q a ha).trans
    (h.trans (radialPairingLp_representative μ hQ s q' a' ha').symm)

/-- Restriction agrees with construction on the smaller testing region. -/
theorem radialPairingLp_restrict {s t : Set X} (hst : t ⊆ s)
    (q a : SobolevSpace μ hQ) {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ a a x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict t, localGamma μ hQ a a x ≤ B') :
    localL2Restriction μ s t hst (radialPairingLp μ hQ s q a ha) =
      radialPairingLp μ hQ t q a ha' := by
  apply Lp.ext
  filter_upwards [localL2Restriction_coe μ s t hst (radialPairingLp μ hQ s q a ha),
    ae_restrict_of_ae_restrict_of_subset hst (radialPairingLp_representative μ hQ s q a ha),
    radialPairingLp_representative μ hQ t q a ha'] with x h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

omit [BorelSpace X] [ProperSpace X] in
/-- Every invertible normalizing frame gives the SAME least-squares residual. -/
theorem affineResidual_transformed {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hfin : μ s ≠ ∞) (A : Euclidean n ≃L[ℝ] Euclidean n) :
    affineResidual μ hQ (transformedColumn μ hQ u A) s hfin =
      affineResidual μ hQ u s hfin := by
  apply affineResidual_eq_of_change μ hQ u _ s hfin A 0
  intro v
  rw [sobolevColumnMap_transformed]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    zero_apply, zero_smul, add_zero]

/-- Applying the inverse normalizing frame to a covector recovers its
original raw radial pairing in the local L2 space. -/
theorem radialPairingLp_frame {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (q : SobolevSpace μ hQ) (A : Euclidean n ≃L[ℝ] Euclidean n)
    (b : Euclidean n) {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict s,
      localGamma μ hQ (sobolevColumnMap μ hQ (transformedColumn μ hQ u A) (A.symm b))
        (sobolevColumnMap μ hQ (transformedColumn μ hQ u A) (A.symm b)) x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict s,
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ B') :
    radialPairingLp μ hQ s q (sobolevColumnMap μ hQ (transformedColumn μ hQ u A) (A.symm b)) ha =
      radialPairingLp μ hQ s q (sobolevColumnMap μ hQ u b) ha' := by
  apply radialPairingLp_congr
  rw [sobolevColumnMap_transformed]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The dimensionless least-squares error of the actual radial derivative. -/
def radialFitError {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) (r : ℝ) (hfin : μ (Metric.ball p r) ≠ ∞)
    (q a : SobolevSpace μ hQ) {B : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (Metric.ball p r), localGamma μ hQ a a x ≤ B) : ℝ :=
  ‖normalizeLocalL2 μ (Metric.ball p r) hfin
    (affineResidual μ hQ u (Metric.ball p r) hfin
      (radialPairingLp μ hQ (Metric.ball p r) q a ha))‖ / r

theorem radialFitError_nonneg {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) {r : ℝ} (hr : 0 ≤ r) (hfin : μ (Metric.ball p r) ≠ ∞)
    (q a : SobolevSpace μ hQ) {B : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (Metric.ball p r), localGamma μ hQ a a x ≤ B) :
    0 ≤ radialFitError μ hQ u p r hfin q a ha := div_nonneg (norm_nonneg _) hr

/-- Cutoff changes preserve the dimensionless fit whenever locality
identifies their actual radial derivatives on the testing ball. -/
theorem radialFitError_congr {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) (r : ℝ) (hfin : μ (Metric.ball p r) ≠ ∞)
    (q a q' a' : SobolevSpace μ hQ) {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (Metric.ball p r), localGamma μ hQ a a x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict (Metric.ball p r), localGamma μ hQ a' a' x ≤ B')
    (h : localGamma μ hQ q a =ᵐ[μ.restrict (Metric.ball p r)] localGamma μ hQ q' a') :
    radialFitError μ hQ u p r hfin q a ha = radialFitError μ hQ u p r hfin q' a' ha' := by
  unfold radialFitError
  rw [radialPairingLp_congr μ hQ _ q a q' a' ha ha' h]

theorem radialFitError_radius_eq {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) {r t : ℝ} (hrt : r = t)
    (hr : μ (Metric.ball p r) ≠ ∞) (ht : μ (Metric.ball p t) ≠ ∞)
    (q a : SobolevSpace μ hQ) {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (Metric.ball p r), localGamma μ hQ a a x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict (Metric.ball p t), localGamma μ hQ a a x ≤ B') :
    radialFitError μ hQ u p r hr q a ha = radialFitError μ hQ u p t ht q a ha' := by
  subst t
  apply radialFitError_congr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The same numerical fit is obtained in every invertible normalizing frame. -/
theorem radialFitError_frame {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) (r : ℝ) (hfin : μ (Metric.ball p r) ≠ ∞)
    (q : SobolevSpace μ hQ) (A : Euclidean n ≃L[ℝ] Euclidean n) (b : Euclidean n) {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (Metric.ball p r),
      localGamma μ hQ (sobolevColumnMap μ hQ (transformedColumn μ hQ u A) (A.symm b))
        (sobolevColumnMap μ hQ (transformedColumn μ hQ u A) (A.symm b)) x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict (Metric.ball p r),
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ B') :
    radialFitError μ hQ (transformedColumn μ hQ u A) p r hfin q
      (sobolevColumnMap μ hQ (transformedColumn μ hQ u A) (A.symm b)) ha =
    radialFitError μ hQ u p r hfin q (sobolevColumnMap μ hQ u b) ha' := by
  unfold radialFitError
  rw [affineResidual_transformed μ hQ u _ hfin A,
    radialPairingLp_frame μ hQ u _ q A b ha ha']

omit [ProperSpace X] in
/-- Harmonic affine improvement is a property of the affine span, so the
same improvement applies after every invertible normalization. -/
theorem HasNormalizedAffineImprovement.transformed {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X)
    {u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic} {p : X} {r θ : ℝ}
    (hfit : HasNormalizedAffineImprovement hX u p r θ)
    (A : Euclidean n ≃L[ℝ] Euclidean n) :
    HasNormalizedAffineImprovement hX (transformedColumn (hausdorff n X) hX.quadratic u A) p r θ := by
  intro w hw hn
  have h := hfit w hw hn
  rw [affineResidual_transformed (hausdorff n X) hX.quadratic u _
    (ne_of_lt (hX.finiteOnBounded _ Metric.isBounded_ball)) A]
  exact h

end RegularPointCoordinates

end

end OAI
