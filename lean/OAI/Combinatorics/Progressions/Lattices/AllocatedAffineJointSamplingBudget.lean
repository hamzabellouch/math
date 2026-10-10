import OAI.Combinatorics.Progressions.Dynamics.AllocatedFiniteIdealMaskBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedProjectedAmbientLogBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_affineAmbientUniformSamplingThreshold_bound (K : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {base D p : ℝ} {outputs dim : ℕ},
      0 ≤ base → 0 ≤ D → 0 ≤ p →
      (outputs : ℝ) ≤ D → (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      (ambientL1SamplingBudget (affineAmbientPrimitiveBudget base (idealSiteLogBudget outputs dim p)) + K) ^ K ≤
        (base + D + p + A) ^ A := by
  let poly : Polynomial ℕ :=
    (ambientL1SamplingBudget (affineAmbientPrimitiveBudget Polynomial.X
      (allocatedFiniteIdealProfileLog Polynomial.X Polynomial.X)) + Polynomial.C K) ^ K
  obtain ⟨A, hA, ha⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro base D p outputs dim hbase hD hp hout hdim hprof
  let R := base + D + p
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbR : base ≤ R := by dsimp [R]; linarith
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hQ : 0 ≤ idealSiteLogBudget outputs dim p := (idealSiteLogBudget_bounds _ _ hp).1
  have hQR : idealSiteLogBudget outputs dim p ≤ allocatedFiniteIdealProfileLog R R := by
    apply (idealSiteLogBudget_le_finite_profile hp hout hdim hprof).trans
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hprofR : 0 ≤ allocatedFiniteIdealProfileLog R R := by
    unfold allocatedFiniteIdealProfileLog
    positivity
  have hmono :
      (ambientL1SamplingBudget (affineAmbientPrimitiveBudget base (idealSiteLogBudget outputs dim p)) + K) ^ K ≤
        (ambientL1SamplingBudget (affineAmbientPrimitiveBudget R (allocatedFiniteIdealProfileLog R R)) + K) ^ K := by
    dsimp only [ambientL1SamplingBudget, ambientL1FourierInput, affineAmbientPrimitiveBudget, affineAmbientMassLog]
    gcongr
  apply hmono.trans
  simpa [poly, ambientL1SamplingBudget, ambientL1FourierInput, affineAmbientPrimitiveBudget,
    affineAmbientMassLog, allocatedFiniteIdealProfileLog, Polynomial.eval₂_pow] using ha R hR

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def affineJointSamplingInput {A : Type*} [Semiring A] (b : ℕ)
    (actual base idealQ geometry : A) : A :=
  (actual + (b : A)) ^ b + affineAmbientPrimitiveBudget base idealQ + geometry

theorem exists_allocatedAffineJointSamplingThreshold_bound (m dim Aproj K : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {actual base D p geometry : ℝ} {outputs : ℕ},
      0 ≤ actual → 0 ≤ base → 0 ≤ D → 0 ≤ p → 0 ≤ geometry →
      (outputs : ℝ) ≤ D → (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      (ambientL1SamplingBudget (allocatedProjectedAmbientLog m dim Aproj actual +
        affineAmbientPrimitiveBudget base (idealSiteLogBudget outputs dim p) + geometry) + K) ^ K ≤
        (actual + base + D + p + geometry + A) ^ A := by
  obtain ⟨b, hb, hactual⟩ := exists_allocatedProjectedAmbientLog_bound m dim Aproj
  let X : Polynomial ℕ := Polynomial.X
  let poly : Polynomial ℕ :=
    (ambientL1SamplingBudget (affineJointSamplingInput b X X
      (allocatedFiniteIdealProfileLog X X) X) + Polynomial.C K) ^ K
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro actual base D p geometry outputs ha hbase hD hp hg hout hdim hprofile
  let R := actual + base + D + p + geometry
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have haR : actual ≤ R := by dsimp [R]; linarith
  have hbR : base ≤ R := by dsimp [R]; linarith
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hgR : geometry ≤ R := by dsimp [R]; linarith
  have hQ : 0 ≤ idealSiteLogBudget outputs dim p := (idealSiteLogBudget_bounds _ _ hp).1
  have hprofR : 0 ≤ allocatedFiniteIdealProfileLog R R := by
    unfold allocatedFiniteIdealProfileLog
    positivity
  have hQR : idealSiteLogBudget outputs dim p ≤ allocatedFiniteIdealProfileLog R R := by
    apply (idealSiteLogBudget_le_finite_profile hp hout hdim hprofile).trans
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hap : allocatedProjectedAmbientLog m dim Aproj actual ≤ (R + b) ^ b :=
    (hactual actual ha).trans (pow_le_pow_left₀ (by positivity) (by linarith) b)
  have ha0 : 0 ≤ allocatedProjectedAmbientLog m dim Aproj actual := by
    have h := allocatedAmbientLog_nonneg m ha
    unfold allocatedProjectedAmbientLog
    positivity
  have hmono :
      (ambientL1SamplingBudget (allocatedProjectedAmbientLog m dim Aproj actual +
        affineAmbientPrimitiveBudget base (idealSiteLogBudget outputs dim p) + geometry) + K) ^ K ≤
      (ambientL1SamplingBudget (affineJointSamplingInput b R R (allocatedFiniteIdealProfileLog R R) R) + K) ^ K := by
    dsimp only [affineJointSamplingInput, ambientL1SamplingBudget, ambientL1FourierInput,
      affineAmbientPrimitiveBudget, affineAmbientMassLog]
    gcongr
  apply hmono.trans
  simpa [poly, X, affineJointSamplingInput, ambientL1SamplingBudget, ambientL1FourierInput,
    affineAmbientPrimitiveBudget, affineAmbientMassLog, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI
