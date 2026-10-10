import OAI.Probability.InvariantIsing.Arrays.NSpinTensorCascade
import OAI.Probability.InvariantIsing.Arrays.NSpinFactorization
import OAI.Probability.InvariantIsing.Arrays.TensorProfiles

namespace OAI

/-!
# Removing zero-amplitude tensor marks

Projection onto the site coordinates sends the tensor Gaussian product law
to the original site-field law.  This identifies the actual zero-amplitude
cascade pressure with the unperturbed rotated enriched pressure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorSiteProjection {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (z : SpinTensorIndex I degree → ℝ) : Fin N → ℝ :=
  fun i => z (Sum.inl i)

lemma tensorSiteProjection_add {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (z w : SpinTensorIndex I degree → ℝ) :
    tensorSiteProjection I degree (z + w) =
      tensorSiteProjection I degree z + tensorSiteProjection I degree w := rfl

lemma tensorSiteProjection_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) (site : ℝ≥0)
    (hv : ∀ i, v (Sum.inl i) = site) :
    MeasurePreserving (tensorSiteProjection I degree)
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ))
      (vectorGaussianLaw N site : Measure (Fin N → ℝ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i))
  have hfst := measurePreserving_fst
    (μ := Measure.pi (fun i : Fin N => gaussianReal 0 (v (Sum.inl i))))
    (ν := Measure.pi (fun j : Sigma (fun j : Fin k => SpectralTensorIndex I (degree j)) =>
      gaussianReal 0 (v (Sum.inr j))))
  have h := hfst.comp hsplit
  change MeasurePreserving (tensorSiteProjection I degree)
    (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i : Fin N => gaussianReal 0 site))
  change MeasurePreserving (tensorSiteProjection I degree)
    (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i : Fin N => gaussianReal 0 (v (Sum.inl i)))) at h
  simpa only [hv] using h

lemma spinTensorEnergy_zero_amplitude {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (z : SpinTensorIndex I degree → ℝ) (σ : Spin N) :
    spinTensorEnergy U I degree (fun _ => 0) z σ =
      fieldEnergy (tensorSiteProjection I degree z) σ := by
  classical
  simp only [spinTensorEnergy, Fintype.sum_sum_type, spinTensorFeature, zero_mul,
    mul_zero, Finset.sum_const_zero, add_zero, tensorSiteProjection, fieldEnergy]

lemma spinTensorTerminal_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (z : SpinTensorIndex I degree → ℝ) :
    spinTensorTerminal eig U c I degree (fun _ => 0) z =
      rotatedFieldTerminal eig U c (tensorSiteProjection I degree z) := by
  unfold spinTensorTerminal rotatedFieldTerminal
  congr 1
  funext σ
  rw [spinTensorEnergy_zero_amplitude]
  simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- Zero-amplitude tensor coordinates disappear at every Gaussian recursion
step, irrespective of their unused variances. -/
theorem tensorCascadeValue_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (site : ℕ → ℝ≥0) (hv : ∀ j i, v j (Sum.inl i) = site j)
    (z : SpinTensorIndex I degree → ℝ) :
    tensorCascadeValue eig U c I degree (fun _ => 0) n b v z =
      rotatedCascadeValue n b site eig U c (tensorSiteProjection I degree z) := by
  induction n generalizing b v site z with
  | zero => exact spinTensorTerminal_zero_amplitude eig U c I degree z
  | succ n ih =>
    let F := rotatedCascadeValue n (fun j => b (j + 1)) (fun j => site (j + 1)) eig U c
    have hF : Measurable F :=
      measurable_cascadeRecursion n (fun j => b (j + 1))
        (fun j => vectorGaussianLaw N (site (j + 1)))
        (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
    have hE : Measurable (fun w : Fin N → ℝ =>
        Real.exp (b 0 * F (tensorSiteProjection I degree z + w))) :=
      ((hF.comp (measurable_const.add measurable_id)).const_mul (b 0)).exp
    have hm := tensorSiteProjection_measurePreserving I degree (v 0) (site 0) (hv 0)
    change logMean (b 0) (tensorGaussianLaw I degree (v 0) : Measure _)
        (fun w => tensorCascadeValue eig U c I degree (fun _ => 0) n
          (fun j => b (j + 1)) (fun j => v (j + 1)) (z + w)) =
      logMean (b 0) (vectorGaussianLaw N (site 0) : Measure _)
        (fun w => F (tensorSiteProjection I degree z + w))
    unfold logMean
    congr 1
    congr 1
    calc
      _ = ∫ w : SpinTensorIndex I degree → ℝ,
          Real.exp (b 0 * F (tensorSiteProjection I degree z + tensorSiteProjection I degree w))
          ∂(tensorGaussianLaw I degree (v 0) : Measure _) := by
        apply integral_congr_ae
        refine ae_of_all _ fun w => ?_
        dsimp only
        rw [ih (fun j => b (j + 1)) (fun j => v (j + 1))
          (fun j => site (j + 1)) (fun j i => hv (j + 1) i)]
        rfl
      _ = _ := hm.hasLaw.integral_comp hE.aestronglyMeasurable

/-- The exact unperturbed enriched-pressure identity used at temperature zero. -/
theorem tensorEnrichedPressure_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (site : ℕ → ℝ≥0) (hv : ∀ j i, v j (Sum.inl i) = site j)
    (root : SpinTensorIndex I degree → ℝ≥0) (rootSite : ℝ≥0)
    (hroot : ∀ i, root (Sum.inl i) = rootSite) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b v root =
      rotatedEnrichedPressure n b site rootSite eig U c := by
  unfold tensorEnrichedPressure rotatedEnrichedPressure
  congr 1
  have hF : Measurable (rotatedCascadeValue n b site eig U c) :=
    measurable_cascadeRecursion n b (fun j => vectorGaussianLaw N (site j))
      (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
  calc
    _ = ∫ z : SpinTensorIndex I degree → ℝ,
        rotatedCascadeValue n b site eig U c (tensorSiteProjection I degree z)
        ∂(tensorGaussianLaw I degree root : Measure _) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => tensorCascadeValue_zero_amplitude eig U c I degree n b v site hv z
    _ = _ := (tensorSiteProjection_measurePreserving I degree root rootSite hroot).hasLaw.integral_comp
      hF.aestronglyMeasurable

/-- The manuscript profile retains precisely the original linear-field
increments when the monomial amplitudes vanish. -/
theorem tensorPathPressure_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0) =
    rotatedEnrichedPressure n b (fun i => varianceIncrement h (i + 1))
      (varianceIncrement h 0) eig U c :=
  tensorEnrichedPressure_zero_amplitude eig U c I degree n b _ _
    (fun _ _ => rfl) _ _ (fun _ => rfl)

lemma varianceIncrement_heightSequence (h : FieldStep) (i : ℕ) :
    varianceIncrement (heightSequence h) (i + 1) = fieldCascadeVariance h i := by
  apply NNReal.eq
  rw [varianceIncrement_coe (heightSequence_mono h) (heightSequence_nonneg h 0)]
  exact (pathAmplitude_sq (heightSequence_mono h) (heightSequence_nonneg h 0) (i + 1)).symm

lemma varianceIncrement_heightSequence_zero (h : FieldStep) :
    varianceIncrement (heightSequence h) 0 = NNReal.mk (h.height 0) (h.nonneg 0) := by
  apply NNReal.eq
  rw [varianceIncrement_coe (heightSequence_mono h) (heightSequence_nonneg h 0)]
  simp only [pathIncrement, heightSequence, Nat.zero_min]
  change h.height ⟨0, _⟩ = h.height 0
  congr 1

/-- The exact zero-temperature base value in the tensor model, with all
unused monomial variances still present. -/
theorem tensorPathPressure_field_zero_time {N m k : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (treeDegree : Fin k → ℕ) (h : FieldStep) :
    tensorEnrichedPressure (fun _ => 0) U (fun _ => 0) I degree (fun _ => 0)
      h.depth (chainExponent h.cut)
      (fun i => tensorPathProfile I degree h.depth treeDegree (heightSequence h) (i + 1))
      (tensorPathProfile I degree h.depth treeDegree (heightSequence h) 0) -
      h.height (Fin.last h.depth) / 2 = fieldValue h 0 := by
  rw [tensorPathPressure_zero_amplitude, varianceIncrement_heightSequence_zero]
  simp_rw [varianceIncrement_heightSequence]
  exact rotatedEnrichedPressure_field_zero_time hN h U

/-- The zero-temperature contact objective for the actual zero-amplitude
tensor model is nonnegative. -/
theorem tensorPathPressure_zero_time_contact_nonneg {N m k : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (treeDegree : Fin k → ℕ) (h : FieldStep) (p : OverlapPath) {S : ℝ}
    (hS : entropyFunctional p ≤ (S : EReal)) :
    0 ≤ -(tensorEnrichedPressure (fun _ => 0) U (fun _ => 0) I degree (fun _ => 0)
      h.depth (chainExponent h.cut)
      (fun i => tensorPathProfile I degree h.depth treeDegree (heightSequence h) (i + 1))
      (tensorPathProfile I degree h.depth treeDegree (heightSequence h) 0) -
      h.height (Fin.last h.depth) / 2) - fieldPairing p h / 2 + S := by
  rw [tensorPathPressure_zero_amplitude, varianceIncrement_heightSequence_zero]
  simp_rw [varianceIncrement_heightSequence]
  exact zero_time_contact_nonneg hN h U p hS

end InvariantIsing

end

end OAI
