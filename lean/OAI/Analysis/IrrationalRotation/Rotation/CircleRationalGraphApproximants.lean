import OAI.Analysis.IrrationalRotation.Sampling.CircleRationalSamplingIndex
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingGraphLimits
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphTrimmingMeasure
import OAI.Analysis.IrrationalRotation.Rotation.CircleRationalGraphTransfer
import OAI.Analysis.IrrationalRotation.Sampling.TrimmedCircleSamplingGraph

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

def rationalSamplingStage (A n : ℕ) : ℕ := n + A + 1

def rationalSamplingLabel (A : ℕ) (r : ℤ) (n : ℕ) : ℕ :=
  Classical.choose (hp.exists_rational_sampling_index_of_late
    (A := A) (j := rationalSamplingStage A n) (by unfold rationalSamplingStage; omega) r)

theorem rationalSamplingStage_pos (A n : ℕ) : 1 ≤ rationalSamplingStage A n := by
  unfold rationalSamplingStage
  omega

theorem rationalSamplingLabel_lt (A : ℕ) (r : ℤ) (n : ℕ) :
    hp.rationalSamplingLabel A r n < p.q (p.blockEnd (rationalSamplingStage A n - 1)) :=
  (Classical.choose_spec (hp.exists_rational_sampling_index_of_late
    (A := A) (j := rationalSamplingStage A n) (by unfold rationalSamplingStage; omega) r)).1

theorem rationalSamplingLabel_shift (A : ℕ) (r : ℤ) (n : ℕ) :
    (p.shift (rationalSamplingStage A n) (hp.rationalSamplingLabel A r n) : Circle) =
      p.rationalTranslation A r :=
  (Classical.choose_spec (hp.exists_rational_sampling_index_of_late
    (A := A) (j := rationalSamplingStage A n) (by unfold rationalSamplingStage; omega) r)).2.symm

theorem rationalSamplingStage_tendsto (A : ℕ) :
    Tendsto (rationalSamplingStage A) atTop atTop := by
  exact tendsto_atTop_mono (fun n => by dsimp [rationalSamplingStage]; omega) tendsto_id

def rationalGraphApproximant (A : ℕ) (r : ℤ) (n : ℕ) : FiniteMeasure (Circle × Circle) :=
  (p.samplingGraphFinite θ (rationalSamplingStage A n) (hp.rationalSamplingLabel A r n)
    (hp.m_pos _ (rationalSamplingStage_pos A n))).restrict
      (Prod.fst ⁻¹' p.rationalGraphGood A (rationalSamplingStage A n))

theorem rationalGraphApproximant_tendsto (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    Tendsto (hp.rationalGraphApproximant A r) atTop
      (𝓝 (circleTranslationGraph (p.rationalTranslation A r))) := by
  have hb : Tendsto (fun n => circleMeasure.real
      (p.rationalGraphGood A (rationalSamplingStage A n))ᶜ) atTop (𝓝 0) := by
    have hshift : Tendsto (fun n : ℕ => n + A) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right n A) tendsto_id
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((hp.tendsto_measure_rationalGraphBad hA).comp hshift)
    simpa only [rationalSamplingStage, rationalGraphBad, Measure.real,
      Function.comp_def, ENNReal.toReal_zero] using h
  have h := hp.tendsto_samplingGraph_translation_trimmed
    (rationalSamplingStage A) (hp.rationalSamplingLabel A r)
    (rationalSamplingStage_pos A) (hp.rationalSamplingLabel_lt A r)
    (rationalSamplingStage_tendsto A) (p.rationalTranslation A r)
    (hp.rationalSamplingLabel_shift A r)
    (fun n => p.rationalGraphGood A (rationalSamplingStage A n))
    (fun n => p.measurableSet_rationalGraphGood A _) hb
  exact h

theorem rationalGraphApproximant_marginals (A : ℕ) (r : ℤ) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (hp.rationalGraphApproximant A r n : Measure (Circle × Circle)).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (hp.rationalGraphApproximant A r n : Measure (Circle × Circle)).map Prod.snd) := by
  obtain ⟨hfirst, hsecond⟩ := hp.samplingGraph_marginals_uniformlyAbsolutelyContinuous
    (rationalSamplingStage A) (hp.rationalSamplingLabel A r)
    (rationalSamplingStage_pos A) (hp.rationalSamplingLabel_lt A r)
  exact ⟨hfirst.map_restrict Prod.fst measurable_fst _,
    hsecond.map_restrict Prod.snd measurable_snd _⟩

theorem rationalGraphApproximant_positive_orbits (A : ℕ) (r : ℤ) (n : ℕ) :
    ∀ᵐ z ∂(hp.rationalGraphApproximant A r n : Measure (Circle × Circle)),
      ∃ k : ℕ, 0 < k ∧ z.2 = CircleWeights.rotate θ (k : ℤ) z.1 := by
  have h := ae_restrict_of_ae (s := Prod.fst ⁻¹'
      p.rationalGraphGood A (rationalSamplingStage A n))
    (hp.samplingGraphAverage_ae_positive_graph (rationalSamplingStage A n)
      (rationalSamplingStage_pos A n) (hp.rationalSamplingLabel A r n)
      (hp.rationalSamplingLabel_lt A r n))
  filter_upwards [h] with z hz
  obtain ⟨k, _, hk, he⟩ := hz
  refine ⟨k, hk, ?_⟩
  simpa only [samplingTranslation, CircleWeights.rotate, natCast_zsmul,
    ← AddCircle.coe_nsmul, nsmul_eq_mul] using he

theorem rationalGraphApproximant_ratio_cap (A : ℕ) (hA : 1 ≤ A) (r : ℤ)
    (n : ℕ) :
    ∀ᵐ z ∂(hp.rationalGraphApproximant A r n : Measure (Circle × Circle)),
      ∀ v : ℤ, p.floorCocycle θ v z.2 / p.floorCocycle θ v z.1 ≤
        p.rationalRatioBound A := by
  have ht : p.q A • ((p.shift (rationalSamplingStage A n)
      (hp.rationalSamplingLabel A r n) : ℝ) : Circle) = 0 := by
    rw [hp.rationalSamplingLabel_shift A r n]
    simpa only [rationalTranslation, Int.cast_natCast, natCast_zsmul] using
      CircleCharacterDynamics.zsmul_rational_eq_zero
        (q := (p.q A : ℤ)) (d := (p.q A : ℤ))
        (by exact_mod_cast (hp.q_pos A).ne') dvd_rfl r
  exact hp.trimmedSamplingGraphAverage_ae_ratio_cap hA
    (rationalSamplingStage_pos A n) (hp.rationalSamplingLabel_lt A r n) ht

include hp

theorem rationalGraphIdentities_of_positive_orbits
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ x, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂circleMeasure,
      (1 - P (CircleWeights.rotate θ (n : ℤ) x)).comp
        ((ratioDiagonal (p.floorCocycle θ)
          (x, CircleWeights.rotate θ (n : ℤ) x)).comp (P x)) = 0) :
    p.RationalGraphIdentities θ P := by
  apply hp.rationalGraphIdentities_of_forall P
  intro A hA r
  apply hp.rational_graph_identity_of_orbit_approximants P hP hPm horbit A hA r
    (hp.rationalGraphApproximant A r) (hp.rationalGraphApproximant_tendsto A hA r)
    (hp.rationalGraphApproximant_marginals A r).1
    (hp.rationalGraphApproximant_marginals A r).2
  · intro n k
    exact (hp.rationalGraphApproximant_ratio_cap A hA r n).mono fun _ h => h k
  · exact hp.rationalGraphApproximant_positive_orbits A r

end Invariant233.CircleParameterLaws

end

end OAI
