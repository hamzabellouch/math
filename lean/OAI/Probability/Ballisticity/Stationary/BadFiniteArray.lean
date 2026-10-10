import Mathlib
import OAI.Probability.Ballisticity.Estimates.BadDropMoment
import OAI.Probability.Ballisticity.Estimates.OperationalLengthMarks
import OAI.Probability.Ballisticity.Renewal.PositiveLengthMark

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma logLengthMark_real {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hf : (Y.1 0).1<⊤) :
    (logLengthMark e Y).toReal = Real.log (1+((Y.1 0).1.toNat:ℝ)) := by
  have he := ENat.natCast_toNat hf.ne
  change (ENNReal.log (1+(Y.1 0).1.toENNReal)).toENNReal.toReal=_
  generalize (Y.1 0).1.toNat=n at he ⊢
  rw [←he,ENat.toENNReal_coe]
  rw [ENNReal.log_pos_real (by positivity) (by finiteness),EReal.real_coe_toENNReal,
    ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.natCast_ne_top n)]
  simp only [ENNReal.toReal_one,ENNReal.toReal_natCast]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg n)))]

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

theorem bad_array_finite_marks (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => C.occupation hef (Ns (φ n))
        ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
      MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
        (ρ : Measure (ActualEpisodeArray e)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p j z,
        Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
        arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
        0<(Y.1 0).1 ∧ (Y.1 0).1<⊤ ∧ (Y.1 0).2.1<⊤ ∧ (Y.1 0).2.2<∞) ∧
      Integrable (fun Y => ((Y.1 0).2.1).toENNReal.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      Integrable (fun Y => Real.log (1+((Y.1 0).1.toNat:ℝ))) (ρ : Measure (ActualEpisodeArray e)) ∧
      Integrable (fun Y => (Y.1 0).2.2.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      C.b ≤ ∫ Y, (Y.1 0).2.2.toReal ∂(ρ : Measure (ActualEpisodeArray e)) := by
  obtain ⟨ρ,φ,hφ,hlim,hstat,hsample,hzero⟩ := C.bad_array_sampling_limit hef hD Ns hNs hN hlarge hmass
  have hJ := C.bad_limit_finite_stages hef hD (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hlarge (φ n)) (fun n => hmass (φ n)) ρ hlim
  have hc := C.bad_limit_drop_moment hef hD (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hlarge (φ n)) (fun n => hmass (φ n)) ρ hlim
  have hh := C.bad_limit_length_moment hef hD (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hlarge (φ n)) (fun n => hmass (φ n)) ρ hlim
  have hpos := C.bad_limit_positive_length hef (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hmass (φ n)) ρ hlim
  refine ⟨ρ,φ,hφ,hlim,hstat,hsample,hzero,?_,hJ.2,?_,hc.2.1,hc.2.2⟩
  · filter_upwards [hpos,hh.1,hJ.1,hc.1] with Y ha hb hj hk
    exact ⟨ha,hb,hj,hk⟩
  · exact hh.2.congr (hh.1.mono (fun Y hY => logLengthMark_real e Y hY))

end OperationalConstants
end DirectionalTransience

end

end OAI
