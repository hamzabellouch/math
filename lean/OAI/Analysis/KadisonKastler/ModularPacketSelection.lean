import OAI.Analysis.KadisonKastler.ModularPacketCoefficient
import OAI.Analysis.KadisonKastler.ShortFrequencyScalar
import OAI.Analysis.KadisonKastler.VectorStateWitness

namespace OAI

/-! # A short spectral interval retaining a strict state inequality

Strong invariance and the packet norm identity allow one Fourier fiber to
retain any strict self-adjoint test. This is the local separation step toward
the required approximate-eigenstate decomposition, without a disintegration
hypothesis or an assumed measure on states.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_packet_fiber_gt
    (F : RegularCoreHilbert H) (hF : ‖F‖=1) (T : H →L[ℂ] H) {c : ℝ}
    (hc : c < ∫ s : ℝ, (inner ℂ (F s) (T (F s))).re)
    (P : ℝ → Prop) (hP : ∀ᵐ s : ℝ, P s) :
    ∃ s : ℝ, P s ∧ c*‖F s‖^2 < (inner ℂ (F s) (T (F s))).re := by
  by_contra hn
  push Not at hn
  have hle : ∀ᵐ s : ℝ, (inner ℂ (F s) (T (F s))).re ≤ c*‖F s‖^2 :=
    hP.mono fun s hs => hn s hs
  have hi := (integrable_regular_vector_coefficient F T).re
  have hj := ((Lp.memLp F).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul c
  have h := integral_mono_ae hi hj hle
  rw [integral_const_mul,regular_integral_norm_sq,hF,one_pow,mul_one] at h
  exact (not_le_of_gt hc) h

variable {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem exists_packet_localized_vector_gt
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (a b : ℝ)
    (hlo : regularFrequencyProjection a φ=φ) (hhi : regularFrequencyProjection b φ=0) :
    ∃ (s : ℝ) (ξ : H), ξ ≠ 0 ∧
      S.upperCut (a-2*Real.pi*s) ξ=ξ ∧ S.upperCut (b-2*Real.pi*s) ξ=0 ∧
      c*‖ξ‖^2 < (inner ℂ ξ (T ξ)).re := by
  have hvalue : c < (ψ (scalarPacketAverage S.group S.continuous φ hφ T)).re := by
    rwa [scalarPacketAverage_strongly_invariant S.group S.continuous ψ hinv]
  obtain ⟨η,hη,hηT⟩ := exists_vector_state_gt ψ hψ _
    (scalarPacketAverage_selfAdjoint S.group S.continuous φ hφ T hT) hvalue
  have hnorm : ‖S.fourierPacket φ η‖=1 := by rw [S.norm_fourierPacket,hφ,hη,one_mul]
  have hint : c < ∫ s : ℝ,
      (inner ℂ (S.fourierPacket φ η s) (T (S.fourierPacket φ η s))).re := by
    rwa [S.fourierPacket_coefficient_re φ hφ]
  have hsupport := (S.fourierPacket_lower_support a φ hlo η).and
    (S.fourierPacket_upper_support b φ hhi η)
  obtain ⟨s,hs,hgt⟩ := exists_packet_fiber_gt _ hnorm T hint _ hsupport
  refine ⟨s,S.fourierPacket φ η s,?_,hs.1,hs.2,hgt⟩
  intro hz
  simp only [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,
    map_zero,inner_zero_left,Complex.zero_re,lt_self_iff_false] at hgt

theorem exists_short_spectral_vector_gt
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (ξ : H), ξ ≠ 0 ∧ S.upperCut r ξ=ξ ∧ S.upperCut (r+δ) ξ=0 ∧
      c*‖ξ‖^2 < (inner ℂ ξ (T ξ)).re := by
  obtain ⟨φ,hφ,hlo,hhi⟩ := exists_short_frequency_scalar hδ
  obtain ⟨s,ξ,hξ,hl,hh,hgt⟩ := S.exists_packet_localized_vector_gt ψ hψ hinv T hT hc φ hφ 0 δ hlo hhi
  refine ⟨-2*Real.pi*s,ξ,hξ,?_,?_,hgt⟩
  · simpa only [zero_sub, neg_mul] using hl
  · simpa only [sub_eq_add_neg, neg_mul, add_comm] using hh

end ModularSpectralResolution

end

end KadisonKastler

end OAI
