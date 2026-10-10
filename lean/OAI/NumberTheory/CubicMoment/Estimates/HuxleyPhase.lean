import OAI.NumberTheory.CubicMoment.Estimates.PublishedAdditiveSieve

namespace OAI

/-! The additive sieve phase as the standard Fourier character of the trace lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma huxleyPhase_eq_traceFourierChar (q h n : Eisenstein) :
    huxleyPhase q h n = (Real.fourierChar
      (tracePair (n:ℂ) ((h:ℂ)/(traceLambda*(q:ℂ)))):ℂ) := by
  unfold huxleyPhase tracePair
  rw [Real.fourierChar_apply]
  have he : (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ)) =
      (n:ℂ)*((h:ℂ)/(traceLambda*(q:ℂ))) := by ring
  rw [he]
  have hc (z : ℂ) : z+star z = ((2*z.re:ℝ):ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  dsimp only
  rw [hc]
  push_cast
  congr 1
  ring

lemma trace_lattice_integer (n h : Eisenstein) :
    ∃ k : ℤ, tracePair (n:ℂ) ((h:ℂ)/traceLambda) = (k:ℝ) := by
  obtain ⟨v,rfl⟩ := coordinatesEquiv.surjective n
  obtain ⟨w,hw⟩ := (dualIntegerEquiv.trans coordinatesEquiv).surjective h
  change coordinatesEquiv (dualIntegerEquiv w) = h at hw
  rw [← hw,← dualRealCoords_integer,coordinatesEquiv_coe,dualRealCoords_trace]
  exact ⟨∑ i, v i*w i,by push_cast; rfl⟩

lemma fourierChar_trace_lattice (n h : Eisenstein) :
    (Real.fourierChar (tracePair (n:ℂ) ((h:ℂ)/traceLambda)):ℂ) = 1 := by
  obtain ⟨k,hk⟩ := trace_lattice_integer n h
  rw [hk,Real.fourierChar_apply]
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  push_cast
  ring_nf

def huxleyFrequencyPhase (x : ℂ) (n : Eisenstein) : ℂ :=
  Real.fourierChar (tracePair (n:ℂ) (x/traceLambda))

lemma huxleyPhase_eq_frequency (q h n : Eisenstein) :
    huxleyPhase q h n = huxleyFrequencyPhase ((h:ℂ)/(q:ℂ)) n := by
  rw [huxleyPhase_eq_traceFourierChar]
  unfold huxleyFrequencyPhase
  rw [show (h:ℂ)/(traceLambda*(q:ℂ)) = ((h:ℂ)/(q:ℂ))/traceLambda by ring]

lemma huxleyFrequencyPhase_add_lattice (x : ℂ) (z n : Eisenstein) :
    huxleyFrequencyPhase (x+(z:ℂ)) n = huxleyFrequencyPhase x n := by
  have he : tracePair (n:ℂ) ((x+(z:ℂ))/traceLambda) =
      tracePair (n:ℂ) (x/traceLambda)+tracePair (n:ℂ) ((z:ℂ)/traceLambda) := by
    simp only [tracePair,add_div,mul_add,Complex.add_re]
  unfold huxleyFrequencyPhase
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul,fourierChar_trace_lattice,mul_one]

end CubicFirstMoment

end

end OAI
