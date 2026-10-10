import OAI.NumberTheory.JointDickman.Counting.SamplingFamilyRate

namespace OAI

/-! # A vanishing error envelope for the adaptive cut comparison -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def samplingDegreeEnvelope (U q K B : ℝ) : ℝ :=
  (4*U*q/K^2)*(B^(0.11 : ℝ)/B^(0.14 : ℝ))

noncomputable def samplingSquareEnvelope (q B : ℝ) : ℝ :=
  q*(B^(0.20 : ℝ)/B^(0.21 : ℝ))

noncomputable def samplingEntropyEnvelope (c K a B : ℝ) : ℝ :=
  Real.exp (2*(B^(0.14 : ℝ)*Real.log B) - (a^2*c/(8*K^2))*B^(0.18 : ℝ))

noncomputable def samplingRateEnvelope (C q c U K a B : ℝ) : ℝ :=
  2*Real.sqrt (U*(B^(0.12 : ℝ)/B^(0.14 : ℝ))) +
    (4*K/c)*(B^(0.21 : ℝ)/B^(0.32 : ℝ)) +
    Real.sqrt ((C^2+q*B^(-0.21 : ℝ))*(samplingDegreeEnvelope U q K B +
      samplingSquareEnvelope q B + samplingEntropyEnvelope c K a B))

theorem samplingDegreeEnvelope_tendsto (U q K : ℝ) :
    Tendsto (samplingDegreeEnvelope U q K) atTop (𝓝 0) := by
  unfold samplingDegreeEnvelope
  simpa only [mul_zero] using
    (power_div_power_tendsto_zero (a := (0.11 : ℝ)) (b := (0.14 : ℝ))
      (by norm_num)).const_mul (4*U*q/K^2)

theorem samplingSquareEnvelope_tendsto (q : ℝ) :
    Tendsto (samplingSquareEnvelope q) atTop (𝓝 0) := by
  unfold samplingSquareEnvelope
  simpa only [mul_zero] using
    (power_div_power_tendsto_zero (a := (0.20 : ℝ)) (b := (0.21 : ℝ))
      (by norm_num)).const_mul q

theorem samplingRateEnvelope_tendsto (C q U : ℝ) {c K a : ℝ}
    (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    Tendsto (samplingRateEnvelope C q c U K a) atTop (𝓝 0) := by
  unfold samplingRateEnvelope samplingEntropyEnvelope
  have hq : Tendsto (fun B : ℝ => C^2+q*B^(-0.21 : ℝ)) atTop (𝓝 (C^2)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.21)).const_mul q)
  have hp := ((samplingDegreeEnvelope_tendsto U q K).add
    (samplingSquareEnvelope_tendsto q)).add (samplingFamily_envelope_tendsto hc hK ha)
  have hs := (hq.mul hp).sqrt
  simpa only [mul_zero,Real.sqrt_zero,add_zero,samplingEntropyEnvelope] using
    (sampling_error_envelope_tendsto U K c).add hs

theorem sampling_parameters_eventually (C q U L : ℝ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ B : ℝ in atTop, 1 ≤ B ∧ 2*C ≤ K*B^(0.07 : ℝ) ∧
      samplingDegreeEnvelope U q K B < 1 ∧
      Real.sqrt (q*B^(-0.21 : ℝ))+L*samplingDegreeEnvelope U q K B ≤ ε := by
  have hd : Tendsto (fun B : ℝ => K*B^(0.07 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).const_mul_atTop hK
  have hm : Tendsto (fun B : ℝ => Real.sqrt (q*B^(-0.21 : ℝ))+
      L*samplingDegreeEnvelope U q K B) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.21)).const_mul q).sqrt
    simpa using hh.add ((samplingDegreeEnvelope_tendsto U q K).const_mul L)
  filter_upwards [eventually_ge_atTop (1 : ℝ),hd.eventually_ge_atTop (2*C),
    (samplingDegreeEnvelope_tendsto U q K).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hm.eventually (eventually_lt_nhds hε)] with B hB hd hb hm
  exact ⟨hB,hd,hb,hm.le⟩

end JointDickman

end OAI
