import OAI.Probability.InvariantIsing.Fields.SpinFiniteCoverMean

namespace OAI

/-! Normalization of the finite-cover error and its dimension limit. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma normalized_spinCover_error {N : ℕ} (hN : 0<N) (d Q : ℕ) (K C t : ℝ) :
    (N:ℝ)⁻¹*(Real.log Q+2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+Real.log (1+Real.exp (-t)) =
      Real.log Q/(N:ℝ)+2*K*Real.sqrt ((d:ℝ)/N)+(2*C+t)*((d:ℝ)/N)+Real.log (1+Real.exp (-t)) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have he : (N:ℝ)*d=(N:ℝ)^2*((d:ℝ)/N) := by field_simp
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hnp]
  field_simp
  ring

lemma spinCover_error_tendsto (N d : ℕ → ℕ) (hN : ∀ k, 0<N k)
    (hNlim : Tendsto N atTop atTop) (Q : ℕ) (B K C t δ : ℝ)
    (hd : Tendsto (fun k => (d k:ℝ)/(N k:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun k => Q*Real.sqrt (B*K^2/(N k:ℝ))+
      (N k:ℝ)⁻¹*(Real.log Q+2*K*Real.sqrt ((N k:ℝ)*d k)+2*C*d k+t*d k)+
        Real.log (1+Real.exp (-t))) atTop
      (𝓝 (2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t)))) := by
  have hn : Tendsto (fun k => (N k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hNlim
  have hsq : Tendsto (fun k => Q*Real.sqrt (B*K^2/(N k:ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp (tendsto_const_nhds.div_atTop hn)).const_mul (Q:ℝ)
  have hlog : Tendsto (fun k => Real.log Q/(N k:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have he := ((hsq.add hlog).add ((Real.continuous_sqrt.tendsto δ |>.comp hd).const_mul (2*K))).add
    (hd.const_mul (2*C+t))
  have hh := he.add_const (Real.log (1+Real.exp (-t)))
  simp only [zero_add] at hh
  convert hh using 1
  ext k
  dsimp only [Function.comp_apply]
  linarith [normalized_spinCover_error (hN k) (d k) Q K C t]

end InvariantIsing

end

end OAI
