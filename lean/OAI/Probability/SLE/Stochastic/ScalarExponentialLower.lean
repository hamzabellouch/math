import Mathlib

namespace OAI

/-! A lower exponential comparison for the positive forward height. -/
noncomputable section
open Set

namespace SLEExactGauge

lemma scalar_exponential_lower {a b C : ℝ} (y y' : ℝ → ℝ)
    (hc : ContinuousOn y (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt y (y' t) (Ici t) t)
    (hb : ∀ t ∈ Ico a b, -C*y t ≤ y' t) :
    ∀ t ∈ Icc a b, y a * Real.exp (-C*(t-a)) ≤ y t := by
  let f (t : ℝ) := -(y t*Real.exp (C*(t-a)))
  have hfc : ContinuousOn f (Icc a b) :=
    (hc.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn).neg
  have hfd (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt f
      (-(y' t+C*y t)*Real.exp (C*(t-a))) (Ici t) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (C*(s-a)))
        (C*Real.exp (C*(t-a))) t := by
      convert! (((hasDerivAt_id t).sub_const a).const_mul C).exp using 1
      simp only [id_eq]
      ring
    convert! ((hd t ht).mul he.hasDerivWithinAt).neg using 1
    ring
  have he := image_le_of_deriv_right_le_deriv_boundary hfc hfd
    (B := fun _ => -y a) (B' := fun _ => 0)
    (by simp [f]) continuousOn_const
    (fun t _ => hasDerivWithinAt_const t (Ici t) (-y a))
    (fun t ht => mul_nonpos_of_nonpos_of_nonneg (by linarith [hb t ht]) (Real.exp_pos _).le)
  intro t ht
  have h := he ht
  change -(y t*Real.exp (C*(t-a))) ≤ -y a at h
  have hh : y a ≤ y t*Real.exp (C*(t-a)) := by linarith
  have hdv := (div_le_iff₀ (Real.exp_pos (C*(t-a)))).mpr hh
  simpa only [div_eq_mul_inv,← Real.exp_neg,neg_mul] using hdv

end SLEExactGauge

end

end OAI
