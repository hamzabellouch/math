import OAI.Probability.SLE.Loewner.MappedFutureArc

namespace OAI

/-! The future chart does not identify distinct points of the prescribed
arc, including its newly filled real endpoint. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma mappedFutureArc_of_ne_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {u : unitInterval} (hu : u≠0) :
    mappedFutureArc p hi h0 hH hst ht u=mappedFutureRaw p hi h0 hH s t u := by
  have hc : (u:ℝ)≠0 := ne_of_gt (unitInterval.pos_iff_ne_zero.mpr hu)
  exact ite_eq_right hc

theorem mappedFutureArc_injective (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    Injective (mappedFutureArc p hi h0 hH hst ht) := by
  intro u v he
  by_cases hu : u=0
  · subst u
    by_contra hv
    have hpos := mappedFutureArc_upper p hi h0 hH hst ht (Ne.symm hv)
    rw [← he,mappedFutureArc_zero] at hpos
    change 0<(_ : ℂ).im at hpos
    simp only [ofReal_im,lt_self_iff_false] at hpos
  by_cases hv : v=0
  · subst v
    have hpos := mappedFutureArc_upper p hi h0 hH hst ht hu
    rw [he,mappedFutureArc_zero] at hpos
    change 0<(_ : ℂ).im at hpos
    simp only [ofReal_im,lt_self_iff_false] at hpos
  have hur : (u:ℝ)∈Ioc (0:ℝ) 1 := ⟨unitInterval.pos_iff_ne_zero.mpr hu,u.property.2⟩
  have hvr : (v:ℝ)∈Ioc (0:ℝ) 1 := ⟨unitInterval.pos_iff_ne_zero.mpr hv,v.property.2⟩
  have huD := slitFuturePoint_mem_domain p hi hH s (future_scaled_offset hst ht hur)
  have hvD := slitFuturePoint_mem_domain p hi hH s (future_scaled_offset hst ht hvr)
  rw [mappedFutureArc_of_ne_zero p hi h0 hH hst ht hu,
    mappedFutureArc_of_ne_zero p hi h0 hH hst ht hv] at he
  have hp := congrArg (initialInverseChart p hi h0 hH s) he
  change initialInverseChart p hi h0 hH s (initialForwardChart p hi h0 hH s _) =
    initialInverseChart p hi h0 hH s (initialForwardChart p hi h0 hH s _) at hp
  rw [initialInverse_forward_at p hi h0 hH s huD,
    initialInverse_forward_at p hi h0 hH s hvD] at hp
  have hparam := congrArg (fun a : unitInterval => (a:ℝ)) (hi hp)
  rw [slitFutureParameter_coe s (future_scaled_offset hst ht hur),
    slitFutureParameter_coe s (future_scaled_offset hst ht hvr)] at hparam
  apply Subtype.ext
  have hd : (t:ℝ)-(s:ℝ)≠0 := ne_of_gt (sub_pos.mpr (show (s:ℝ)<(t:ℝ) from hst))
  exact mul_left_cancel₀ hd (add_left_cancel hparam)

end SLEExactGauge

end

end OAI
