import OAI.Analysis.KadisonKastler.ModularLogRegularization
import OAI.Analysis.KadisonKastler.TomitaResolventDenseRange

namespace OAI

/-! # Functional calculus for the bounded Tomita resolvent

The weighted scalar estimates apply to the graph resolvent because its
spectrum is contained in `[0,1]`.  All assertions here concern bounded
operators; no unbounded functional calculus is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem graphResolvent_spectrum_bounds (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {s : ℝ} (hs : s ∈ spectrum ℝ (graphResolvent M J Ω 1)) : 0 ≤ s ∧ s ≤ 1 := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    rw [spectrum.of_subsingleton] at hs
    exact False.elim hs
  | inr h =>
    have hp : 0 ≤ graphResolvent M J Ω 1 :=
      ContinuousLinearMap.nonneg_iff_isPositive.mpr (graphResolvent_positive J Ω 1)
    exact ⟨spectrum_nonneg_of_nonneg hp hs,
      (le_abs_self s).trans ((spectrum.norm_le_norm_of_mem hs).trans
      (graphResolvent_norm_le_one J Ω 1))⟩

theorem regularizedLogScalar_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (regularizedLogScalar ε) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  have hm : ContinuousAt (fun r : ℝ => 1 - r + ε) s := by fun_prop
  have hp : ContinuousAt (fun r : ℝ => r + ε) s := by fun_prop
  exact ((Real.continuousAt_log (by linarith)).comp hm).continuousWithinAt.sub
    (((Real.continuousAt_log (by linarith)).comp hp).continuousWithinAt)

theorem regularizedModularLog_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) :
    (regularizedModularLog M J Ω ε).val =
      cfc (regularizedLogScalar ε) (graphResolvent M J Ω 1) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hp : ContinuousOn Real.log ((fun s : ℝ => s + ε) '' spectrum ℝ R) := by
    rintro _ ⟨s, hs, rfl⟩
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact (Real.continuousAt_log (by linarith)).continuousWithinAt
  have hm : ContinuousOn Real.log ((fun s : ℝ => 1 - s + ε) '' spectrum ℝ R) := by
    rintro _ ⟨s, hs, rfl⟩
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact (Real.continuousAt_log (by linarith)).continuousWithinAt
  have hap : cfc (fun s : ℝ => s + ε) R = R + algebraMap ℝ (H →L[ℂ] H) ε := by
    rw [cfc_add_const ε (fun s : ℝ => s) R (by fun_prop) hR, cfc_id' ℝ R hR]
  have ham : cfc (fun s : ℝ => 1 - s + ε) R =
      1 - R + algebraMap ℝ (H →L[ℂ] H) ε := by
    rw [cfc_add_const ε (fun s : ℝ => 1 - s) R (by fun_prop) hR,
      cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) R (by fun_prop) (by fun_prop),
      cfc_const_one ℝ R hR, cfc_id' ℝ R hR]
  have hcp := cfc_comp Real.log (fun s : ℝ => s + ε) R hR hp (by fun_prop)
  have hcm := cfc_comp Real.log (fun s : ℝ => 1 - s + ε) R hR hm (by fun_prop)
  rw [hap] at hcp
  rw [ham] at hcm
  change CFC.log (1 - R + algebraMap ℝ (H →L[ℂ] H) ε) -
    CFC.log (R + algebraMap ℝ (H →L[ℂ] H) ε) = _
  rw [CFC.log, CFC.log, ← hcp, ← hcm]
  symm
  exact cfc_sub _ _ R (hm.comp (by fun_prop) (Set.mapsTo_image _ _))
    (hp.comp (by fun_prop) (Set.mapsTo_image _ _))

theorem graphResolventCutoff_eq_cfc (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    graphResolventCutoff M J Ω =
      cfc (fun s : ℝ => s * (1 - s)) (graphResolvent M J Ω 1) := by
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  rw [cfc_mul (fun s : ℝ => s) (fun s : ℝ => 1 - s) _ (by fun_prop) (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) _ (by fun_prop) (by fun_prop),
    cfc_id' ℝ _ hR, cfc_const_one ℝ _ hR]
  rfl

/-- Endpoint weighting turns the logarithmic difference into a norm estimate. -/
theorem regularizedModularLog_weighted_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ‖((regularizedModularLog M J Ω ε).val - (regularizedModularLog M J Ω δ).val) *
      graphResolventCutoff M J Ω‖ ≤ |ε - δ| := by
  have he := regularizedLogScalar_continuousOn (M := M) J Ω hε
  have hd := regularizedLogScalar_continuousOn (M := M) J Ω hδ
  rw [regularizedModularLog_eq_cfc J Ω hε, regularizedModularLog_eq_cfc J Ω hδ,
    graphResolventCutoff_eq_cfc, ← cfc_sub _ _ _ he hd,
    ← cfc_mul (fun s : ℝ => regularizedLogScalar ε s - regularizedLogScalar δ s)
      (fun s : ℝ => s * (1 - s)) _ (he.sub hd) (by fun_prop)]
  apply norm_cfc_le (abs_nonneg _)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)),
    mul_comm]
  exact weighted_regularizedLog_difference s ε δ hb.1 hb.2 hε hδ

end

end KadisonKastler

end OAI
