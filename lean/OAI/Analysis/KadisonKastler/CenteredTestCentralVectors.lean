import OAI.Analysis.KadisonKastler.ModularAlgebraicTestValues
import OAI.Analysis.KadisonKastler.CenteredTestShiftLimits
import OAI.Analysis.KadisonKastler.NormPreservingGraphShift
import OAI.Analysis.KadisonKastler.ModularRightScalar
import OAI.Analysis.KadisonKastler.ModularScalingDefect

namespace OAI

/-! # Moving the detected centered test to approximate central vectors

The remote coisometries shift either side of the modular eigenvalue one.
Their existence is supplied by the constructed spatial matrix product.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

private theorem real_lt_of_close {z w : ℂ} {c c' η : ℝ}
    (hz : ‖z-w‖ < η) (hw : c' < w.re) (hη : η ≤ c'-c) : c < z.re := by
  have h := (Complex.abs_re_le_norm (z-w)).trans_lt hz
  have hh := (abs_lt.mp h).1
  change -η < z.re-w.re at hh
  linarith

theorem centeredTest_approximate_central_vectors
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (S : ModularSpectralResolution M Ω)
    (hcuts : ∀ r, S.upperCut r=modularUpperCut M J Ω r)
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (hremote : ∀ t : ℝ, 0 < t → t < 1 → ∃ v : ℕ → Algebra M,
      (∀ n, v n*star (v n)=1) ∧
      Tendsto (fun n => (v n).val Ω-(t : ℂ) • d.rightAction (v n) Ω) atTop (𝓝 0) ∧
      ∀ (b : Algebra M) (η : H),
        Tendsto (fun n => (v n*b*star (v n)).val η) atTop (𝓝 (b.val η)))
    (a : Algebra M) {c : ℝ} (hc : c < (ψ (modularCenteredTest d a)).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Algebra M, ‖b.val Ω-d.rightAction b Ω‖ < ε ∧
      ((‖b.val Ω‖ < 2 ∧ c < (inner ℂ (b.val Ω) (modularCenteredTest d a (b.val Ω))).re) ∨
       (‖d.rightAction b Ω‖ < 2 ∧ c <
         (inner ℂ (d.rightAction b Ω) (modularCenteredTest d a (d.rightAction b Ω))).re)) := by
  let T := modularCenteredTest d a
  let c' := (c+(ψ T).re)/2
  have hcc : c < c' := by dsimp [c',T]; linarith
  have hcp : c' < (ψ T).re := by dsimp [c']; linarith
  let γ := min (ε/8) (1/4)
  have hγ : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγε : γ ≤ ε/8 := min_le_left _ _
  have hγ1 : γ ≤ 1/4 := min_le_right _ _
  obtain ⟨x,q,ξ,hq,hξ,hxl,hxr,hvl,hvr⟩ := exists_algebraic_modular_test_values
    J hsep hcyc d hd S hcuts ψ hψ hinv T (modularCenteredTest_selfAdjoint d a) hcp hγ
  have hlnorm : ‖x.val Ω‖ < 2 := by
    have h := norm_le_norm_sub_add (x.val Ω) ξ
    rw [hξ] at h
    linarith
  have hrnorm : ‖((q : ℂ)⁻¹) • d.rightAction x Ω‖ < 2 := by
    have h := norm_le_norm_sub_add (((q : ℂ)⁻¹) • d.rightAction x Ω) ξ
    rw [hξ] at h
    linarith
  have hdef : ‖x.val Ω-((q : ℂ)⁻¹) • d.rightAction x Ω‖ < 2*γ := by
    have h := norm_sub_le_norm_sub_add_norm_sub (x.val Ω) ξ
      (((q : ℂ)⁻¹) • d.rightAction x Ω)
    rw [norm_sub_rev ξ] at h
    linarith
  let η := min (ε/2) (c'-c)
  have hη : 0 < η := lt_min (by positivity) (sub_pos.mpr hcc)
  have hηε : η ≤ ε/2 := min_le_left _ _
  have hηc : η ≤ c'-c := min_le_right _ _
  rcases lt_trichotomy q 1 with hq1 | hq1 | hq1
  · obtain ⟨v,hv,hscale,hconv⟩ := hremote q hq hq1
    let y : Algebra M := (q : ℂ)⁻¹ • x
    have hry : d.rightAction y Ω=((q : ℂ)⁻¹) • d.rightAction x Ω := by
      rw [d.rightAction_smul,smul_apply]
    have hleft : (q : ℂ) • y.val Ω=x.val Ω := by
      change (q : ℂ) • ((q : ℂ)⁻¹ • x.val Ω)=_
      rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hq.ne'),one_smul]
    obtain ⟨b,hb,hbn,hbt⟩ := d.exists_coisometry_test_shift v hv Ω Ω (q : ℂ)
      hscale y T (d.coisometry_centeredTest_tendsto v hconv a (d.rightAction y Ω)) hη
    rw [hleft,hry] at hb
    refine ⟨b,by linarith,Or.inr ⟨?_,?_⟩⟩
    · rw [hbn,hry]
      exact hrnorm
    · rw [hry] at hbt
      exact real_lt_of_close hbt hvr hηc
  · subst q
    simp only [Complex.ofReal_one,inv_one,one_smul] at hdef
    exact ⟨x,by linarith,Or.inl ⟨hlnorm,hcc.trans hvl⟩⟩
  · have ht : 0 < q⁻¹ := inv_pos.mpr hq
    have ht1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    obtain ⟨v,hv,hscale,hconv⟩ := hremote q⁻¹ ht ht1
    obtain ⟨b,hb,hbn,hbt⟩ := d.exists_isometry_test_shift v hv Ω Ω ((q⁻¹ : ℝ) : ℂ)
      (d.rightAction_adjoint_defect_tendsto v q⁻¹ hscale) x T
      (d.isometry_centeredTest_tendsto v hconv a (x.val Ω)) hη
    rw [Complex.ofReal_inv] at hb
    exact ⟨b,by linarith,Or.inl ⟨hbn.trans_lt hlnorm,real_lt_of_close hbt hvl hηc⟩⟩

end

end KadisonKastler

end OAI
