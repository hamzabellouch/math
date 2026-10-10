import OAI.Analysis.KadisonKastler.CoreHalfFrequencyWindow
import OAI.Analysis.KadisonKastler.CoreTraceDualScaling
import OAI.Analysis.KadisonKastler.CoreDualAction
import OAI.Analysis.KadisonKastler.ConstructedCoreFiniteWindow
import OAI.Analysis.KadisonKastler.CornerProjectionVectorNorm
import OAI.Analysis.KadisonKastler.SemifiniteIsomorphism

namespace OAI

/-! # Dual translation changes the trace of every nonzero sub-half-window -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coreFrequencyProjection
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (a b : ℝ) : AlgebraProjection (regularCoreAlgebra U hU M) :=
  ⟨⟨regularFrequencyWindow a b, regularFrequencyWindow_mem_core U hU M a b⟩, by
    constructor
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) a b).isIdempotentElem.eq
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) a b).isSelfAdjoint.star_eq⟩

theorem coreFrequencyProjection_le
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (a b c d : ℝ) (h : Set.Ioc a b ⊆ Set.Ioc c d) :
    coreFrequencyProjection U hU M a b ≤ coreFrequencyProjection U hU M c d := by
  apply Subtype.ext
  change regularFrequencyWindow c d * regularFrequencyWindow a b = regularFrequencyWindow a b
  have he := regularFrequencyWindow_mul_of_subset (H := H) a b c d h
  simpa only [star_mul, (regularFrequencyWindow_isStarProjection (H := H) a b).isSelfAdjoint.star_eq,
    (regularFrequencyWindow_isStarProjection (H := H) c d).isSelfAdjoint.star_eq] using congrArg star he

variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def constructedCoreDualEquiv (a : ℝ) :
    Algebra (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) ≃⋆ₐ[ℂ]
    Algebra (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) :=
  regularCoreDualEquiv _ _ M
    (fun s _ ha => modularStrongGroup_conj_mem J Ω hsep hcyc s.toAdd ha) a

theorem constructedCore_subhalf_not_equivalent_dual
    (q : AlgebraProjection (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)) (hq0 : q.val ≠ 0)
    (hqh : q ≤ coreFrequencyProjection _ _ M 0 (1 / 2)) :
    ¬ q.Equivalent (mapAlgebraProjection
      (constructedCoreDualEquiv J Ω hsep hcyc (2 * Real.pi * (1 / 2))) q) := by
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  let R := regularCoreAlgebra U hU M
  let p := coreFrequencyProjection U hU M 0 1
  let e := constructedCoreDualEquiv J Ω hsep hcyc (2 * Real.pi * (1 / 2))
  let r := mapAlgebraProjection e q
  have hsub : Set.Ioc (0 : ℝ) (1 / 2) ⊆ Set.Ioc 0 1 := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (by norm_num)⟩
  have hqp : q ≤ p := hqh.trans (coreFrequencyProjection_le U hU M 0 (1 / 2) 0 1 hsub)
  have hshift : mapAlgebraProjection e (coreFrequencyProjection U hU M 0 (1 / 2)) =
      coreFrequencyProjection U hU M (1 / 2) 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change unitaryConj (regularCharacterUnitary (H := H) (2 * Real.pi * (1 / 2)))
      (regularFrequencyWindow 0 (1 / 2)) = regularFrequencyWindow (1 / 2) 1
    simpa only [zero_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using
      regularFrequencyWindow_character_conj (H := H) 0 (1 / 2) (1 / 2)
  have hrp : r ≤ p := by
    have hr := mapAlgebraProjection_mono e hqh
    rw [hshift] at hr
    exact hr.trans (coreFrequencyProjection_le U hU M (1 / 2) 1 0 1 (by
      intro t ht
      exact ⟨lt_trans (by norm_num) ht.1, ht.2⟩))
  have hright : q.val.val * regularFrequencyWindow 0 1 = q.val.val :=
    congrArg Subtype.val (projection_mul_of_le hqp)
  have hleft : q.val.val * regularFrequencyWindow (-(1 / 2)) (1 - 1 / 2) = q.val.val := by
    have hi := coreFrequencyProjection_le U hU M 0 (1 / 2) (-(1 / 2)) (1 - 1 / 2) (by
      intro t ht
      exact ⟨lt_trans (by norm_num) ht.1, le_trans ht.2 (by norm_num)⟩)
    exact congrArg Subtype.val (projection_mul_of_le (hqh.trans hi))
  have hqξ : q.val.val (coreTraceFrequencyVector Ω) ≠ 0 := by
    intro hz
    have hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M :=
      fun s _ ha => modularStrongGroup_conj_mem J Ω hsep hcyc s.toAdd ha
    have hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω := by
      intro s
      simpa only [ofAdd_toAdd] using modularStrongGroup_fixes_state J Ω hsep hcyc s.toAdd
    have he := core_kills_window_of_kills_trace_packet U hU M hn Ω hΩ hsep
      q.val.val q.val.property hz
    rw [hright] at he
    exact hq0 (Subtype.ext he)
  have hscale : ‖r.val.val (coreTraceFrequencyVector Ω)‖ =
      Real.exp (Real.pi * (1 / 2)) * ‖q.val.val (coreTraceFrequencyVector Ω)‖ := by
    change ‖unitaryConj (regularCharacterUnitary (H := H) (2 * Real.pi * (1 / 2)))
      q.val.val (coreTraceFrequencyVector Ω)‖ = _
    simp only [unitaryConj, mul_apply_eq_comp, Unitary.norm_map]
    rw [coreTraceFrequencyVector_supported_scaling (1 / 2) Ω q.val.val hright hleft,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  intro heq
  have hn := equivalent_corner_projection_vector_norm p q r (coreTraceFrequencyVector Ω)
    hqp hrp (fun a hpa hap => ?_) heq
  · have he := Real.one_lt_exp_iff.mpr (show 0 < Real.pi * (1 / 2) by positivity)
    have hpos := norm_pos_iff.mpr hqξ
    nlinarith
  · let P := tomitaPolarConjugation J Ω hsep hcyc
    let C := regularCoreConjugation U hU P
    have hC := regularCoreConjugation_involutive U hU P
      (tomitaPolarConjugation_involutive J Ω hsep hcyc)
      (modularStrongGroup_polar_commutes J Ω hsep hcyc)
    have ha := constructedCore_traceSymmetry J Ω hsep hcyc a.val a.property
    have hl : regularFrequencyWindow 0 1 * a.val = a.val := congrArg Subtype.val hpa
    have hr : a.val * regularFrequencyWindow 0 1 = a.val := congrArg Subtype.val hap
    rw [hl, hr] at ha
    exact coreTraceSymmetry_norm C hC (coreTraceFrequencyVector Ω) a.val ha

end

end KadisonKastler

end OAI
