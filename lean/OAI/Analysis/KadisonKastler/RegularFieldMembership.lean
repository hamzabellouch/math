import OAI.Analysis.KadisonKastler.SpatialFieldPeriods
import OAI.Analysis.KadisonKastler.StrongCommutantTests
import OAI.Analysis.KadisonKastler.RegularCoreAlgebra
import OAI.Analysis.KadisonKastler.UnitBallClosure

namespace OAI

/-! # Countable tests recover fiberwise algebra membership

A represented measurable field inherits commutation with a bounded set
of constant operators on one common conull set. Countable strong tests
justify the interchange of the almost-everywhere and operator quantifiers.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Constant commutation descends to a represented field almost everywhere. -/
theorem RepresentsOperatorField.commute_constant_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (b : H →L[ℂ] H)
    (hcomm : Commute T (regularConstantHom volume b)) :
    ∀ᵐ t ∂volume, Commute (F t) b := by
  have he := hF.intertwine_translation b 0 (by simpa using hcomm)
  filter_upwards [he] with t ht
  change F t * b = b * F t
  simpa only [add_zero] using ht

/-- One common conull set works for a whole bounded collection of tests. -/
theorem RepresentsOperatorField.commute_set_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (S : Set (H →L[ℂ] H))
    (hS : ∀ b ∈ S, ‖b‖ ≤ 1)
    (hcomm : ∀ b ∈ S, Commute T (regularConstantHom volume b)) :
    ∀ᵐ t ∂volume, ∀ b ∈ S, Commute (F t) b := by
  obtain ⟨E, hEc, hES, htest⟩ := exists_countable_commutant_tests S hS
  have hall : ∀ᵐ t ∂volume, ∀ b ∈ E, Commute (F t) b := by
    apply (ae_ball_iff hEc).mpr
    intro b hb
    exact hF.commute_constant_ae b (hcomm b (hES hb))
  exact hall.mono fun t ht => (htest (F t)).mp ht

/-- The field of an operator in the constant-commutant tensor algebra
belongs to the original algebra almost everywhere. -/
theorem RepresentsOperatorField.mem_algebra_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (P : VonNeumannAlgebra H)
    (hT : T ∈ regularTensorAlgebra P) : ∀ᵐ t ∂volume, F t ∈ P := by
  have hc := hF.commute_set_ae (unitBall P.commutant) (fun _ hb => hb.2)
    (fun b hb => ((mem_regularTensorAlgebra_iff P T).mp hT b hb.1).symm)
  filter_upwards [hc] with t ht
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  have hclip : Commute (F t) (unitBallClip b) := ht _
    ⟨unitBallClip_mem P.commutant.toStarSubalgebra.toSubalgebra.toSubmodule hb,
      unitBallClip_norm_le b⟩
  have hp : 0 < max 1 ‖b‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have he : ((max 1 ‖b‖ : ℝ) : ℂ) • unitBallClip b = b := by
    rw [unitBallClip, smul_smul]
    have hn : ((max 1 ‖b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    simp only [Complex.ofReal_inv, mul_inv_cancel₀ hn, one_smul]
  have h := congrArg (fun B : H →L[ℂ] H => ((max 1 ‖b‖ : ℝ) : ℂ) • B) hclip.eq
  have heq : F t * (((max 1 ‖b‖ : ℝ) : ℂ) • unitBallClip b) =
      (((max 1 ‖b‖ : ℝ) : ℂ) • unitBallClip b) * F t := by
    rw [mul_smul_comm, smul_mul_assoc]
    exact h
  rw [he] at heq
  exact heq.symm

end

end KadisonKastler

end OAI
