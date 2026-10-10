import OAI.Analysis.KadisonKastler.ModularHaagerupWitnesses

namespace OAI

/-! # Two-vector witnesses on the algebraic symmetric core

This is the bounded-vector part of Haagerup's Lemma 2.9. The constants
are deliberately loose; they remain uniform over the algebra and vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem commutator_norm_le_vector_defects (a b : Algebra M) :
    ‖(a*b-b*a).val Ω‖ ≤
      ‖a‖*‖b.val Ω-d.rightAction b Ω‖+
        ‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖ := by
  have he : (a*b-b*a).val Ω =
      a.val (b.val Ω-d.rightAction b Ω)-
        (b.val (a.val Ω)-d.rightAction b (a.val Ω)) := by
    have hc := congrArg (fun T : H →L[ℂ] H => T Ω) (d.rightAction_commute a b)
    change a.val (d.rightAction b Ω)=d.rightAction b (a.val Ω) at hc
    change a.val (b.val Ω)-b.val (a.val Ω)=_
    rw [map_sub,hc]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (a.val.le_opNorm _) le_rfl)

theorem bounded_symmetric_vector_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Algebra M,
      ‖b.val Ω‖+‖b.val (a.val Ω)‖ <
        12*‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖ ∧
      ‖b.val Ω-d.rightAction b Ω‖ <
        δ*‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖ := by
  let γ := min (δ/2) (1/(2*(‖a‖+1)))
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  have hγδ : γ ≤ δ/2 := min_le_left _ _
  have ham : ‖a‖*γ ≤ 1/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*(‖a‖+1) by positivity)).mp
      (show γ ≤ 1/(2*(‖a‖+1)) from min_le_right _ _)
    nlinarith
  obtain ⟨b,hsize,hdef⟩ := h a hbal hzero hnorm γ hγ
  let C := ‖(a*b-b*a).val Ω‖
  let D := ‖b.val (a.val Ω)-d.rightAction b (a.val Ω)‖
  have hC : C ≤ 2*D := by
    have hnorms := d.commutator_norm_le_vector_defects a b
    have he : ‖a‖*‖b.val Ω-d.rightAction b Ω‖ ≤ (1/2)*C := by
      calc
        _ ≤ ‖a‖*(γ*C) := mul_le_mul_of_nonneg_left hdef.le (norm_nonneg a)
        _ = (‖a‖*γ)*C := by ring
        _ ≤ (1/2)*C := mul_le_mul_of_nonneg_right ham (norm_nonneg _)
    change C ≤ _+D at hnorms
    linarith
  refine ⟨b,?_,?_⟩
  · change ‖b.val Ω‖+‖(b*a).val Ω‖ < 12*D
    exact hsize.trans_le (by linarith)
  · calc
      _ < γ*C := hdef
      _ ≤ (δ/2)*C := mul_le_mul_of_nonneg_right hγδ (norm_nonneg _)
      _ ≤ δ*D := by nlinarith

end ModularConjugationData

end

end KadisonKastler

end OAI
