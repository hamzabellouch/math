import OAI.Analysis.KadisonKastler.StateBicentralizerLocal

namespace OAI

/-! # Closure of the bicentralizer in the faithful reference-vector norm

Near invariance of the reference state bounds the error caused by replacing
an operator by a nearby bicentralizer element on that vector. No uniform
operator-norm bound on the approximating elements is required.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateBicentralizerMember_of_reference_approximation (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ b : Algebra M,
      stateBicentralizerMember ξ b ∧ ‖(a-b).val ξ‖ < ε) :
    stateBicentralizerMember ξ a := by
  apply (stateBicentralizerMember_iff_local_reference ξ hsep a).mpr
  intro ε hε
  obtain ⟨b,hb,hnear⟩ := ha (ε/8) (by positivity)
  obtain ⟨δ,hδ,hbδ⟩ :=
    (stateBicentralizerMember_iff_local_reference ξ hsep b).mp hb (ε/2) (by positivity)
  let d := a-b
  let r := ε^2/(64*(‖d‖^2+1))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨min δ r,lt_min hδ hr,?_⟩
  intro u hu
  have hdnear : ‖d.val ξ‖ < ε/8 := hnear
  have hweight : r*‖d‖^2 ≤ ε^2/64 := by
    have he : r*(64*(‖d‖^2+1))=ε^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith only [he,hr]
  have hnorm := stateConjugate_vector_norm_sq_le ξ d u
  have hsmall : ‖(star u.val*d*u.val).val ξ‖ < ε/4 := by
    have hdef : ‖vectorStateCommutator ξ u.val‖*‖d‖^2 ≤ r*‖d‖^2 :=
      mul_le_mul_of_nonneg_right (lt_of_lt_of_le hu (min_le_right _ _)).le (sq_nonneg _)
    nlinarith only [hnorm,hdef,hweight,hdnear,norm_nonneg (d.val ξ),
      norm_nonneg ((star u.val*d*u.val).val ξ),hε]
  have hdcomm : ‖(d*u.val-u.val*d).val ξ‖ < ε/2 := by
    calc
      _ = ‖(star u.val*d*u.val).val ξ-d.val ξ‖ := by
        rw [← unitary_commutator_vector_norm_eq ξ d u]
        change ‖d.val (u.val.val ξ)-u.val.val (d.val ξ)‖=
          ‖u.val.val (d.val ξ)-d.val (u.val.val ξ)‖
        exact norm_sub_rev _ _
      _ ≤ ‖(star u.val*d*u.val).val ξ‖+‖d.val ξ‖ := norm_sub_le _ _
      _ < ε/2 := by linarith only [hsmall,hdnear,hε]
  have he : a*u.val-u.val*a=(b*u.val-u.val*b)+(d*u.val-u.val*d) := by
    dsimp [d]
    rw [sub_mul,mul_sub]
    abel
  rw [he]
  change ‖(b*u.val-u.val*b).val ξ+(d*u.val-u.val*d).val ξ‖ < ε
  exact (norm_add_le _ _).trans_lt (by
    have hh := hbδ u (lt_of_lt_of_le hu (min_le_left _ _))
    linarith only [hh,hdcomm])

end

end KadisonKastler

end OAI
