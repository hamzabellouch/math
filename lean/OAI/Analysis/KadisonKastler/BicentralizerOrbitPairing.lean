import OAI.Analysis.KadisonKastler.StateBicentralizerLocal

namespace OAI

/-! # Bicentralizer pairings are preserved by asymptotic orbit averages

The state commutator controls moving a unitary through the functional;
the bicentralizer controls the other error on the faithful vector.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateConjugate_pairing_error (ξ : H) (a b : Algebra M)
    (u : unitary (Algebra M)) :
    ‖inner ℂ (b.val ξ) ((star u.val*a*u.val).val ξ)-inner ℂ (b.val ξ) (a.val ξ)‖ ≤
      ‖(u.val*b*star u.val-b).val ξ‖*‖a.val ξ‖+
        ‖vectorStateCommutator ξ u.val‖*(‖b‖*‖a‖) := by
  let c := u.val*b*star u.val-b
  let z := star b*star u.val*a
  have hp (b a : Algebra M) : vectorFunctional ξ (star b*a)=
      inner ℂ (b.val ξ) (a.val ξ) := by
    change inner ℂ ξ (b.val.adjoint (a.val ξ))=inner ℂ (b.val ξ) (a.val ξ)
    exact b.val.adjoint_inner_right ξ (a.val ξ)
  have he : vectorFunctional ξ (star b*(star u.val*a*u.val))-
      vectorFunctional ξ (star b*a)=
      vectorFunctional ξ (star c*a)-vectorStateCommutator ξ u.val z := by
    dsimp only [c,z]
    simp only [vectorStateCommutator_apply,star_sub,star_mul,star_star,
      sub_mul,map_sub,mul_assoc]
    ring
  rw [← hp b (star u.val*a*u.val),← hp b a,he,hp c a]
  have hz : ‖z‖ ≤ ‖b‖*‖a‖ := by
    calc
      _ ≤ ‖star b*star u.val‖*‖a‖ := norm_mul_le _ _
      _ ≤ (‖b‖*‖u.val‖)*‖a‖ := by
        simpa only [norm_star] using mul_le_mul_of_nonneg_right
          (norm_mul_le (star b) (star u.val)) (norm_nonneg a)
      _ ≤ ‖b‖*‖a‖ := by
        have hu := norm_unitary_le_one u
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg b) hu
  exact (norm_sub_le _ _).trans (add_le_add (norm_inner_le_norm _ _)
    (((vectorStateCommutator ξ u.val).le_opNorm z).trans
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _))))

theorem stateOrbitCore_bicentralizer_pairing (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a b : Algebra M)
    (hb : stateBicentralizerMember ξ b) {T : H →WOT[ℂ] H}
    (hT : T ∈ stateOrbitCore ξ a) :
    inner ℂ (b.val ξ) (T ξ)=inner ℂ (b.val ξ) (a.val ξ) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let C := ‖b‖*‖a‖+‖a.val ξ‖+1
  let r := ε/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : 0 < r := div_pos hε hC
  obtain ⟨δ,hδ,hbδ⟩ := (stateBicentralizerMember_iff_local_reference ξ hsep b).mp hb r hr
  let d := min (δ/2) r
  have hd : 0 < d := lt_min (half_pos hδ) hr
  let L : (H →WOT[ℂ] H) →ₗ[ℝ] ℂ :=
    { toFun := fun S => inner ℂ (b.val ξ) (S ξ)
      map_add' := fun _ _ => inner_add_right _ _ _
      map_smul' := fun _ _ => inner_smul_real_right _ _ _ }
  let D : Set (H →WOT[ℂ] H) :=
    {S | ‖inner ℂ (b.val ξ) (S ξ)-inner ℂ (b.val ξ) (a.val ξ)‖ ≤ ε}
  have hcD : Convex ℝ D := by
    have he : D=L ⁻¹' Metric.closedBall (inner ℂ (b.val ξ) (a.val ξ)) ε := by
      ext S
      change ‖inner ℂ (b.val ξ) (S ξ)-inner ℂ (b.val ξ) (a.val ξ)‖ ≤ ε ↔
        dist (inner ℂ (b.val ξ) (S ξ)) (inner ℂ (b.val ξ) (a.val ξ)) ≤ ε
      rw [dist_eq_norm]
    rw [he]
    exact (convex_closedBall (inner ℂ (b.val ξ) (a.val ξ)) ε).linear_preimage L
  have hclosed : IsClosed D := by
    apply isClosed_le _ continuous_const
    exact ((ContinuousLinearMapWOT.continuous_inner_apply continuous_id ξ (b.val ξ)).sub
      continuous_const).norm
  apply closedConvexHull_min ?_ hcD hclosed (hT d hd)
  rintro S ⟨u,hu,rfl⟩
  have hstar : ‖vectorStateCommutator ξ (star u).val‖ < δ := by
    change ‖vectorStateCommutator ξ (star u.val)‖ < δ
    rw [vectorStateCommutator_star_norm]
    exact (hu.trans (min_le_left _ _)).trans_lt (by linarith)
  have hsmall := hbδ (star u) hstar
  have hconj : ‖(u.val*b*star u.val-b).val ξ‖ < r := by
    change ‖(u.val*b*star u.val).val ξ-b.val ξ‖ < r
    have he := unitary_commutator_vector_norm_eq ξ b (star u)
    simp only [Unitary.coe_star,star_star] at he
    rw [← he]
    change ‖(star u.val).val (b.val ξ)-b.val ((star u.val).val ξ)‖ < r
    change ‖b.val ((star u.val).val ξ)-(star u.val).val (b.val ξ)‖ < r at hsmall
    simpa only [norm_sub_rev] using hsmall
  have herr := stateConjugate_pairing_error ξ a b u
  change ‖inner ℂ (b.val ξ) ((star u.val*a*u.val).val ξ)-
    inner ℂ (b.val ξ) (a.val ξ)‖ ≤ ε
  apply herr.trans
  have hdsmall := hu.trans (min_le_right _ _)
  have hcancel : r*C=ε := div_mul_cancel₀ _ (ne_of_gt hC)
  change r*(‖b‖*‖a‖+‖a.val ξ‖+1)=ε at hcancel
  calc
    _ ≤ r*‖a.val ξ‖+r*(‖b‖*‖a‖) := add_le_add
      (mul_le_mul_of_nonneg_right hconj.le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hdsmall (by positivity))
    _ ≤ ε := by nlinarith only [hcancel,hr]

end

end KadisonKastler

end OAI
