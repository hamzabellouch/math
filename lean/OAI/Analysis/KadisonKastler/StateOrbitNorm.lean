import OAI.Analysis.KadisonKastler.StateOrbitComposition

namespace OAI

/-! # Vector norms on approximate state-central orbit hulls

Approximate invariance of the reference state controls the vector norm
of every conjugate. Weak lower semicontinuity extends the estimate to
the closed convex hull; its asymptotic core cannot increase vector norm.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateConjugate_vector_norm_sq_le (ξ : H) (a : Algebra M)
    (u : unitary (Algebra M)) :
    ‖(star u.val*a*u.val).val ξ‖^2 ≤ ‖a.val ξ‖^2+
      ‖vectorStateCommutator ξ u.val‖*‖a‖^2 := by
  let F := sandwichFunctional (vectorFunctional (M := M) ξ) u.val-vectorFunctional ξ
  have hF : ‖F‖ ≤ ‖vectorStateCommutator ξ u.val‖ := by
    simpa only [Unitary.coe_star,star_star,vectorStateCommutator_star_norm] using
      sandwich_unitary_state_norm_sub_le ξ (star u)
  have he : (F (star a*a)).re=‖a.val (u.val.val ξ)‖^2-‖a.val ξ‖^2 := by
    dsimp only [F]
    rw [sub_apply,sandwichFunctional_vectorFunctional,
      vectorFunctional_star_mul_self,vectorFunctional_star_mul_self]
    norm_cast
  have hb : ‖F (star a*a)‖ ≤ ‖vectorStateCommutator ξ u.val‖*‖a‖^2 := by
    have hn : ‖star a*a‖=‖a‖^2 := by rw [CStarRing.norm_star_mul_self,pow_two]
    exact (F.le_opNorm _).trans (by rw [hn]; gcongr)
  have hr := Complex.re_le_norm (F (star a*a))
  rw [he] at hr
  have hu : ‖(star u.val*a*u.val).val ξ‖=‖a.val (u.val.val ξ)‖ := by
    exact Unitary.norm_map (ambientAlgebraUnitary (star u)) _
  rw [hu]
  linarith only [hr,hb]

omit [CompleteSpace H] in
private theorem wotVectorSquaredBall_convex (ξ : H) (R : ℝ) (hR : 0 ≤ R) :
    Convex ℝ {T : H →WOT[ℂ] H | ‖T ξ‖^2 ≤ R} := by
  let ev : (H →WOT[ℂ] H) →ₗ[ℝ] H :=
    { toFun := fun T => T ξ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : {T : H →WOT[ℂ] H | ‖T ξ‖^2 ≤ R} =
      ev ⁻¹' Metric.closedBall 0 (Real.sqrt R) := by
    ext T
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right]
    exact (Real.le_sqrt (norm_nonneg _) hR).symm
  rw [he]
  exact (convex_closedBall (0 : H) (Real.sqrt R)).linear_preimage ev

theorem stateOrbitHull_vector_norm_sq_le (ξ : H) (a : Algebra M)
    {δ : ℝ} (hδ : 0 ≤ δ) {T : H →WOT[ℂ] H}
    (hT : T ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a δ)) :
    ‖T ξ‖^2 ≤ ‖a.val ξ‖^2+δ*‖a‖^2 := by
  apply closedConvexHull_min ?_
    (wotVectorSquaredBall_convex ξ _ (by positivity))
    (show IsClosed {S : H →WOT[ℂ] H | ‖S ξ‖^2 ≤ ‖a.val ξ‖^2+δ*‖a‖^2} from by
      simpa only [Set.preimage,Set.mem_Iic,sub_zero] using
        (wot_vector_sqDistance_lowerSemicontinuous ξ 0).isClosed_preimage
          (‖a.val ξ‖^2+δ*‖a‖^2)) hT
  rintro S ⟨u,hu,rfl⟩
  exact (stateConjugate_vector_norm_sq_le ξ a u).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hu (sq_nonneg _)))

theorem stateOrbitCore_vector_norm_sq_le (ξ : H) (a : Algebra M)
    {T : H →WOT[ℂ] H} (hT : T ∈ stateOrbitCore ξ a) : ‖T ξ‖^2 ≤ ‖a.val ξ‖^2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(‖a‖^2+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hb := stateOrbitHull_vector_norm_sq_le ξ a hδ.le (hT δ hδ)
  have hm : δ*(‖a‖^2+1)=ε := div_mul_cancel₀ ε (by positivity)
  have hp : 0 ≤ δ := hδ.le
  nlinarith only [hb,hm,hp]

end

end KadisonKastler

end OAI
