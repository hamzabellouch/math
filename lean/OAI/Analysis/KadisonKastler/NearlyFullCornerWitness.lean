import OAI.Analysis.KadisonKastler.ModularCornerNormalization
import OAI.Analysis.KadisonKastler.UnnormalizedProjectionWitness
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison

namespace OAI

/-! # A uniform projection witness in every nearly full corner

The constant is independent of the corner. The hypotheses are the actual
positive reference and the all-vector remote coisometries already constructed
in the spatial two-ratio product.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance nearlyFullRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem nearly_full_corner_projection_witness
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (q : AlgebraProjection M)
    (hsmall : ‖(1-modularQuadratic J q.val) ξ‖^2+
      ‖(1-modularQuadratic J q.val) η‖^2≤1/16)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val≠0 ∧ p≤q ∧
      ‖p.val.val (modularQuadratic J q.val ξ)‖^2+
        ‖p.val.val (modularQuadratic J q.val η)‖^2 <
        65536*‖centralVectorDefect J (modularQuadratic J q.val η) p.val.val‖^2 ∧
      ‖centralVectorDefect J (modularQuadratic J q.val ξ) p.val.val‖^2 <
        δ*‖centralVectorDefect J (modularQuadratic J q.val η) p.val.val‖^2 := by
  let P := modularQuadratic J q.val
  have hP : IsStarProjection P := modularQuadratic_projection J hJ hright q
  obtain ⟨hx,hy,hdet⟩ := projection_corner_angle_determinant hP ξ η huξ huη horth hsmall
  have hnx : ‖P ξ‖≤1 := (projection_apply_norm_le hP ξ).trans_eq huξ
  have hny : ‖P η‖≤1 := (projection_apply_norm_le hP η).trans_eq huη
  have hq : q.val≠0 := by
    intro he
    have hP0 : P=0 := by
      change modularQuadratic J q.val=0
      rw [he]
      rfl
    rw [hP0,zero_apply,norm_zero] at hx
    exact (lt_irrefl 0) hx
  obtain ⟨v,hv,hvq⟩ := hIII.exists_isometry_onto_projection q.val q.property hq
  let x := modularQuadratic J (star v) ξ
  let y := modularQuadratic J (star v) η
  have hxn : x≠0 := norm_ne_zero_iff.mp (ne_of_gt (by
    simpa only [x,modularCorner_pullback_norm J hJ hright v hv q hvq] using hx))
  have hyn : y≠0 := norm_ne_zero_iff.mp (ne_of_gt (by
    simpa only [y,modularCorner_pullback_norm J hJ hright v hv q hvq] using hy))
  have hang := normalized_angle_lower (P ξ) (P η) (norm_pos_iff.mp hx)
    (norm_pos_iff.mp hy) hnx hny hdet
  have hinner := modularCorner_normalized_inner J hJ hright v hv q hvq ξ η
  have hang' : 1/2≤1-(inner ℂ (normalize x) (normalize y)).re^2 := by
    change 1/2≤1-(inner ℂ (normalize (modularQuadratic J (star v) ξ))
      (normalize (modularQuadratic J (star v) η))).re^2
    rw [hinner]
    exact hang
  obtain ⟨hne,hne'⟩ := normalized_angle_noncollinear x y hxn hyn hang'
  obtain ⟨p,hp,hpq,hm,hd⟩ := positive_corner_projection_witness J hJ hright hleft
    ξ hξ hpos ξ (reference_mem_modularPositiveCone J hJ ξ) hsep
    (by rw [← norm_pos_iff,huξ]; norm_num) hIII hremote q v hv hvq η hη hyn hne hne'
    (half_pos hδ)
  simp only [modularCorner_push_normalize J hJ hright v hv q hvq,hinner] at hm hd
  have hY : 1/2≤‖P η‖^2 := by
    have hX : ‖P ξ‖^2≤1 := by nlinarith only [hnx,norm_nonneg (P ξ)]
    have hh := mul_le_of_le_one_left (sq_nonneg ‖P η‖) hX
    nlinarith only [hdet,hh,sq_nonneg (inner ℂ (P ξ) (P η)).re]
  exact ⟨p,hp,hpq,projection_witness_unnormalize J (P ξ) (P η) p.val.val
    hnx hny hY _ δ hang hδ hm hd⟩

end

end KadisonKastler

end OAI
