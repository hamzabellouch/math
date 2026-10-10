import OAI.Analysis.KadisonKastler.NearlyFullCornerWitness
import OAI.Analysis.KadisonKastler.PinchingRefinementInvariants

namespace OAI

/-! # A strict admissible refinement of every nearly full remainder

Both quantitative invariants survive the split, and the test-vector
energy increases strictly. This is the local contradiction for a maximal
orthogonal projection family.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance strictPinchingRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem exists_strict_pinching_refinement
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (A : H →L[ℂ] H) (hA : IsStarProjection A) (q : AlgebraProjection M)
    (hAq : A*modularQuadratic J q.val=0) (δ : ℝ) (hδ : 0 < δ)
    (hwide : ‖(1-modularQuadratic J q.val) ξ‖^2+
        ‖(1-modularQuadratic J q.val) η‖^2 ≤
      131072*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hsmall : ‖(1-(A+modularQuadratic J q.val)) ξ‖^2 ≤
      δ*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hgap : 131072*‖(1-(A+modularQuadratic J q.val)) η‖^2 ≤ 1/16) :
    ∃ p : AlgebraProjection M, p.val≠0 ∧ p≤q ∧
      IsStarProjection (A+refinedCornerProjection J q p) ∧
      (‖(1-modularQuadratic J (q.val-p.val)) ξ‖^2+
          ‖(1-modularQuadratic J (q.val-p.val)) η‖^2 ≤
        131072*‖(1-(A+refinedCornerProjection J q p)) η‖^2) ∧
      (‖(1-(A+refinedCornerProjection J q p)) ξ‖^2 ≤
        δ*‖(1-(A+refinedCornerProjection J q p)) η‖^2) ∧
      ‖(1-(A+modularQuadratic J q.val)) η‖^2 <
        ‖(1-(A+refinedCornerProjection J q p)) η‖^2 := by
  obtain ⟨p,hp,hpq,hm,hd⟩ := nearly_full_corner_projection_witness J hJ hright hleft
    ξ hξ huξ hsep hpos hIII hremote η hη huη horth q (hwide.trans hgap) hδ
  have he (z : H) : centralVectorDefect J z p.val.val=
      (p.val.val-conjugationOperator J p.val.val) z := by
    rw [centralVectorDefect_apply]
    have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
    rw [hs]
    rfl
  simp only [he] at hm hd
  have hmass : 2*(‖p.val.val (modularQuadratic J q.val ξ)‖^2+
      ‖p.val.val (modularQuadratic J q.val η)‖^2) ≤
      131072*‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2 := by
    linarith only [hm]
  have hinv := partialPinching_refinement_preserves J hJ hright A hA q p hpq hAq
    ξ η hξ hη 131072 δ hwide hsmall hmass hd.le
  refine ⟨p,hp,hpq,partialPinching_refinement_isProjection J hJ hright A hA q p hpq hAq,
    hinv.1,hinv.2,?_⟩
  rw [partialPinching_refinement_energy J hJ hright A hA q p hpq hAq η]
  have hpos' : 0 < ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2 := by
    nlinarith only [hm,sq_nonneg ‖p.val.val (modularQuadratic J q.val ξ)‖,
      sq_nonneg ‖p.val.val (modularQuadratic J q.val η)‖]
  linarith only [hpos']

end

end KadisonKastler

end OAI
