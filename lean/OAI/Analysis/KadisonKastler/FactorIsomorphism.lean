import OAI.Analysis.KadisonKastler.SemifiniteFactor

namespace OAI

/-! # Algebraic transport of the projection-theoretic factor predicates -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

private theorem equiv_star (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (x : Algebra M) :
    e (star x) = star (e x) := e.map_star' x

private theorem equiv_smul (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (c : ℂ) (x : Algebra M) :
    e (c • x) = c • e x := e.map_smul' c x

theorem ScalarCenter.of_starAlgEquiv (hM : ScalarCenter M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) : ScalarCenter N := by
  intro x hx hc
  let y : Algebra M := e.symm ⟨x, hx⟩
  have hy (a : Algebra M) : a * y = y * a := by
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    change (e a).val * (e (e.symm ⟨x, hx⟩)).val =
      (e (e.symm ⟨x, hx⟩)).val * (e a).val
    rw [e.apply_symm_apply]
    exact hc (e a).val (e a).property
  obtain ⟨c, hc⟩ := hM y.val y.property (fun a ha =>
    congrArg Subtype.val (hy ⟨a, ha⟩))
  have he : y = c • (1 : Algebra M) := Subtype.ext hc
  have ht := congrArg e he
  rw [equiv_smul, map_one] at ht
  dsimp only [y] at ht
  rw [e.apply_symm_apply] at ht
  exact ⟨c, congrArg Subtype.val ht⟩

theorem FiniteProjectionIn.of_starAlgEquiv (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (p : Algebra M) (hp : FiniteProjectionIn M p) : FiniteProjectionIn N (e p) := by
  intro v hv hvp
  have hi := congrArg e.symm hv
  rw [map_mul, equiv_star, e.symm_apply_apply] at hi
  have hl := congrArg e.symm hvp
  rw [map_mul, e.symm_apply_apply] at hl
  have he := congrArg e (hp (e.symm v) hi hl)
  rw [map_mul, equiv_star, e.apply_symm_apply] at he
  exact he

theorem nonzero_of_starAlgEquiv (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hM : (1 : H →L[ℂ] H) ≠ 0) : (1 : K →L[ℂ] K) ≠ 0 := by
  intro hn
  have ht : (1 : Algebra N) = 0 := Subtype.ext hn
  have hs : (1 : Algebra M) = 0 := by
    simpa only [map_one, map_zero] using congrArg e.symm ht
  exact hM (congrArg Subtype.val hs)

theorem TypeIIIFactor.of_starAlgEquiv (hM : TypeIIIFactor M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) : TypeIIIFactor N where
  nonzero := nonzero_of_starAlgEquiv e hM.nonzero
  factor := hM.factor.of_starAlgEquiv e
  purelyInfinite := by
    intro p hp hf
    have hs : FiniteProjectionIn M (e.symm p) :=
      FiniteProjectionIn.of_starAlgEquiv e.symm p hf
    have hz := hM.purelyInfinite (e.symm p) (hp.map e.symm) hs
    simpa only [StarAlgEquiv.apply_symm_apply, map_zero] using congrArg e hz

theorem ProperlyInfiniteIdentity.of_starAlgEquiv (hM : ProperlyInfiniteIdentity M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) : ProperlyInfiniteIdentity N where
  nonzero := nonzero_of_starAlgEquiv e hM.nonzero
  isometries := by
    obtain ⟨v, w, hv, hw, hvw⟩ := hM.isometries
    refine ⟨e v, e w, ?_, ?_, ?_⟩
    · have h := congrArg e hv
      rw [map_mul, equiv_star, map_one] at h
      exact h
    · have h := congrArg e hw
      rw [map_mul, equiv_star, map_one] at h
      exact h
    · have h := congrArg e hvw
      rw [map_mul, equiv_star, map_zero] at h
      exact h

end

end KadisonKastler

end OAI
