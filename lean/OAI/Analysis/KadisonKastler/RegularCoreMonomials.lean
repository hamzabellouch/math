import OAI.Analysis.KadisonKastler.RegularCoreCovariance

namespace OAI

/-! # Algebraic generation by regular monomials

The core's algebraic generators reduce to finite linear combinations of
one original-algebra coefficient followed by one translation. This is
the dense algebra used to compute the frequency-window trace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

def regularCoreMonomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M) :
    Submonoid (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  carrier := {T | ∃ a ∈ M, ∃ s, regularCoreMonomial U hU a s = T}
  one_mem' := ⟨1, M.one_mem, 1, by simp [regularCoreMonomial]⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, s, rfl⟩ ⟨b, hb, t, rfl⟩
    refine ⟨a * unitaryConj (star (U s)) b, M.mul_mem ha ?_, s * t,
      (regularCoreMonomial_mul U hU a b s t).symm⟩
    rw [Unitary.star_eq_inv, ← map_inv]
    exact hM _ b hb

theorem regularCore_generator_mem_monomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularCoreGenerators U hU M) :
    T ∈ regularCoreMonomials U hU M hM := by
  rcases hT with ⟨a, ha, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨a, ha, 1, by simp [regularCoreMonomial]⟩
  · exact ⟨1, M.one_mem, s, by simp [regularCoreMonomial]⟩

theorem regularCore_generator_star_mem_monomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularCoreGenerators U hU M) :
    star T ∈ regularCoreMonomials U hU M hM := by
  apply regularCore_generator_mem_monomials U hU M hM
  rcases hT with ⟨a, ha, rfl⟩ | ⟨s, rfl⟩
  · exact Or.inl ⟨star a, M.star_mem' ha, (map_star (regularCoreEmbedding U hU) a)⟩
  · refine Or.inr ⟨s⁻¹, ?_⟩
    have he : regularRightTranslation (H := H) s⁻¹ = star (regularRightTranslation s) := by
      rw [map_inv, Unitary.star_eq_inv]
    exact congrArg Subtype.val he

theorem regularCore_adjoin_eq_span_monomials
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M) :
    (StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (regularCoreMonomials U hU M hM :
        Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by
  apply le_antisymm
  · rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_mono
    change Submonoid.closure (regularCoreGenerators U hU M ∪
      star (regularCoreGenerators U hU M)) ≤ regularCoreMonomials U hU M hM
    apply Submonoid.closure_le.mpr
    intro T hT
    rcases hT with hT | hT
    · exact regularCore_generator_mem_monomials U hU M hM hT
    · have h := regularCore_generator_star_mem_monomials U hU M hM (Set.mem_star.mp hT)
      rcases h with ⟨a, ha, s, he⟩
      refine ⟨a, ha, s, ?_⟩
      simpa only [star_star] using he
  · apply Submodule.span_le.mpr
    rintro T ⟨a, ha, s, rfl⟩
    exact (StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)).mul_mem
      (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, ha, rfl⟩))
      (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨s, rfl⟩))

end

end KadisonKastler

end OAI
