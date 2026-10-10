import OAI.Analysis.KadisonKastler.IncreasingGroupEmbedding
import OAI.Analysis.KadisonKastler.AbelianInvariantMean
import OAI.Analysis.KadisonKastler.InjectiveStability
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

/-! # Constructed embeddings for commutative von Neumann algebras -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- All internal unitaries generate the represented algebra. -/
theorem generated_internal_unitaries (M : VonNeumannAlgebra H) :
    generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ
      (Set.range (fun u : unitary (Algebra M) => (u : H →L[ℂ] H)))) = M := by
  let A := StarAlgebra.adjoin ℂ
    (Set.range (fun u : unitary (Algebra M) => (u : H →L[ℂ] H)))
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro _ ⟨u, rfl⟩
    exact u.val.property
  · intro x hx
    apply subset_generatedVonNeumannAlgebra
    let V : Submodule ℂ (Algebra M) :=
      A.toSubalgebra.toSubmodule.comap M.toStarSubalgebra.subtype.toLinearMap
    have hspan : Submodule.span ℂ (unitary (Algebra M) : Set (Algebra M)) ≤ V := by
      apply Submodule.span_le.mpr
      intro u hu
      exact StarAlgebra.subset_adjoin ℂ _ ⟨⟨u, hu⟩, rfl⟩
    change (⟨x, hx⟩ : Algebra M) ∈ V
    apply hspan
    rw [CStarAlgebra.span_unitary]
    trivial

/-- The abelian unitary group mean gives an actual embedding, without an
injectivity or published amenable-embedding premise. -/
theorem exists_unitary_abelian_embedding {M N : VonNeumannAlgebra H}
    (hcomm : ∀ x y : Algebra M, x * y = y * x)
    {γ : ℝ} (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H), (∀ x ∈ M, unitaryConj w x ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let G : Type _ := unitary (Algebra M)
  let : CommGroup G := { (inferInstance : Group G) with
    mul_comm a b := Subtype.ext (hcomm a.val b.val) }
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  exact exists_unitary_embedding_of_invariant_group (abelianScalarInvariantMean G)
    (MonoidHom.id G) (generated_internal_unitaries M) hγ hsmall hnear

/-- At small ordinary distance the constructed inclusion is onto. -/
theorem exists_abelian_conjugacy_of_kkDistance_lt {M N : VonNeumannAlgebra H}
    (hcomm : ∀ x y : Algebra M, x * y = y * x)
    {γ : ℝ} (hγ : γ ≤ 1 / 1152) (hgap : kkDistance M N < γ) :
    ∃ w : unitary (H →L[ℂ] H), Conjugates w M N ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  have hpos : 0 < γ := (kkDistance_nonneg M N).trans_lt hgap
  obtain ⟨w, hw, hn⟩ := exists_unitary_abelian_embedding hcomm hpos.le hγ
    (nearInclusion_of_kkDistance_lt hgap)
  let P := unitaryConjugateAlgebra w M
  have hPN : P ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hw x hx
  have hdist : kkDistance P N < 1 := by
    have hd := kkDistance_conjugate_le (M := N) (conjugates_unitaryConjugateAlgebra w M)
    rw [kkDistance_comm N P, kkDistance_comm N M] at hd
    linarith
  have heq := eq_of_le_of_kkDistance_lt_one hPN hdist
  exact ⟨w, heq ▸ conjugates_unitaryConjugateAlgebra w M, hn⟩

end

end KadisonKastler

end OAI
