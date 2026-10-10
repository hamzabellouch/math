import OAI.Analysis.KadisonKastler.AmenableEmbedding
import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.Range

namespace OAI

/-! # Strong stability when the source algebra is injective

The one-sided amenable embedding gives a nearby conjugate subalgebra of
the neighbor. Riesz's lemma forces this inclusion to be equality once the
unit-ball gap is below one. No second perturbation or injectivity of the
neighbor is required.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A proper closed linear subspace cannot approximate the entire unit
ball with uniform error less than one. Applied inside the larger algebra,
this turns a sufficiently close inclusion into equality. -/
theorem eq_of_le_of_kkDistance_lt_one {P Q : VonNeumannAlgebra H}
    (hPQ : P ≤ Q) (hgap : kkDistance P Q < 1) : P = Q := by
  let V : Submodule ℂ (Algebra Q) :=
    P.toStarSubalgebra.toSubalgebra.toSubmodule.comap Q.toStarSubalgebra.subtype.toLinearMap
  have hclosed : IsClosed (V : Set (Algebra Q)) := by
    change IsClosed ((fun x : Algebra Q => x.val) ⁻¹' (P : Set (H →L[ℂ] H)))
    exact (isClosed_algebra P).preimage continuous_subtype_val
  let c := (kkDistance P Q + 1) / 2
  have hc : c < 1 := by dsimp [c]; linarith
  have hdist : kkDistance Q P < c := by
    rw [kkDistance_comm Q P]
    dsimp [c]
    linarith
  have htop : V = ⊤ := eq_top_of_unitBall_approx V hclosed hc (by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx (M := Q) (N := P)
      (x := x.val) ⟨x.property, hx⟩ hdist
    refine ⟨(⟨y, hPQ hy.1⟩ : Algebra Q), hy.1, ?_⟩
    exact hxy.le)
  apply le_antisymm hPQ
  intro x hx
  have hm : (⟨x, hx⟩ : Algebra Q) ∈ V := by rw [htop]; trivial
  exact hm

/-- The one-sided embedding already gives equality for an injective
source at a sufficiently small ordinary distance. -/
theorem exists_injective_conjugacy_of_kkDistance_lt
    (hpub : PublishedAmenableEmbedding (H := H))
    (M N : VonNeumannAlgebra H) (hM : IsInjective M)
    {γ : ℝ} (hγ : γ < 1 / 1000) (hgap : kkDistance M N < γ) :
    ∃ w : unitary (H →L[ℂ] H), Conjugates w M N ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * γ := by
  obtain ⟨w, hw, hnorm⟩ := exists_amenable_embedding_of_kkDistance_lt hpub
    (show M ≤ M from le_rfl) hM hgap (by linarith)
  let P := unitaryConjugateAlgebra w M
  have hPN : P ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hw x hx
  have hdist : kkDistance P N < 1 := by
    have hd := kkDistance_conjugate_le (M := N) (conjugates_unitaryConjugateAlgebra w M)
    rw [kkDistance_comm N P, kkDistance_comm N M] at hd
    linarith
  have heq := eq_of_le_of_kkDistance_lt_one hPN hdist
  exact ⟨w, heq ▸ conjugates_unitaryConjugateAlgebra w M, hnorm⟩

/-- The tolerance is independent of the Hilbert space and the two
algebras. Only the source must be injective. -/
theorem uniform_injective_strong_stability {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      PublishedAmenableEmbedding (H := H) →
      ∀ M N : VonNeumannAlgebra H, IsInjective M → kkDistance M N < δ →
        NearConjugacy M N ε := by
  refine ⟨min (1 / 2000) (ε / 300), lt_min (by norm_num) (by positivity), ?_⟩
  intro H _ _ _ hpub M N hM hgap
  obtain ⟨w, hw, hnorm⟩ := exists_injective_conjugacy_of_kkDistance_lt hpub M N hM
    (lt_of_le_of_lt (min_le_left _ _) (by norm_num)) hgap
  refine ⟨w, hw, ?_⟩
  have hsmall := min_le_right (1 / 2000 : ℝ) (ε / 300)
  linarith

end

end KadisonKastler

end OAI
