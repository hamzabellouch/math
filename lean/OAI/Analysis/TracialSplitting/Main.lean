import OAI.Analysis.TracialSplitting.FiniteSplitting

namespace OAI

universe uNuclear


section

namespace CurrentMain

open Pureness Filter

theorem real_rank_zero_uniform_gamma
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)) :
    UniformPropertyGammaAt A U := by
  classical
  let τ := fun t : TracialState A => t
  let D := FamilyUltrapower (completionTrace τ) U
  let j : A →⋆ₐ[ℂ] D := (familyUltrapowerMap (completionTrace τ) U).comp (completionMap τ)
  let σ := familyLimitTrace (completionTrace τ) U
  have hTD : Nonempty (TracialState D) := ⟨σ (fun _ => Classical.arbitrary _)⟩
  apply completion_central_splitting_of_finite_stages τ U hfree
  intro K ε hε
  obtain ⟨P,hP,htest⟩ := finite_set_central_splitting j (simple_starAlgHom_injective hsimple j)
    hA hRR hTD (fun _ hδ => small_full_projections hsimple hinf j hRR hTD hδ) K ε hε
  refine ⟨P,hP,?_⟩
  intro u hu
  exact ⟨(familyTwoNorm_le_uniform σ _).trans_lt (htest u hu).1,
    (familyHalvingError_le_uniform σ P (j (u : A))).trans_lt (htest u hu).2⟩

end CurrentMain

end

end OAI
