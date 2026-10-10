import OAI.Computability.PerfectCompleteness.Decoding.LeftDecoder

namespace OAI


namespace PerfectCompleteness.LeftDecoderKnownRows

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open ClauseSupport MixedSupport
open LeftDecoder (F2)

noncomputable section

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (labeling : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

theorem exists_fallback_candidate_realizer
    (hW : RepresentativeMatrixTable.Determined slots H other W) :
    ∃ x : Assignment slots,
      other x = (CanonicalMatrixTable.response slots H other labeling
        (0 : CanonicalMatrixTable.Matrix (K := K) slots H)).2 ∧
      ∀ q : PulledColumnSpace.Candidates W ⊥
        (RepresentativeMatrixTable.correctionFunctional slots H other W s hs
          (CanonicalMatrixTable.response slots H other labeling
            (0 : CanonicalMatrixTable.Matrix (K := K) slots H)).2),
      ∀ b : W, q.val (b : H) = b.val.val x := by
  obtain ⟨x, _, hx⟩ := CanonicalMatrixTable.response_realized slots H other labeling
    (0 : CanonicalMatrixTable.Matrix (K := K) slots H)
  refine ⟨x, hx, ?_⟩
  intro q b
  rw [PulledColumnSpace.candidate_apply_known, ← hx]
  simpa only [add_zero] using RepresentativeDecoder.coset_apply_at_image
    slots H other W s hs hW x 0 W.dualAnnihilator.zero_mem b


attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable [FiniteDimensional F2 H]
  [Fintype H] [Fintype K]
  (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)

local instance representativeDualFintype : Fintype (Module.Dual F2 H) :=
  LeftDecoder.dualFintype (V := H)

theorem adviceLaw_probability_eq_one_of_known_realizer
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2))
    (event : Module.Dual F2 H → Bool)
    (hevent : ∀ q : Module.Dual F2 H,
      (∃ x : Assignment slots, ∀ b : W, q (b : H) = b.val.val x) → event q = true) :
    (LeftDecoder.adviceLaw slots H other labeling W s hs useful r ρ A U).probability
      event = 1 := by
  by_cases hgood : ManyGoodRows.GoodRow
      (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U
  · rw [LeftDecoder.adviceLaw_of_good slots H other labeling W s hs useful r ρ A U hgood]
    unfold LeftDecoder.law
    apply LeftDecoder.affineLaw_probability_eq_one
    intro q
    obtain ⟨x, _, hknown⟩ := LeftDecoder.exists_candidate_realizer
      slots H other labeling W s hs useful hW
      (ManyGoodRows.selectWitness
        (RepresentativeMatrixTable.partialTable slots H other labeling W s useful)
        r ρ A U hgood) hρ
    exact hevent q.val ⟨x, hknown q⟩
  · simp only [LeftDecoder.adviceLaw, dite_eq_right hgood]
    apply LeftDecoder.affineLaw_probability_eq_one
    intro q
    obtain ⟨x, _, hknown⟩ :=
      exists_fallback_candidate_realizer (K := K) slots H other labeling W s hs hW
    exact hevent q.val ⟨x, hknown q⟩

theorem adviceLaw_known_realizer
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)) :
    (LeftDecoder.adviceLaw slots H other labeling W s hs useful r ρ A U).probability
      (fun q => decide (∃ x : Assignment slots,
        ∀ b : W, q (b : H) = b.val.val x)) = 1 :=
  adviceLaw_probability_eq_one_of_known_realizer
    slots H other labeling W s hs useful hW r ρ hρ A U _
    (fun _ hx => decide_eq_true hx)


end
end PerfectCompleteness.LeftDecoderKnownRows

end OAI
