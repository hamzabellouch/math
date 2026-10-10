import OAI.Combinatorics.ContingencyTables.Counting.CompanionComputedInitial
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableReindex

namespace OAI

/-! # Exact invariance of the finite initializer under computed cell order -/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FixedCardinalityMixture
open InitialTransversals CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section
variable {C : Type*} [Fintype C] {q : ℕ}

def finiteChoiceLaw (b : C → ℕ) (B : ℕ) : RationalLaw ((c : C) → Finset (Fin (b c))) where
  mass S := ∏ c,(mapLaw (uniformLaw (α := Fin (drawBits B (b c)) → Bool))
    (subsetDraw B (b c))).mass (S c)
  nonnegative S := Finset.prod_nonneg (fun c _ => (mapLaw
    (uniformLaw (α := Fin (drawBits B (b c)) → Bool)) (subsetDraw B (b c))).nonnegative (S c))
  total := by
    rw [←Fintype.prod_sum]
    simp only [RationalLaw.total,Finset.prod_const_one]

/-- Reordering the independent cell words changes no finite initializer
law, including its finite-precision bias. -/
theorem transversalDraw_law (b : C → ℕ) (e : C ≃ Fin q) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
      (transversalDraw b e B)=
        equivLaw (plainEquivChoices b).symm (finiteChoiceLaw b B) := by
  let E := (choiceEquiv b e).trans (plainEquivChoices b).symm
  have he := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
    (drawChoices (fun i => b (e.symm i)) B)
  rw [drawChoices_law] at he
  change mapLaw _ (fun bits => E (drawChoices _ B bits))=_
  refine he.trans ?_
  apply RationalLaw.ext
  funext S
  change (∏ i : Fin q,
    (mapLaw (uniformLaw (α := Fin (drawBits B (b (e.symm i))) → Bool))
      (subsetDraw B (b (e.symm i)))).mass ((plainEquivChoices b S) (e.symm i)))=
    ∏ c,(mapLaw (uniformLaw (α := Fin (drawBits B (b c)) → Bool))
      (subsetDraw B (b c))).mass ((plainEquivChoices b S) c)
  symm
  apply Fintype.prod_equiv e
  intro c
  exact congrArg (fun c =>
    (mapLaw (uniformLaw (α := Fin (drawBits B (b c)) → Bool))
      (subsetDraw B (b c))).mass ((plainEquivChoices b S) c)) (e.symm_apply_apply c).symm

end
end ContingencyTables.InitialFactorialBits

namespace ContingencyTables.CompanionComputedInitial

open CommonBasesFPRAS ResidualMixture FirstSuccess CompanionFactorialApplication
open InitialFactorialBits FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem initialDraw_law (A : Instance (Fin m) (Fin n)) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (wordLength A B) → Bool)) (initialDraw A B)=
      mapLaw (uniformLaw (α := Fin (CompanionInitialDraw.initialBits A B) → Bool))
        (CompanionInitialDraw.draw A B) := by
  let b := fun s : SmallCell A => A.b s.val.1 s.val.2
  let E := CompanionInitialDraw.indexEquiv A
  have h₁ := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b ((cellOrder A).symm i)) B) → Bool))
    (transversalDraw b (cellOrder A) B)
  have h₂ := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b ((CompanionInitialDraw.cellEnum A).symm i)) B) → Bool))
    (transversalDraw b (CompanionInitialDraw.cellEnum A) B)
  have ht : mapLaw (uniformLaw (α := Fin (bitCount (fun i => b ((cellOrder A).symm i)) B) → Bool))
      (transversalDraw b (cellOrder A) B)=
      mapLaw (uniformLaw (α := Fin (bitCount (fun i => b ((CompanionInitialDraw.cellEnum A).symm i)) B) → Bool))
        (transversalDraw b (CompanionInitialDraw.cellEnum A) B) :=
    (transversalDraw_law b (cellOrder A) B).trans
      (transversalDraw_law b (CompanionInitialDraw.cellEnum A) B).symm
  exact h₁.trans ((congrArg (equivLaw E) ht).trans h₂.symm)

theorem initialProgram_sameLaw (A : Instance (Fin m) (Fin n)) (B : ℕ) (hB : 0 < B) :
    SameLaw (fun bits : Fin (wordLength A B) → Bool =>
      initialProgram ((CompanionCellCatalog.input A,B),List.ofFn bits))
      (fun bits : Fin (CompanionInitialDraw.initialBits A B) → Bool =>
        CompanionArithmeticProposal.encodeSet (coordinateOrder A)
          (CompanionInitialDraw.draw A B bits).val.val) := by
  have h := (SameLaw.of_mapLaw_eq (initialDraw A B) (CompanionInitialDraw.draw A B)
    (initialDraw_law A B)).map (fun S => CompanionArithmeticProposal.encodeSet (coordinateOrder A) S.val.val)
  intro phi
  simpa only [initialProgram_eq A B hB] using h phi

end
end ContingencyTables.CompanionComputedInitial

end OAI
