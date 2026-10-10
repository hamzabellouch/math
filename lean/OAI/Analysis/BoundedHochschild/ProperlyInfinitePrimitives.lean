import OAI.Analysis.BoundedHochschild.CountableMatrixHomotopy
import OAI.Analysis.BoundedHochschild.ClassicalVanishingReduction

namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem properlyInfinite_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) {n : ℕ} (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  cases subsingleton_or_nontrivial M with
  | inl hM =>
      let := hM
      exact ⟨0, fun _ => Subsingleton.elim _ _⟩
  | inr hM =>
      let := hM
      obtain ⟨c, hi, ho, ht⟩ := exists_countable_isometries e hno
      obtain ⟨b, hb⟩ := primitive_of_countableMatrixAverage e hno c hi ho ht f hf
      have hH := countableMatrixBarOperator_cocycle e c hi ho f hf
      refine ⟨b + countableMatrixBarOperator e c hi ho f, fun x => ?_⟩
      have hx : differentialValue (countableMatrixBarOperator e c hi ho f) x =
          f x - countableMatrixAverage e c hi ho f x := by
        simpa only [differential_apply, sub_apply] using
          congrArg (fun F : Cochain M (n + 2) => F x) hH
      rw [differentialValue_add, hb, hx]
      abel

theorem properlyInfiniteVanishingInput : ProperlyInfiniteVanishingInput.{u} := by
  intro N hN hPO hSO hW hno n f hf
  let := hW
  obtain ⟨Y, hY, hYS, hYC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := N)
  let := hY
  let := hYS
  let := hYC
  exact properlyInfinite_primitive e hno f hf

theorem classicalVanishingInput : ClassicalVanishingInput.{u} :=
  classicalVanishing_of_properlyInfinite properlyInfiniteVanishingInput

end BoundedHochschild.KadisonRingrose

end

end OAI
