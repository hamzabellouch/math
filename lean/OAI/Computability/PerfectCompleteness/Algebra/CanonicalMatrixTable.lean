import OAI.Computability.PerfectCompleteness.Algebra.EvaluationMatrix
import OAI.Computability.PerfectCompleteness.Foundations.LinearEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas

namespace OAI

section

namespace PerfectCompleteness.CanonicalMatrixTable

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)

abbrev Matrix := Module.Dual F2 H →ₗ[F2] K

def query (X : Matrix (K := K) slots H) : Assignment slots → K × Z :=
  EvaluationMatrix.joint H other X

def response (X : Matrix (K := K) slots H) : K × Z :=
  KeyStrategy.response σ .left slots (query slots H other X)

def partialTable (useful : Matrix (K := K) slots H → Prop) (X : Matrix (K := K) slots H) : Option (K × Z) :=
  if useful X then some (response slots H other σ X) else none

theorem response_realized (X : Matrix (K := K) slots H) :
    ∃ x : Assignment slots,
      EvaluationMatrix.evaluate H X x = (response slots H other σ X).1 ∧
      other x = (response slots H other σ X).2 := by
  obtain ⟨x, hx⟩ := KeyStrategy.response_mem_range σ .left slots (query slots H other X)
  exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

def rightQuery (a : K) (X : Matrix (K := K) slots H) : Assignment slots → DirectionQuotient.Space a × Z :=
  DirectionQuotient.projectWithSide a ∘ query slots H other X

theorem rightQuery_shift (a : K) (X : Matrix (K := K) slots H) (h : H) :
    rightQuery slots H other a (EvaluationMatrix.shift H X a h) =
      rightQuery slots H other a X := by
  funext x
  apply Prod.ext
  · change DirectionQuotient.proj a
        (EvaluationMatrix.evaluate H X x + h.val x • a) =
      DirectionQuotient.proj a (EvaluationMatrix.evaluate H X x)
    rw [map_add, map_smul]
    have ha : DirectionQuotient.proj a a = 0 :=
      (DirectionQuotient.proj_eq_zero_iff a a).mpr (Or.inr rfl)
    simp [ha]
  · rfl

theorem rightResponse_shift (a : K) (X : Matrix (K := K) slots H) (h : H) :
    KeyStrategy.response σ .right slots
        (rightQuery slots H other a (EvaluationMatrix.shift H X a h)) =
      KeyStrategy.response σ .right slots (rightQuery slots H other a X) := by
  rw [rightQuery_shift]

def Accepts (a : K) (X : Matrix (K := K) slots H) : Prop :=
  CanonicalEdges.coarsen slots (query slots H other X) (DirectionQuotient.projectWithSide a)
    (KeyStrategy.label σ .left slots (query slots H other X)) =
      KeyStrategy.label σ .right slots (rightQuery slots H other a X)

theorem accepts_iff (a : K) (X : Matrix (K := K) slots H) :
    Accepts slots H other σ a X ↔
      DirectionQuotient.projectWithSide a (response slots H other σ X) =
        KeyStrategy.response σ .right slots (rightQuery slots H other a X) :=
  CanonicalEdges.coarsen_eq_iff slots (query slots H other X)
    (DirectionQuotient.projectWithSide a) _ _

theorem accepted_response_in_fiber (a : K) (X : Matrix (K := K) slots H) (h : H)
    (hacc : Accepts slots H other σ a (EvaluationMatrix.shift H X a h)) :
    DirectionQuotient.projectWithSide a
        (response slots H other σ (EvaluationMatrix.shift H X a h)) =
      KeyStrategy.response σ .right slots (rightQuery slots H other a X) := by
  have h := (accepts_iff slots H other σ a (EvaluationMatrix.shift H X a h)).mp hacc
  rwa [rightResponse_shift] at h

theorem card_accepted_responses_le_two [Finite K] [Finite Z]
    (a : K) (ha : a ≠ 0) (X : Matrix (K := K) slots H) :
    Nat.card {y : K × Z // ∃ h : H,
      Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
      response slots H other σ (EvaluationMatrix.shift H X a h) = y} ≤ 2 := by
  let z := KeyStrategy.response σ .right slots (rightQuery slots H other a X)
  let intoFiber :
      {y : K × Z // ∃ h : H,
        Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
        response slots H other σ (EvaluationMatrix.shift H X a h) = y} →
      {y : K × Z // DirectionQuotient.projectWithSide a y = z} := fun y =>
    ⟨y.val, by
      obtain ⟨h, hacc, hy⟩ := y.property
      rw [← hy]
      exact accepted_response_in_fiber slots H other σ a X h hacc⟩
  calc
    _ ≤ Nat.card {y : K × Z // DirectionQuotient.projectWithSide a y = z} :=
      Nat.card_le_card_of_injective intoFiber (by
        intro y y' he
        exact Subtype.ext (congrArg
          (fun v : {y : K × Z // DirectionQuotient.projectWithSide a y = z} => v.val) he))
    _ = 2 := DirectionQuotient.card_projectWithSide_fiber a ha z

end
end PerfectCompleteness.CanonicalMatrixTable

end

end OAI
