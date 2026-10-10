import Mathlib.Tactic.Abel
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.CanonicalMatrixTable
import OAI.Computability.PerfectCompleteness.Construction.FactoredFunctionsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.TriangularFolding

namespace OAI


namespace PerfectCompleteness.MatrixTriangularFolding

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)

theorem query_add (X Δ : CanonicalMatrixTable.Matrix (K := K) slots H) (d : Z → K)
    (hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x = d (other x)) :
    CanonicalMatrixTable.query slots H other (X + Δ) =
      TriangularFolding.translate d ∘ CanonicalMatrixTable.query slots H other X := by
  funext x
  apply Prod.ext
  · change X (EvaluationMatrix.evaluation H x) + Δ (EvaluationMatrix.evaluation H x) =
      X (EvaluationMatrix.evaluation H x) + d (other x)
    rw [← hΔ x]
    rfl
  · rfl

theorem response_add (X Δ : CanonicalMatrixTable.Matrix (K := K) slots H) (d : Z → K)
    (hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x = d (other x)) :
    CanonicalMatrixTable.response slots H other σ (X + Δ) =
      TriangularFolding.translate d (CanonicalMatrixTable.response slots H other σ X) := by
  unfold CanonicalMatrixTable.response
  rw [query_add slots H other X Δ d hΔ]
  exact KeyStrategy.response_postcomp_injective σ .left slots
    (CanonicalMatrixTable.query slots H other X) (TriangularFolding.translate d)
    (TriangularFolding.translate d).injective

theorem response_add_side (X Δ : CanonicalMatrixTable.Matrix (K := K) slots H) (d : Z → K)
    (hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x = d (other x)) :
    (CanonicalMatrixTable.response slots H other σ (X + Δ)).2 =
      (CanonicalMatrixTable.response slots H other σ X).2 := by
  rw [response_add slots H other σ X Δ d hΔ]
  rfl

theorem response_add_selected (X Δ : CanonicalMatrixTable.Matrix (K := K) slots H) (d : Z → K)
    (hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x = d (other x)) :
    (CanonicalMatrixTable.response slots H other σ (X + Δ)).1 =
      (CanonicalMatrixTable.response slots H other σ X).1 +
        d (CanonicalMatrixTable.response slots H other σ X).2 := by
  rw [response_add slots H other σ X Δ d hΔ]
  rfl

def sideFunctional (B : Submodule F2 (Assignment slots → F2))
    (hB : B ≤ FactoredFunctions.factoringSpace other) (z : Z) : Module.Dual F2 B :=
  if hz : z ∈ Set.range other then FactoredFunctions.evaluation hB ⟨z, hz⟩ else 0

theorem sideFunctional_at_image (B : Submodule F2 (Assignment slots → F2))
    (hB : B ≤ FactoredFunctions.factoringSpace other) (x : Assignment slots) :
    sideFunctional slots other B hB (other x) = EvaluationMatrix.evaluation B x := by
  have hx : other x ∈ Set.range other := ⟨x, rfl⟩
  rw [sideFunctional, dite_eq_left hx]
  ext b
  exact FactoredFunctions.evaluation_apply_of_eq hB ⟨other x, hx⟩ x rfl b

def liftCorrection (B : Submodule F2 (Assignment slots → F2)) (hBH : B ≤ H)
    (Δ : Module.Dual F2 B →ₗ[F2] K) : CanonicalMatrixTable.Matrix (K := K) slots H :=
  Δ.comp (Submodule.inclusion hBH).dualMap

def correction (B : Submodule F2 (Assignment slots → F2))
    (hB : B ≤ FactoredFunctions.factoringSpace other)
    (Δ : Module.Dual F2 B →ₗ[F2] K) (z : Z) : K :=
  Δ (sideFunctional slots other B hB z)

theorem evaluate_liftCorrection (B : Submodule F2 (Assignment slots → F2))
    (hBH : B ≤ H) (hB : B ≤ FactoredFunctions.factoringSpace other)
    (Δ : Module.Dual F2 B →ₗ[F2] K) (x : Assignment slots) :
    EvaluationMatrix.evaluate H (liftCorrection slots H B hBH Δ) x =
      correction slots other B hB Δ (other x) := by
  unfold correction
  rw [sideFunctional_at_image]
  rfl

theorem response_add_correction (B : Submodule F2 (Assignment slots → F2))
    (hBH : B ≤ H) (hB : B ≤ FactoredFunctions.factoringSpace other)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) (Δ : Module.Dual F2 B →ₗ[F2] K) :
    CanonicalMatrixTable.response slots H other σ (X + liftCorrection slots H B hBH Δ) =
      TriangularFolding.translate (correction slots other B hB Δ)
        (CanonicalMatrixTable.response slots H other σ X) :=
  response_add slots H other σ X _ _
    (evaluate_liftCorrection slots H other B hBH hB Δ)

theorem correction_rankOne (B : Submodule F2 (Assignment slots → F2))
    (hB : B ≤ FactoredFunctions.factoringSpace other) (a : K) (b : B) (z : Z) :
    correction slots other B hB ((Module.Dual.eval F2 B b).smulRight a) z =
      sideFunctional slots other B hB z b • a := rfl

end
end PerfectCompleteness.MatrixTriangularFolding



namespace PerfectCompleteness.RepresentativeMatrixTable

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

def Determined : Prop := ∀ b : W, ∀ x y : Assignment slots,
  other x = other y → b.val.val x = b.val.val y

theorem determined_comap (B : Submodule F2 (Assignment slots → F2))
    (hB : B ≤ FactoredFunctions.factoringSpace other) :
    Determined slots H other (B.comap H.subtype) := by
  intro b x y h
  exact hB b.property x y h

def sideEvaluation (z : Z) : Module.Dual F2 W :=
  if hz : z ∈ Set.range other then
    (EvaluationMatrix.evaluation H (Classical.choose hz)).comp W.subtype
  else 0

theorem sideEvaluation_at_image (hW : Determined slots H other W)
    (x : Assignment slots) :
    sideEvaluation slots H other W (other x) =
      (EvaluationMatrix.evaluation H x).comp W.subtype := by
  have hx : other x ∈ Set.range other := ⟨x, rfl⟩
  rw [sideEvaluation, dite_eq_left hx]
  ext b
  exact hW b _ x (Classical.choose_spec hx)

def correctionFunctional (z : Z) : Module.Dual F2 H :=
  (sideEvaluation slots H other W z).comp (MatrixRowQuotient.residualVector W s hs)

def representative (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    CanonicalMatrixTable.Matrix (K := K) slots H :=
  MatrixRowQuotient.liftMatrix W s (MatrixRowQuotient.projectMatrix W X)

def response (X : CanonicalMatrixTable.Matrix (K := K) slots H) : K × Z :=
  CanonicalMatrixTable.response slots H other σ (representative slots H W s X)

def partialTable (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (X : Module.Dual F2 (H ⧸ W) →ₗ[F2] K) : Option (K × Z) :=
  if useful X then
    some (CanonicalMatrixTable.response slots H other σ (MatrixRowQuotient.liftMatrix W s X))
  else none

theorem raw_response (hW : Determined slots H other W)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    CanonicalMatrixTable.response slots H other σ X =
      TriangularFolding.translate (fun z => X (correctionFunctional slots H other W s hs z))
        (response slots H other σ W s X) := by
  let Δ := (X.comp (MatrixRowQuotient.residualVector W s hs).dualMap).comp W.subtype.dualMap
  have hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x =
      X (correctionFunctional slots H other W s hs (other x)) := by
    intro x
    unfold correctionFunctional
    rw [sideEvaluation_at_image slots H other W hW x]
    rfl
  have hsum : representative slots H W s X + Δ = X := by
    have he := MatrixRowQuotient.residual_factorization W s hs X
    change X - representative slots H W s X = Δ at he
    rw [← he]
    abel
  have hr := MatrixTriangularFolding.response_add slots H other σ
    (representative slots H W s X) Δ
    (fun z => X (correctionFunctional slots H other W s hs z)) hΔ
  rw [hsum] at hr
  exact hr

def normalizeOutput (X : CanonicalMatrixTable.Matrix (K := K) slots H) (y : K × Z) : K × Z :=
  (y.1 - X (correctionFunctional slots H other W s hs y.2), y.2)

theorem response_eq_normalize (hW : Determined slots H other W)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    response slots H other σ W s X =
      normalizeOutput slots H other W s hs X (CanonicalMatrixTable.response slots H other σ X) := by
  rw [raw_response slots H other σ W s hs hW X]
  apply Prod.ext
  · change (response slots H other σ W s X).1 =
      (response slots H other σ W s X).1 +
        X (correctionFunctional slots H other W s hs (response slots H other σ W s X).2) -
        X (correctionFunctional slots H other W s hs (response slots H other σ W s X).2)
    abel
  · rfl

def normalizeQuotient (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H)
    (y : DirectionQuotient.Space a × Z) : DirectionQuotient.Space a × Z :=
  (y.1 - DirectionQuotient.proj a
    (X (correctionFunctional slots H other W s hs y.2)), y.2)

theorem project_normalize_shift (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H)
    (h : H) (y : K × Z) :
    DirectionQuotient.projectWithSide a
      (normalizeOutput slots H other W s hs (EvaluationMatrix.shift H X a h) y) =
      normalizeQuotient slots H other W s hs a X (DirectionQuotient.projectWithSide a y) := by
  apply Prod.ext
  · change DirectionQuotient.proj a
        (y.1 - (X (correctionFunctional slots H other W s hs y.2) +
          correctionFunctional slots H other W s hs y.2 h • a)) =
      DirectionQuotient.proj a y.1 - DirectionQuotient.proj a
        (X (correctionFunctional slots H other W s hs y.2))
    have ha : DirectionQuotient.proj a a = 0 :=
      (DirectionQuotient.proj_eq_zero_iff a a).mpr (Or.inr rfl)
    simp only [map_sub, map_add, map_smul, ha, smul_zero, add_zero]
  · rfl

theorem accepted_response_in_fiber (hW : Determined slots H other W)
    (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H)
    (hacc : CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h)) :
    DirectionQuotient.projectWithSide a
      (response slots H other σ W s (EvaluationMatrix.shift H X a h)) =
      normalizeQuotient slots H other W s hs a X
        (KeyStrategy.response σ .right slots (CanonicalMatrixTable.rightQuery slots H other a X)) := by
  rw [response_eq_normalize slots H other σ W s hs hW]
  rw [project_normalize_shift]
  rw [CanonicalMatrixTable.accepted_response_in_fiber slots H other σ a X h hacc]

include hs in
theorem card_accepted_responses_le_two [Finite K] [Finite Z]
    (hW : Determined slots H other W) (a : K) (ha : a ≠ 0)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    Nat.card {y : K × Z // ∃ h : H,
      CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
      response slots H other σ W s (EvaluationMatrix.shift H X a h) = y} ≤ 2 := by
  let z := normalizeQuotient slots H other W s hs a X
    (KeyStrategy.response σ .right slots (CanonicalMatrixTable.rightQuery slots H other a X))
  let intoFiber :
      {y : K × Z // ∃ h : H,
        CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
        response slots H other σ W s (EvaluationMatrix.shift H X a h) = y} →
      {y : K × Z // DirectionQuotient.projectWithSide a y = z} := fun y =>
    ⟨y.val, by
      obtain ⟨h, hacc, hy⟩ := y.property
      rw [← hy]
      exact accepted_response_in_fiber slots H other σ W s hs hW a X h hacc⟩
  calc
    _ ≤ Nat.card {y : K × Z // DirectionQuotient.projectWithSide a y = z} :=
      Nat.card_le_card_of_injective intoFiber (by
        intro y y' he
        exact Subtype.ext (congrArg
          (fun v : {y : K × Z // DirectionQuotient.projectWithSide a y = z} => v.val) he))
    _ = 2 := DirectionQuotient.card_projectWithSide_fiber a ha z

end
end PerfectCompleteness.RepresentativeMatrixTable

end OAI
