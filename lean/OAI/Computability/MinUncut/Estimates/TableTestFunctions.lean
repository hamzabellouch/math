import Mathlib
import OAI.Computability.MinUncut.Estimates.ActualBoxBound
import OAI.Computability.MinUncut.Estimates.FourthTest
import OAI.Computability.MinUncut.Estimates.TableLawPacking

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

def disagreement (b c : Bool) : ℝ := if b=c then 0 else 1

lemma disagreement_range (b c : Bool) : 0≤disagreement b c ∧ disagreement b c≤1 := by
  unfold disagreement
  split <;> norm_num

def firstTable (f : FoldedProof A) (B : FaceArray A m n) (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => t (false,labelCode B a)))
    (f.answer (fun a => t (true,labelCode B a)))

def secondTable (f : FoldedProof A) (B C : FaceArray A m n) (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => t (true,labelCode B a)))
    (f.answer (fun a => t (true,labelCode C a)))

def thirdTable (f : FoldedProof A) (B : FaceArray A m n) (z : Code m n)
    (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => Function.update (fun z => t (true,z)) z true (labelCode B a)))
    (f.answer (fun a => Function.update (fun z => t (true,z)) z false (labelCode B a)))

def fourthTable (f : FoldedProof A) (g : FoldedProof A') (B : FaceArray A m n)
    (C : FaceArray A' m n) (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => t (true,labelCode B a)))
    (g.answer (fun a => t (true,labelCode C a)))

omit [Fintype A] in
lemma firstTable_source (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    firstTable f B (sourceTable σ η c g l)=firstFailure f B σ η c g l := rfl

omit [Fintype A] in
lemma secondTable_source (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    secondTable f B C (sourceTable σ η c g l)=secondFailure f B C σ η c (g,l) := rfl

omit [Fintype A] in
lemma thirdTable_source (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    thirdTable f B z (sourceTable σ η c g l)=thirdFailure f B η (c+σ•g) l z := rfl

omit [Fintype A] [Fintype A'] in
lemma fourthTable_source (f : FoldedProof A) (g : FoldedProof A') (B : FaceArray A m n)
    (C : FaceArray A' m n) (σ η : ℝ) (c h : Point m n → ℝ) (l : Code m n → ℝ) :
    fourthTable f g B C (sourceTable σ η c h l)=comparisonFailure f g B C σ η c (h,l) := rfl

omit [Fintype A] in
lemma firstTable_integral (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    (∫ c, firstRejection f B σ η c ∂gauss (Point m n))=
      ∫ x, firstTable f B (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) :=
  table_integral_pack σ η (firstTable f B) (fun _ => disagreement_range _ _)

omit [Fintype A] in
lemma secondTable_integral (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ) :
    (∫ c, secondRejection f B C σ η c ∂gauss (Point m n))=
      ∫ x, secondTable f B C (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) :=
  table_integral_product σ η (secondTable f B C) (fun _ => disagreement_range _ _)

omit [Fintype A] in
lemma thirdTable_integral (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    (∫ c, thirdRejection f B σ η c ∂gauss (Point m n))=
      𝔼 z : Code m n, ∫ x, thirdTable f B z (thresholdTable (scoreFamily σ η) x)
        ∂gaussianLaw (TestCoordinates m n) := by
  unfold thirdRejection
  simp only [Fintype.expect_eq_sum_div_card,integral_div]
  simp_rw [← thirdTable_source]
  rw [integral_finsetSum _ (fun z _ => sourceTest_outer_integrable σ η (thirdTable f B z)
    (fun _ => disagreement_range _ _))]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact table_integral_pack σ η (thirdTable f B z) (fun _ => disagreement_range _ _)

omit [Fintype A] [Fintype A'] in
lemma fourthTable_integral (f : FoldedProof A) (g : FoldedProof A') (B : FaceArray A m n)
    (C : FaceArray A' m n) (σ η : ℝ) :
    (∫ c, comparisonRejection f g B C σ η c ∂gauss (Point m n))=
      ∫ x, fourthTable f g B C (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) :=
  table_integral_product σ η (fourthTable f g B C) (fun _ => disagreement_range _ _)

end MinUncut.FiniteGaussian

end
end

end OAI
