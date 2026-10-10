import Mathlib
import OAI.Computability.MinUncut.Graphs.HonestComparisons
import OAI.Computability.MinUncut.Estimates.ComparisonSoundness

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma secondError_evaluation_le (a : A) (hn : 0 < n) (hm : 0 < m)
    {σ η δ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hρ : δ^2/(m:ℝ) ≤ 1) :
    secondError (m := m) (n := n) (evaluationProof a) (δ^2/(m:ℝ)) σ η ≤ 8*δ+4*η := by
  have hρ0 : 0 ≤ δ^2/(m:ℝ) := by positivity
  have hB (B : FaceArray A m n) :
      (𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
        (∫ c, secondRejection (evaluationProof a) B C σ η c ∂gauss (Point m n))) ≤ 8*δ+4*η := by
    calc
      _ ≤ 𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
          (4*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖+4*η) := by
        apply Finset.expect_le_expect
        intro C _
        exact mul_le_mul_of_nonneg_left (secondRejection_evaluation_le a B C hn hσ hσ1 hη)
          (density_nonneg hρ0 hρ B C)
      _ = 4*(𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
          ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖)+4*η := by
        simp_rw [mul_add,mul_left_comm (density _ B _),Finset.expect_add_distrib,
          ← Finset.mul_expect]
        rw [← Finset.expect_mul,density_mean,one_mul]
      _ ≤ _ := by have h := noise_vector_le a B hn hm hδ hρ; linarith
  exact (Finset.expect_le_expect (fun B _ => hB B)).trans_eq (Fintype.expect_const _)

lemma honest_first_budget (a : A) (hn : 0 < n) {J : ℝ} (hJ : 1 ≤ J) :
    firstError (m := m) (n := n) (evaluationProof a) (sourceSigma J) (sourceEta J) ≤
      10*sourceSigma J := by
  have h := firstError_evaluation_le (m := m) a hn (sourceSigma_pos hJ).le (sourceEta_pos hJ).le
  have := sourceEta_le_sigma hJ
  have := sourceSigma_pos hJ
  linarith

lemma honest_second_budget (a : A) (hn : 0 < n) (hm : 0 < m) {J : ℝ} (hJ : 1 ≤ J) :
    secondError (m := m) (n := n) (evaluationProof a) ((sourceEta J)^2/(m:ℝ))
      (sourceSigma J) (sourceEta J) ≤ 10*(sourceEta J+sourceEta J) := by
  have h := secondError_evaluation_le a hn hm (sourceSigma_pos hJ).le (sourceSigma_le_one hJ)
    (sourceEta_pos hJ).le (sourceEta_pos hJ).le (source_row_rate hJ hm).2.1
  have := sourceEta_pos hJ
  linarith
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B] {m n : ℕ}

omit [Fintype A] [Fintype B] in
lemma labelCode_pullback (π : A →ᵃ[F₂] B) (C : FaceArray B m n) (a : A) :
    labelCode (pullbackFaces π C) a=labelCode C (π a) := by
  apply Subtype.ext
  funext x
  rfl

omit [Fintype A] in
lemma fourthError_evaluation (π : A →ᵃ[F₂] B) (a : A) (σ η : ℝ) :
    fourthError (m := m) (n := n) π (evaluationProof a) (evaluationProof (π a)) σ η=0 := by
  simp only [fourthError,comparisonRejection,comparisonFailure,evaluationProof,pullQuery,
    labelCode_pullback,ite_true,integral_zero,Finset.expect_const_zero]

lemma fourthError_le_one (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B) (σ η : ℝ) :
    fourthError (m := m) (n := n) π f g σ η ≤ 1 := by
  have hC (C : FaceArray B m n) :
      (∫ c, comparisonRejection f g (pullbackFaces π C) C σ η c ∂gauss (Point m n)) ≤ 1 := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (comparisonRejection_integrable f g _ _ σ η) (integrable_const 1)
        (fun c => (comparisonRejection_range f g _ _ σ η c).2)
  exact (Finset.expect_le_expect (fun C _ => hC C)).trans_eq (Fintype.expect_const _)
end MinUncut.Inner
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

def honestProof (s : Name → F₂) : ProofFamily Name I where
  first U := evaluationProof (firstLabel s U)
  second Q := evaluationProof (secondLabel s Q)

lemma honest_fourth_point (s : Name → F₂) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (m n : ℕ) (σ η : ℝ) :
    (honestProof (I := I) s).fourthTotal (m := m) (n := n) σ η U h pos ≤
      ∑ i, if Satisfied s (U i) then (0:ℝ) else 1 := by
  by_cases hall : ∀ i, Satisfied s (U i)
  · have hp := honest_projection s U hall h pos
    simp only [ProofFamily.fourthTotal,honestProof]
    rw [← hp,fourthError_evaluation]
    simp only [hall,ite_eq_left,Finset.sum_const_zero,le_refl]
  · obtain ⟨i,hi⟩ := not_forall.mp hall
    have hs : (1:ℝ) ≤ ∑ j, if Satisfied s (U j) then (0:ℝ) else 1 := by
      simpa only [hi,ite_false] using
        (Finset.single_le_sum (a := i) (fun j _ => by split <;> norm_num : ∀ j ∈ Finset.univ, 0 ≤ if Satisfied s (U j) then (0:ℝ) else 1) (Finset.mem_univ i))
    exact (fourthError_le_one (projection U h pos) _ _ σ η).trans hs

lemma failure_fraction (equations : S → Equation Name) (s : Name → F₂) :
    (𝔼 a : S, if Satisfied s (equations a) then (0:ℝ) else 1)=1-equationFraction equations s := by
  have he (a : S) : (if Satisfied s (equations a) then (0:ℝ) else 1)=
      1-(if Satisfied s (equations a) then (1:ℝ) else 0) := by split <;> norm_num
  simp_rw [he,Finset.expect_sub_distrib,Fintype.expect_const,Fintype.expect_eq_sum_div_card]
  rfl

lemma honest_fourth_mean (equations : S → Equation Name) (s : Name → F₂) {k : ℕ}
    (hk : k ≤ Fintype.card I) (m n : ℕ) (σ η : ℝ) :
    edgeMean equations k ((honestProof (I := I) s).fourthTotal (m := m) (n := n) σ η) ≤
      (Fintype.card I:ℝ)*(1-equationFraction equations s) := by
  apply (edgeMean_mono equations k (fun U h p => honest_fourth_point s U h p m n σ η)).trans_eq
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  have hcoord (i : I) : (𝔼 a : I → S, if Satisfied s (equations (a i)) then (0:ℝ) else 1)=
      1-equationFraction equations s :=
    (Subbox.expect_coordinate (B := fun _ : I => S) i
      (fun b => if Satisfied s (equations b) then (0:ℝ) else 1)).trans (failure_fraction equations s)
  simp only [edgeMean,Fintype.expect_const,Finset.expect_sum_comm,hcoord,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]

attribute [local irreducible] firstError secondError thirdError fourthError edgeMean

lemma honest_errors_le {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (equations : S → Equation Name) (s : Name → F₂) (hcard : Fintype.card I=O.t)
    (hs : (O.t:ℝ)*(1-equationFraction equations s) ≤ O.b4) (j : Test) :
    (honestProof (I := I) s).testErrors P O equations j ≤ budgets P O j := by
  have hk : O.k ≤ Fintype.card I := by simpa only [hcard] using O.hk
  have hn : 0 < P.n := by have := P.hn; omega
  have hm : 0 < P.m := by have := P.hm; omega
  cases j <;> simp only [ProofFamily.testErrors,budgets,honestProof]
  · apply (edgeMean_mono equations O.k (fun U h pos => honest_first_budget (V := SecondAlphabet (secondQuestion U h pos)) (secondLabel s (secondQuestion U h pos)) hn hJ)).trans_eq
    exact edgeMean_const equations hk _
  · apply (edgeMean_mono equations O.k (fun U h pos => honest_second_budget (V := SecondAlphabet (secondQuestion U h pos)) (secondLabel s (secondQuestion U h pos)) hn hm hJ)).trans_eq
    exact edgeMean_const equations hk _
  · apply le_of_eq
    simp only [thirdError_evaluation]
    exact edgeMean_const equations hk _
  · exact (honest_fourth_mean equations s hk P.m P.n (sourceSigma J) (sourceEta J)).trans
      (by simpa only [hcard] using hs)

lemma honest_cost_le {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (equations : S → Equation Name) (s : Name → F₂) (hcard : Fintype.card I=O.t)
    (hs : (O.t:ℝ)*(1-equationFraction equations s) ≤ O.b4) :
    (honestProof (I := I) s).cost P O equations ≤ 4 := by
  have hh : (honestProof (I := I) s).cost P O equations ≤ ∑ _ : Test, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact (div_le_one (budgets_pos hJ P O j)).mpr (honest_errors_le hJ P O equations s hcard hs j)
  have hc : (∑ _ : Test, (1:ℝ))=4 := by
    have hc : Fintype.card Test=4 := by decide
    simp [hc]
  exact hh.trans_eq hc
end MinUncut.Outer

end

end OAI
