import OAI.NumberTheory.DirichletL.Reflection.CubeSlotChoices

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (H : Ideal Eis) (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

include hmax hgood in
lemma cubeJoined_mark (x : CubeSlotChoices H L) (A : Ideal Eis) :
    (∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0)=
      ∏ i : x.1,if (x.2.2 i).val∣A then (1:ℂ) else 0 := by
  have hs := cube_shifted_mark H A (slotChoiceFamily L hmax hgood (cubeChoicesJoin H L x))
  have hl : cubeActiveSlots H (slotChoiceFamily L hmax hgood (cubeChoicesJoin H L x))=x.1 :=
    cubeChoicesJoin_label H L x
  rw [hl] at hs
  apply hs.trans
  rw [←Finset.prod_coe_sort x.1]
  apply Finset.prod_congr rfl
  intro i hi
  have he := slotChoiceSplit_active L x.1
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩)
    (fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩) i
  change (if ((slotChoiceSplit L x.1).symm _ i.val).val∣A then (1:ℂ) else 0)=_
  rw [he]

include hmax hgood in
lemma cubeJoined_completed (x : CubeSlotChoices H L) (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT Ψ W X
      (fun A => ∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0)=
    markedCompletedT Ψ W X
      (fun A => ∏ i : x.1,if (x.2.2 i).val∣A then (1:ℂ) else 0) := by
  congr 1
  funext A
  exact cubeJoined_mark H L hmax hgood x A

lemma cubeJoined_coefficient (x : CubeSlotChoices H L) (w : ∀ i,L i→ℂ) :
    (∏ i,w i (cubeChoicesJoin H L x i))=
      (∏ i : {i // i∉x.1},w i.val ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)*
      (∏ i : x.1,w i.val ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩) := by
  exact (slot_coefficient_split L x.1 w _ _).trans (mul_comm _ _)

def cubeAbsorbedCoefficient (w : ∀ i,L i→ℂ) (T : Finset σ) : ℂ :=
  ∑ b : ∀ i : {i // i∉T},cubeDivList H (L i.val),
    ∏ i : {i // i∉T},w i.val ⟨(b i).val,(Finset.mem_filter.mp (b i).property).1⟩

lemma cubeAbsorbedCoefficient_product (w : ∀ i,L i→ℂ) (T : Finset σ) :
    cubeAbsorbedCoefficient H L w T=
      ∏ i : {i // i∉T},∑ P : cubeDivList H (L i.val),w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ :=
  (Fintype.prod_sum (fun (i : {i // i∉T}) (P : cubeDivList H (L i.val)) =>
    w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩)).symm

include hmax hgood

theorem original_cube_shifted_tuple_source (w : ∀ i,L i→ℂ)
    (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT Ψ W X
      (fun A => ∏ i,if (p i).val∣H^3*A then (1:ℂ) else 0))=
    ∑ T : Finset σ,cubeAbsorbedCoefficient H L w T*
      ∑ a : ∀ i : T,cubeAwayList H (L i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT Ψ W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0) := by
  rw [←(cubeSlotChoiceEquiv H L).sum_comp]
  change (∑ x : CubeSlotChoices H L,(∏ i,w i (cubeChoicesJoin H L x i))*
    markedCompletedT Ψ W X (fun A => ∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0))=_
  simp_rw [cubeJoined_completed H L hmax hgood,cubeJoined_coefficient]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Fintype.sum_prod_type]
  simp only [cubeAbsorbedCoefficient,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end
end SevenEighths.InverseReflectedPhase

end OAI
