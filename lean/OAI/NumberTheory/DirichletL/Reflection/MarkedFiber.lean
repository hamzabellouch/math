import OAI.NumberTheory.DirichletL.Reflection.MarkedActiveSets
import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def joinedInactiveCoefficient (P : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) : ι⊕σ→ℂ :=
  Sum.elim (fun i => if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0)
    (fun i => (Ideal.absNorm (S.ideal i):ℂ)⁻¹)

lemma joined_inactive_weight (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (A : Finset (ι⊕σ)) :
    localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
      (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
        (Sum.elim j (fun _ => 0)) markedSumSlots) A =
    ∏ i∈(Finset.univ:Finset (ι⊕σ))\A, joinedInactiveCoefficient P S j i := by
  have ho : ∀ i, ringChar (Eis⧸(P.sum S).ideal i)≠2 := by
    intro i
    cases i with
    | inl i => exact hP i
    | inr i => exact hS i
  have hj' : ∀ i : ι⊕σ, Sum.elim j (fun _ => 0) i<6 := by
    intro i
    cases i with
    | inl i => exact hj i
    | inr i => norm_num
  rw [mixed_inactive_weight (P.sum S) ho _ hj']
  apply Finset.prod_congr (by ext i; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro i hi
  cases i <;> simp [markedSumSlots,joinedInactiveCoefficient,PrimeFamily.sum]
  rfl

theorem joined_inactive_three_blocks {α β : Type*} [Fintype α] [Fintype β]
    (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (e : α⊕β≃ι) (he : ∀ a, j (e (Sum.inl a))=1)
    (F : Finset (ι⊕σ)→ℂ) :
    (∑ A : Finset (ι⊕σ),
      localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
        (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
          (Sum.elim j (fun _ => 0)) markedSumSlots) A * F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,
        if j (e (Sum.inr b))=0 then 1-(Ideal.absNorm (P.ideal (e (Sum.inr b))):ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*F (markedActiveSet e B T) := by
  have hz : ∀ a, joinedInactiveCoefficient P S j (Sum.inl (e (Sum.inl a)))=0 := by
    intro a
    simp [joinedInactiveCoefficient,he a]
  have h := inactive_weight_three_blocks e (joinedInactiveCoefficient P S j) hz F
  refine Eq.trans ?_ h
  apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
  intro A hA
  congr 1
  exact joined_inactive_weight P S hP hS j hj A
end
end SevenEighths.InverseReflectedPhase

end OAI
