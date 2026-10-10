import OAI.NumberTheory.DirichletL.Reflection.MarkedInactive

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]

def joinedFiberEquiv (e : α⊕β≃γ) : α⊕(β⊕σ)≃γ⊕σ :=
  (Equiv.sumAssoc α β σ).symm.trans (Equiv.sumCongr e (Equiv.refl σ))

def markedActiveSet (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) : Finset (γ⊕σ) :=
  residualActivePrimes (joinedFiberEquiv (σ:=σ) e) ∪
    (B.disjSum T).image (fun x => joinedFiberEquiv e (Sum.inr x))

lemma inactive_product_disjSum (z : β⊕σ→ℂ) (B : Finset β) (T : Finset σ) :
    (∏ x∈(Finset.univ:Finset (β⊕σ))\B.disjSum T,z x)=
    (∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl b))*
    ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t) := by
  have hs : (Finset.univ:Finset (β⊕σ))\B.disjSum T=
      ((Finset.univ:Finset β)\B).disjSum ((Finset.univ:Finset σ)\T) := by
    ext x
    cases x <;> simp
  rw [hs,Finset.prod_disjSum]

theorem inactive_weight_three_blocks (e : α⊕β≃γ) (z : γ⊕σ→ℂ)
    (hz : ∀ a, z (Sum.inl (e (Sum.inl a)))=0) (F : Finset (γ⊕σ)→ℂ) :
    (∑ A : Finset (γ⊕σ), (∏ x∈(Finset.univ:Finset (γ⊕σ))\A,z x)*F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl (e (Sum.inr b))))*
        ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t))*F (markedActiveSet e B T) := by
  have he := inactive_weight_nonresidual_subsets (joinedFiberEquiv e) z hz F
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro x hx
    rfl
  · rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv Finset.sumEquiv.toEquiv
    intro B
    have hB : B=B.toLeft.disjSum B.toRight := (Finset.toLeft_disjSum_toRight).symm
    conv_lhs => rw [hB]
    congr 1
    · refine Eq.trans ?_ (inactive_product_disjSum (fun x => z (joinedFiberEquiv e (Sum.inr x))) B.toLeft B.toRight)
      apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
      intro x hx
      rfl
    · apply congrArg F
      ext x
      simp only [markedActiveSet,Finset.sumEquiv,Equiv.coe_fn_mk,Finset.mem_union,Finset.mem_image]
end
end SevenEighths.InverseReflectedPhase

end OAI
