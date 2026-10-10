import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

abbrev Sample {α : Type*} (U : Finset α) (h : ℕ) := Fin h ↪ U

noncomputable def goodSamples {α : Type*} (U W : Finset α) (h : ℕ) : Finset (Sample U h) := by
  classical
  exact Finset.univ.filter (fun e => ∀ i, (e i).val ∈ W)

noncomputable def goodSampleEquiv {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ) :
    (goodSamples U W h) ≃ Sample W h where
  toFun e :=
    { toFun := fun i => ⟨(e.val i).val,(Finset.mem_filter.mp e.property).2 i⟩
      inj' := by
        intro i j he
        apply e.val.injective
        exact Subtype.ext (congrArg (fun x : W => x.val) he) }
  invFun f :=
    ⟨{ toFun := fun i => ⟨(f i).val,hWU (f i).property⟩
       inj' := by
         intro i j he
         apply f.injective
         exact Subtype.ext (congrArg (fun x : U => x.val) he) },by
       classical
       apply Finset.mem_filter.mpr
       exact ⟨Finset.mem_univ _,fun i => (f i).property⟩⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl

theorem sample_card {α : Type*} (U : Finset α) (h : ℕ) :
    Fintype.card (Sample U h) = U.card.descFactorial h := by
  classical
  simp only [Sample,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_coe]

theorem goodSamples_card {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ) :
    (goodSamples U W h).card = W.card.descFactorial h := by
  classical
  have hh := Fintype.card_congr (goodSampleEquiv U W hWU h)
  simpa only [Fintype.card_coe,sample_card] using hh

noncomputable def sampleFrequency {α : Type*} (U W : Finset α) (h : ℕ) : ℝ :=
  ((goodSamples U W h).card : ℝ)/(Fintype.card (Sample U h) : ℝ)

theorem sampleFrequency_eq {α : Type*} (U W : Finset α) (hWU : W ⊆ U) (h : ℕ) :
    sampleFrequency U W h = (W.card.descFactorial h : ℝ)/(U.card.descFactorial h : ℝ) := by
  rw [sampleFrequency,goodSamples_card U W hWU,sample_card]

end ErdosInverseSampling

end

end Erdos970

end OAI
