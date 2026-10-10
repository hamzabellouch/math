import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.IndependentSetElements

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
open scoped BigOperators
noncomputable section
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma independent_map [DecidableEq V] [DecidableEq W]
    (u : W → M) (e : V ↪ W) (s : Finset V) :
    IsIndependent Ω u (s.map e) ↔ IsIndependent Ω (u∘e) s := by
  simp [IsIndependent]

lemma independentTerm_map [DecidableEq V] [DecidableEq W]
    (u : W → M) (e : V ↪ W) (s : Finset V) (k : ℕ) :
    independentTerm v Ω u k (s.map e)=independentTerm v Ω (u∘e) k s := by
  simp only [independentTerm,independent_map,Finset.card_map,setMonomial,Finset.sum_map]
  rfl

lemma independentElement_reindex [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (u : W → M) (e : V ≃ W) (k : ℕ) :
    independentElement v Ω u k=independentElement v Ω (u∘e) k := by
  unfold independentElement
  rw [←Equiv.sum_comp e.finsetCongr]
  apply Finset.sum_congr rfl
  intro s _
  exact independentTerm_map v Ω u e.toEmbedding s k

def embeddingSumCompl (e : V ↪ W) : V ⊕ {w : W // w∉Set.range e} ≃ W :=
  ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (fun w=>w∈Set.range e))
@[simp] lemma embeddingSumCompl_inl (e : V ↪ W) (x : V) :
    embeddingSumCompl e (.inl x)=e x := rfl
@[simp] lemma embeddingSumCompl_inr (e : V ↪ W) (x : {w : W // w∉Set.range e}) :
    embeddingSumCompl e (.inr x)=x.val := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
