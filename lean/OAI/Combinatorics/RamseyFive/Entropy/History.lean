import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UniformHistory

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance historySupportIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _
omit [Nonempty A] in
lemma history_support (p : Law (((B×A)⊕T)→β)) (n : ℕ)
    (h : BlockHistory B A T β n) (x : ((B×A)⊕T)→β)
    (hx : 0<historyPosterior p h x) : 0<p x := by
  induction n generalizing p with
  | zero => exact hx
  | succ n ih =>
    exact fiber_reveal_support p (representativeSet h.1) h.2.1 x
      (ih _ h.2.2 hx)
lemma preRound_positive (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) (z : (κ×BlockHistory B A T β n)×(B→A))
    (hz : 0<preRoundLaw μ p S n z) :
    0<μ z.1.1 ∧ 0<historyLaw (p z.1.1) (S z.1.1) n z.1.2 ∧
      0<freshBlockLaw (historyUnused (S z.1.1) z.1.2) z.2 := by
  change 0<(μ z.1.1*historyLaw (p z.1.1) (S z.1.1) n z.1.2)*
    freshBlockLaw (historyUnused (S z.1.1) z.1.2) z.2 at hz
  have h1:=(mul_pos_iff.mp hz).resolve_right (fun h=>
    ((freshBlockLaw (historyUnused (S z.1.1) z.1.2)).nonneg z.2).not_gt h.2)
  have h2:=(mul_pos_iff.mp h1.1).resolve_right (fun h=>(μ.nonneg _).not_gt h.1)
  exact ⟨h2.1,h2.2,h1.2⟩
lemma marginal_support_subset {I γ : Type*} [Fintype I] [Fintype γ]
    (p : Law (I→γ)) (D : I→Finset γ) (hp : InDomains p D) (i : I) :
    support (map p (fun x=>x i))⊆D i := by
  intro b hb
  obtain ⟨x,hx,rfl⟩:=map_positive p (fun x=>x i) b ((mem_support _ _).mp hb)
  exact hp x hx i
end
end SharpRamseyFive.FiniteEntropy

end OAI
