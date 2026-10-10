import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UniformHistory

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ Ω Θ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Fintype Ω] [Fintype Θ] [Nonempty A]
local instance historyPrivateIDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

lemma originalHistory_mean (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ)
    (F : ((κ×BlockHistory B A T β n)×(B→A))→(((B×A)⊕T)→β)→ℝ) :
    mean (originalHistoryLaw P context tuple S n)
      (fun z=>F (((context z.1,z.2.1),z.2.2)) (tuple z.1))=
    mean (preRoundLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n)
      (fun z=>mean (historyPosterior (fiber (pair P context tuple) z.1.1) z.1.2) (F z)) := by
  have h:=congrArg (fun p=>mean p (fun z=>F z.1 z.2))
    (originalHistory_joint P context tuple S n)
  simpa only [mean_map,preRoundTupleLaw,mean_adaptive] using h

lemma originalHistory_private_mean (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ)
    (Γ : ((κ×BlockHistory B A T β n)×(B→A))→Type) [∀h,Fintype (Γ h)]
    (privateLaw : ∀h,Law (Γ h)) (tables : Law Θ)
    (F : (h : (κ×BlockHistory B A T β n)×(B→A))→(((B×A)⊕T)→β)→Γ h→Θ→ℝ) :
    let H := fun z : Ω×(BlockHistory B A T β n×(B→A))=>((context z.1,z.2.1),z.2.2)
    mean (adaptiveLaw (sigmaLaw (originalHistoryLaw P context tuple S n)
      (fun z=>privateLaw (H z))) (fun _=>tables))
      (fun z=>F (H z.1.1) (tuple z.1.1.1) z.1.2 z.2)=
    mean (preRoundLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n)
      (fun h=>mean (historyPosterior (fiber (pair P context tuple) h.1.1) h.1.2)
        (fun x=>mean (privateLaw h) (fun v=>mean tables (F h x v)))) := by
  dsimp only
  rw [mean_adaptive,mean_sigma]
  convert originalHistory_mean P context tuple S n
    (fun h x=>mean (privateLaw h) (fun v=>mean tables (F h x v))) using 1
end
end SharpRamseyFive.FiniteEntropy

end OAI
