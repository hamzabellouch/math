import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.WindowPosterior

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {Ω κ α β : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance srFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
namespace SelectedStream
lemma reindex_deficit (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (ctx : Ω→κ) (e : Fin l↪o Fin n) (D : κ→Fin n→Finset β) (J : ℝ)
    (hD : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i)
    (hcap : ∀c,0 < map S.law ctx c→∀i,Real.log (D c i).card≤J) :
    mean (first (pair (S.reindex e).law ctx (S.reindex e).tuple))
      (fun c=>(l:ℝ)*J-entropy (fiber (pair (S.reindex e).law ctx (S.reindex e).tuple) c))≤
    mean (first (pair S.law ctx S.tuple))
      (fun c=>(n:ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c)) := by
  have H:=selectByContext_deficit (pair S.law ctx S.tuple) (fun _=>Finset.univ)
    (fun _=>e.toEmbedding) J (fun _ _ _=>Finset.mem_univ _)
    (fun _ _=>fixedOutside_univ _) (by
      intro c hc i hi
      exact (pair_fiber_domains S.law ctx S.tuple D hD c hc).entropy_cap J
        (hcap c (by simpa only [first_pair] using hc)) i)
  rw [selected_pair] at H
  dsimp only [reindex] at *
  simp only [Fintype.card_fin,activeDeficit,Finset.card_univ,Function.comp_def] at H
  convert H using 1

end SelectedStream
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma reverseTuple_injective : Function.Injective (reverseTuple (K:=K) (V:=V) (N:=n)) := by
  intro x y h
  funext i
  have H:=congrFun h i.rev
  simp only [reverseTuple,Fin.rev_rev] at H
  exact swapFlag.injective H
lemma changeOrientation_deficit (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (J : ℝ) :
    let T:=S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply
    mean (first (pair T.law ctx T.tuple)) (fun c=>(n:ℝ)*J-entropy (fiber (pair T.law ctx T.tuple) c))=
    mean (first (pair S.law ctx S.tuple)) (fun c=>(n:ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c)) := by
  exact mean_fiber_entropy_injective S.law ctx S.tuple reverseTuple reverseTuple_injective _
end
end SharpRamseyFive.SelectedTuple

end OAI
