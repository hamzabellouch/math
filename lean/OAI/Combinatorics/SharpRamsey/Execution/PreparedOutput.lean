import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.PopulationSublist
import OAI.Combinatorics.SharpRamsey.Exposure.PreparedMixture
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalOutput

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance prepOutBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance prepOutFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance prepOutBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→ActualPivot.Flag (K:=K) (V:=V)) (t : Fin k)
  (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))
  (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
  (live : (model w n k p θ G t).FreshHistory→Finset (Fin w)) (fallback : Fin w)

abbrev preparedTargets (y : (mixedPrepared w n k p θ G t hp e).Ω) : Fin w→List (ActualPivot.Flag (K:=K) (V:=V)) :=
  fun i=>List.ofFn (fun j=>(e y.1).source y.2 (goodTarget w n k p θ G t y.1.val (bad y.1.val) i j))

abbrev preparedTree (y : (mixedPrepared w n k p θ G t hp e).Ω) := liveTree (live y.1.val) fallback

theorem prepared_context_of_mean (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
    (hτ : 0≤τ) (hτsmall : τ≤1/40000) (hn : 0<n)
    (hmean : (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
      ∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*((w*(2*(n+k)):ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
        (fun _=>chronoRead b) (preparedTargets w n k p θ G t hp e bad ω.1) tab
        (preparedTree w n k p θ G t hp e live fallback ω.1) (univ,univ)).length))≤
      (w*(2*(n+k)):ℝ)/4) :
    Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
      (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
      (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
        w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  have hw : 0<w:=Nat.zero_lt_of_lt fallback.isLt
  have hN : 0<w*(2*(n+k)) :=
    Nat.mul_pos hw (Nat.mul_pos (by decide) (by omega))
  have hmarg : (attachedPrepared w n k p θ G t hp e).μ.map (fun ω=>ω.2)=p :=
    (attachedPrepared w n k p θ G t hp e).marginal
  have hres:=book.context_output hdim hb hH hP haP hτ hτsmall p (fun ω=>flattenTuple (G ω))
    (attachedPrepared w n k p θ G t hp e).μ (fun ω=>ω.2) hmarg
    (fun ω=>(e ω.1.1).supports ω.1.2)
    (fun ω=>preparedTargets w n k p θ G t hp e bad ω.1)
    (fun ω=>preparedTree w n k p θ G t hp e live fallback ω.1)
    (w*(2*(n+k))) w (Nat.log 2 w+1) (2*(n+k)) hN
    (fun ω=>by rw [goodPopulation_length];exact goodPopulation_size w n k p θ G t _ _ _)
    (fun ω=>by rw [liveTree_nodes];simpa using card_le_univ (live ω.1.1.val))
    (fun ω=>by
      apply (liveTree_height _ _).trans
      exact Nat.add_le_add_right (Nat.log_mono_right (by simpa using card_le_univ (live ω.1.1.val))) 1)
    (fun ω i=>by rw [List.length_ofFn];simpa using card_le_univ (goodMiddle w n k p θ G t ω.1.1.val (bad ω.1.1.val) i))
    (fun ω hω=>goodPopulation_sublist w n k p θ G t ω.1.1.val (bad ω.1.1.val)
      (live ω.1.1.val) fallback ((e ω.1.1).source ω.1.2) (G ω.2)
      (fun i=>((attachedPrepared_tuple w n k p θ G t hp e ω hω).2.2 i).symm))
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hmean)
  have heq : w*(2*(n+k))/2=w*(n+k) := by
    have : w*(2*(n+k))=2*(w*(n+k)) := by ring
    omega
  simpa only [heq] using hres
end
end SharpLogRamsey.Selection.Windows

end

end OAI
