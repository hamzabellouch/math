import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.DomainTransport
import OAI.Combinatorics.RamseyFive.Entropy.SelectedRestriction

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance psFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

structure Prepared (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (J B M : ℝ) where
  domain : κ→Fin n→Finset (FlagPair K V)
  contains : ∀z,0<S.law z→∀i,S.tuple z i∈domain (ctx z) i
  cap : ∀c i,Real.log (domain c i).card≤J
  deficit : mean (first (pair S.law ctx S.tuple))
    (fun c=>(n:ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c))≤B
  incident : ∀z,0<S.law z→TupleIncident (S.tuple z)
  consistent : ∀z,0<S.law z→TupleConsistent (S.tuple z)
  occupancy : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
    (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M

namespace Prepared
variable {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible}
  {ctx : Ω→κ} {J B M : ℝ}
def reindex (h : Prepared S ctx J B M) (e : Fin l↪o Fin n) :
    Prepared (S.reindex e) ctx J B M where
  domain c i:=h.domain c (e i)
  contains z hz i:=h.contains z hz (e i)
  cap c i:=h.cap c (e i)
  deficit:=(S.reindex_deficit ctx e h.domain J h.contains (fun c _=>h.cap c)).trans h.deficit
  incident z hz i:=h.incident z hz (e i)
  consistent z hz i j hij:=h.consistent z hz (e i) (e j) (e.strictMono hij)
  occupancy z hz:=occupancy_reindex _ e e.injective M (h.occupancy z hz)

def swap (h : Prepared S ctx J B M) :
    Prepared (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply) ctx J B M where
  domain c i:=swapDomain (h.domain c i.rev)
  contains z hz i:=(mem_swapDomain_iff _ _).mpr (h.contains z hz i.rev)
  cap c i:=by simpa only [swapDomain,Finset.card_map] using h.cap c i.rev
  deficit:=by rw [changeOrientation_deficit];exact h.deficit
  incident z hz:=reverseTuple_incident (h.incident z hz)
  consistent z hz:=reverseTuple_consistent (h.consistent z hz)
  occupancy z hz:=occupancy_reverse _ M (h.occupancy z hz)
end Prepared
end
end SharpRamseyFive.SelectedTuple

end OAI
