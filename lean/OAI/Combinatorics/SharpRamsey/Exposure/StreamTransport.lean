import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.HighRankMixture

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Selection
open scoped Classical
noncomputable section
variable {Ω F F' ι ι' Γ : Type} [Fintype Ω] [Fintype F] [Fintype F'] [Fintype Γ]

def StreamReplacement.transport {p : Law Ω} {G : Ω→ι→F} {pos : ι→ℕ} {m : ℕ}
    {DD : Γ→Finset F} {B C : ℝ} (e : StreamReplacement p G pos m DD B C)
    (f : F≃F') (j : ι→ι') (G' : Ω→ι'→F') (pos' : ι'→ℕ)
    (htime : ∀ i,pos' (j i)=pos i) (hvalue : ∀ x i,G' x (j i)=f (G x i)) :
    StreamReplacement p G' pos' m (fun c=>(DD c).map f.toEmbedding) B C where
  X:=e.X
  finiteX:=e.finiteX
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  index x i:=j (e.index x i)
  ordered x:=by simpa only [htime] using e.ordered x
  supported:=e.supported
  hit x hx i:=by
    rw [hvalue]
    exact mem_map.mpr ⟨_,e.hit x hx i,rfl⟩
  size x:=by simpa only [card_map] using e.size x
  dominated:=e.dominated
  cost:=e.cost
end
end SharpLogRamsey.ActualHighRank

namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical
noncomputable section
variable {α Ω : Type} [Fintype α] [Fintype Ω]

def singleTuple {n : ℕ} (F : Fin (4*n)→α) : Slot 1 n→α := fun i=>F i.2

omit [Fintype α] in
lemma singleTuple_injective (n : ℕ) : Function.Injective (singleTuple (α:=α) (n:=n)) := by
  intro F G h
  funext i
  exact congrFun h (0,i)

lemma single_position {n : ℕ} (i : Slot 1 n) : position i=i.2.val := by
  have h : i.1.val=0 := Fin.eq_zero i.1 ▸ rfl
  simp only [position,h,zero_mul,zero_add]

lemma single_entropy {n : ℕ} (p : Law Ω) (F : Ω→Fin (4*n)→α) :
    entropy (p.map (fun x=>singleTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>singleTuple (F x))=singleTuple ∘ F from rfl,←Law.map_map]
  exact entropy_map_eq_of_injective _ _ (singleTuple_injective n)
end
end SharpLogRamsey.Selection.Windows

end

end OAI
