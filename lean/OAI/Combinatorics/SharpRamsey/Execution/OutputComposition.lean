import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.UnifiedContext

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω F A : Type} [Fintype Ω] [Fintype F] [Fintype A]
  {N ℓ m : ℕ} {p : Law Ω} {G : Ω→Fin ℓ→F} {B C L : ℝ}

def ContextOutput.transport (e : ContextOutput p G m B C L)
    (φ : F≃A) (G₀ : Ω→Fin N→A) (j : Ω→Fin ℓ↪o Fin N)
    (h : ∀ x i,φ (G x i)=G₀ x (j x i)) :
    ContextOutput p G₀ m B C L where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=fun x=>(e.chosen x).trans (j (e.source x))
  domains:=fun c i=>(e.domains c i).map φ.toEmbedding
  supported:=e.supported
  hit:=by
    intro x i
    change G₀ (e.source x) (j (e.source x) (e.chosen x i)) ∈ _
    rw [←h]
    exact mem_map.mpr ⟨_,e.hit x i,rfl⟩
  size:=by intro c i;simpa only [card_map] using e.size c i
  dominated:=e.dominated
  cost:=e.cost

def ContextOutput.compose (e : ContextOutput p G m B C L)
    {n : ℕ} {B' C' L' : ℝ}
    (f : ContextOutput e.μ (fun x i=>G (e.source x) (e.chosen x i)) n B' C' L')
    (hL' : 0≤L') : ContextOutput p G n B' C' (L'*L) where
  X:=f.X
  Γ:=f.Γ
  finiteX:=f.finiteX
  finiteΓ:=f.finiteΓ
  μ:=f.μ
  source:=e.source∘f.source
  msg:=f.msg
  chosen:=fun x=>(f.chosen x).trans (e.chosen (f.source x))
  domains:=f.domains
  supported:=fun x=>e.supported (f.source x)
  hit:=f.hit
  size:=f.size
  dominated:=by
    intro a
    rw [←Law.map_map]
    calc
      _ ≤ ∑ y ∈ univ.filter (fun y=>e.source y=a),L'*e.μ.mass y := by
        change (∑ y ∈ univ.filter (fun y=>e.source y=a),(f.μ.map f.source).mass y)≤_
        exact sum_le_sum (fun y _=>f.dominated y)
      _ = L'*(e.μ.map e.source).mass a := by
        simp only [Law.map,mul_sum]
      _ ≤ L'*(L*p.mass a) := mul_le_mul_of_nonneg_left (e.dominated a) hL'
      _ = _ := by ring
  cost:=f.cost
end
end SharpLogRamsey.Selection

end

end OAI
