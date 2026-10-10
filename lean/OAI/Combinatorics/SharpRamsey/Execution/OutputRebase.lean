import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.OutputComposition

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω F : Type} [Fintype Ω] [Fintype F]
  {ℓ m : ℕ} {p : Law Ω} {G : Ω→Fin ℓ→F} {B C L : ℝ}

def ContextOutput.mono (e : ContextOutput p G m B C L)
    {B' C' L' : ℝ} (hB : B ≤ B') (hC : C ≤ C') (hL : L ≤ L') :
    ContextOutput p G m B' C' L' where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=e.chosen
  domains:=e.domains
  supported:=e.supported
  hit:=e.hit
  size:=fun c i=>(e.size c i).trans hB
  dominated:=fun a=>(e.dominated a).trans (mul_le_mul_of_nonneg_right hL (p.nonneg a))
  cost:=e.cost.trans hC

def ContextOutput.rebase (e : ContextOutput p G m B C L)
    (p₀ : Law Ω) {L₀ : ℝ} (hL : 0 ≤ L)
    (hp : ∀ x,p.mass x ≤ L₀*p₀.mass x) : ContextOutput p₀ G m B C (L*L₀) where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=e.chosen
  domains:=e.domains
  supported:=by
    intro x hz
    have h:=hp (e.source x)
    rw [hz,mul_zero] at h
    exact e.supported x (le_antisymm h (p.nonneg _))
  hit:=e.hit
  size:=e.size
  dominated:=by
    intro x
    exact (e.dominated x).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp x) hL)
  cost:=e.cost

def ContextOutput.restrict (e : ContextOutput p G m B C L) {n : ℕ} (hn : n ≤ m) :
    ContextOutput p G n B C L where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=fun x=>(OrderEmbedding.ofStrictMono (Fin.castLE hn) (by
    intro i j hij
    exact hij)).trans (e.chosen x)
  domains:=fun c i=>e.domains c (Fin.castLE hn i)
  supported:=e.supported
  hit:=fun x i=>e.hit x (Fin.castLE hn i)
  size:=fun c i=>e.size c (Fin.castLE hn i)
  dominated:=e.dominated
  cost:=e.cost
end
end SharpLogRamsey.Selection

end

end OAI
