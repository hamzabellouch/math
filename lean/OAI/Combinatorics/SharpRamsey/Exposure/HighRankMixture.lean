import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.HighRankReplacement
import OAI.Combinatorics.SharpRamsey.Exposure.DominatedMixture
import OAI.Combinatorics.SharpRamsey.Selection.MixedLoss

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section

structure StreamReplacement {Ω F ι Γ : Type} [Fintype Ω] [Fintype F] [Fintype Γ]
    (p : Law Ω) (G : Ω→ι→F) (pos : ι→ℕ) (m : ℕ) (DD : Γ→Finset F) (B C : ℝ) where
  X : Type
  finiteX : Fintype X
  μ : @Law X finiteX
  source : X→Ω
  msg : X→Γ
  index : X→Fin m→ι
  ordered : ∀ x,StrictMono (fun i=>pos (index x i))
  supported : ∀ x,μ.mass x≠0→p.mass (source x)≠0
  hit : ∀ x,μ.mass x≠0→∀ i,G (source x) (index x i)∈DD (msg x)
  size : ∀ x,((DD (msg x)).card:ℝ)≤B
  dominated : letI:=finiteX; ∀ a,(μ.map source).mass a≤4*p.mass a
  cost : letI:=finiteX; entropy (μ.map msg)≤C
attribute [instance] StreamReplacement.finiteX

variable {Ω F ι Γ Z : Type} [Fintype Ω] [Fintype F] [Fintype ι] [Fintype Γ] [Fintype Z]

omit [Fintype ι] in

theorem mix_stream_replacement [Fintype (ι→F)]
    (p : Law Ω) (G : Ω→ι→F) (pos : ι→ℕ)
    (μ : Law Z) (Q : Z→Type) [∀ z,Fintype (Q z)] (q : ∀ z,Law (Q z))
    (restore : ∀ z,Q z→ι→F)
    (hrestore : (μ.sigma q).map (fun z=>restore z.1 z.2)=p.map G)
    (H : Finset Z) (hH : (1:ℝ)/2≤μ.event H)
    (ℓ : H→ℕ) (target : ∀ z,Q z.val→Fin (ℓ z)→F)
    (loc : ∀ z,Fin (ℓ z)→ι)
    (hloc : ∀ z,StrictMono (fun i=>pos (loc z i)))
    (hvalue : ∀ z y i,restore z.val y (loc z i)=target z y i)
    (m : ℕ) (hm : ∀ z,m≤ℓ z/2) (DD : Γ→Finset F) (B C : ℝ)
    (e : ∀ z,Replacement (q z.val) (target z) DD B C)
    (hcost : ∀ (Y : Type) [Fintype Y] (ν : Law Y) (msg : Y→Γ),entropy (ν.map msg)≤C) :
    Nonempty (StreamReplacement p G pos m DD B C) := by
  let X : H→Type:=fun z=>(e z).Ω
  let ν : ∀ z,Law (X z):=fun z=>(e z).μ
  let f : ∀ z,X z→Q z.val:=fun z=>(e z).source
  let ρ:=(μ.onEvent H (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hH)).sigma ν
  let F0:=fun x : Σ z : H,X z=>restore x.1.val (f x.1 x.2)
  have hd : ∀ y,(ρ.map F0).mass y≤4*(p.map G).mass y := by
    intro y
    have hh:=μ.dominated_history_map H hH Q q X ν f 2 (by norm_num)
      (fun z=>(e z).dominated) restore y
    rw [hrestore] at hh
    simpa only [show (2:ℝ)*2=4 by norm_num] using hh
  let τ:=ρ.attach p F0 G
  let msg:=fun x : Σ _x : (Σ z : H,X z),Ω=>(e x.1.1).msg x.1.2
  let idx:=fun x : Σ _x : (Σ z : H,X z),Ω=>fun i : Fin m=>
    loc x.1.1 ((e x.1.1).chosen x.1.2 (Fin.castLE (hm x.1.1) i))
  refine ⟨⟨_,inferInstance,τ,(fun x=>x.2),msg,idx,?_,?_,?_,?_,?_,hcost _ τ msg⟩⟩
  · intro x i j hij
    exact hloc x.1.1 ((e x.1.1).chosen x.1.2|>.strictMono hij)
  · intro x hx
    exact (ρ.attach_support_of_dominated p F0 G 4 hd x hx).2.1
  · intro x hx i
    have hh:=ρ.attach_support_of_dominated p F0 G 4 hd x hx
    have he:=congrFun hh.2.2 (idx x i)
    rw [he]
    change restore x.1.1.val (f x.1.1 x.1.2)
      (loc x.1.1 ((e x.1.1).chosen x.1.2 (Fin.castLE (hm x.1.1) i)))∈_
    rw [hvalue]
    exact (e x.1.1).hit x.1.2 _
  · intro x
    exact (e x.1.1).size x.1.2
  · intro x
    exact ρ.attach_map_source_le p F0 G 4 hd x
end
end SharpLogRamsey.ActualHighRank

end

end OAI
