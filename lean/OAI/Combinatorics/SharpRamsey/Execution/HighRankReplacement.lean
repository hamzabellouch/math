import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.HighRankEntropy

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

structure Replacement {F Ξ Γ : Type} [Fintype F] [Fintype Ξ] [Fintype Γ]
    (p : Law Ξ) {ℓ : ℕ} (f : Ξ→Fin ℓ→F) (DD : Γ→Finset F) (B C : ℝ) where
  Ω : Type
  inst : Fintype Ω
  μ : @Law Ω inst
  source : Ω→Ξ
  msg : Ω→Γ
  chosen : Ω→(Fin (ℓ/2)↪o Fin ℓ)
  hit : ∀ ω i,f (source ω) (chosen ω i)∈DD (msg ω)
  size : ∀ ω,((DD (msg ω)).card:ℝ)≤B
  dominated : letI := inst; ∀ a,(μ.map source).mass a≤2*p.mass a
  cost : letI := inst; entropy (μ.map msg)≤C
attribute [instance] Replacement.inst

section Generic
variable {F Ξ : Type} [Fintype F] [Fintype Ξ]

theorem replacement_of_success {h ℓ : ℕ} (p : Law Ξ) (E : Finset F) (row : Law E)
    (f : Ξ→Fin ℓ→F) (DD : ((Fin h→F)×(Fin h→F))→Finset F) (B : ℝ) :
    let rows:=(Law.pi (fun _ : Fin h=>row)).prod (Law.pi (fun _ : Fin h=>row))
    let μ:=p.prod rows
    let code:=fun z : Ξ×((Fin h→E)×(Fin h→E))=>
      (fun i=>(z.2.1 i).val,fun i=>(z.2.2 i).val)
    let G:=univ.filter (fun z=>((DD (code z)).card:ℝ)≤B ∧
      ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f z.1 (e i)∈DD (code z))
    (1:ℝ)/2≤μ.event G →
    Nonempty (Replacement p f DD B (2*(h:ℝ)*log (Fintype.card F))) := by
  intro rows μ code G hg
  obtain ⟨hG,ch,hch,hcard,_,hdom,hcost⟩:=context_replacement p E row f DD B
    (fun _ _=>True) (by simp) id hg
  refine ⟨⟨G,inferInstance,μ.onEvent G hG,(fun z=>z.val.1),(fun z=>code z.val),ch,hch,hcard,?_,hcost⟩⟩
  intro a
  have hh:=hdom a
  rw [Law.map_id] at hh
  exact hh

theorem replacement_of_weight_success {h ℓ : ℕ} (p : Law Ξ) (E : Finset F) (row : Law E)
    (f : Ξ→Fin ℓ→F) (DD : ((Fin h→F)×(Fin h→F))→Finset F) (B : ℝ)
    (hg : (1:ℝ)/2≤∑ v∈univ.filter (fun v : Ξ×((Fin h→E)×(Fin h→E))=>
      ((DD (fun i=>(v.2.1 i).val,fun i=>(v.2.2 i).val)).card:ℝ)≤B ∧
      ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f v.1 (e i)∈DD (fun i=>(v.2.1 i).val,fun i=>(v.2.2 i).val)),
      p.mass v.1*(ProductLaw.weight row.mass v.2.1*ProductLaw.weight row.mass v.2.2)) :
    Nonempty (Replacement p f DD B (2*(h:ℝ)*log (Fintype.card F))) := by
  apply replacement_of_success (h:=h) (ℓ:=ℓ) p E row f DD B
  simpa only [Law.event,Law.prod,Law.pi,ProductLaw.weight] using hg

variable {Γ : Type} [Fintype Γ] {p : Law Ξ} {ℓ : ℕ} {f : Ξ→Fin ℓ→F}
  {DD : Γ→Finset F} {B C C' : ℝ}

def Replacement.cost_mono (e : Replacement p f DD B C) (h : C≤C') :
    Replacement p f DD B C' := { e with cost := e.cost.trans h }
end Generic

variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local instance flat_ActualHighRankReplacement_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankReplacement_2 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankReplacement_3 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)
local notation "q" => (Nat.card K:ℝ)

structure Caps (σ : ℝ) (r r' : ℕ) (S : Finset (A×B)) : Prop where
  first : ((S.image Prod.fst).card:ℝ)≤1024*q^r'
  second : ((S.image Prod.snd).card:ℝ)≤1024*q^r
  joint : (S.card:ℝ)≤64*q^d
  firstFiber : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ)
  secondFiber : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ)

theorem eventually_replacement {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ξ : Type) [Field K] [Fintype K] [Fintype Ξ],
      log (Nat.card K:ℝ)=σ →
      ∀ (ℓ : ℕ), 0<ℓ →
      ∀ (s : Law (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (S : Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (p : Law Ξ) (f : Ξ→Fin ℓ→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (U : Fin ℓ→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D : ℝ), σ^beta η≤D → D≤σ^(1-η/2) →
      ∀ r r' : ℕ, 2≤r → r≤d → d+2≤r+r' →
      (∀ z,z∉S→s.mass z=0) → Caps σ r r' S →
      ((d:ℝ)*σ-entropy s≤D*σ^beta η) →
      (∀ x,p.mass x≠0→∀ i,f x i∈U i) →
      (∀ x,p.mass x≠0→∀ i,(f x i).1.rep (f x i).2.rep=0) →
      (∀ i,Caps σ r r' (U i)) →
      (∀ i,(d:ℝ)*σ-entropy (p.map (fun x=>f x i))≤D*σ^beta η) →
      (∀ i,(∑ x,p.mass x*∑ z,s.mass z*FiniteEventBounds.indicator
        (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))≤2*σ^(-2000*beta η)/(Nat.card K:ℝ)) →
      Nonempty (Replacement p f (fun z=>rawDomain (h:=rawRows σ η) z r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_success hη d hd] with σ he
  intro K Ξ _ _ _ hlog ℓ hℓ s S p f U D hDl hDu r r' hr hrd hrank hs hS hsdef hp hinc hU hdef hcon
  obtain ⟨hE,hgood⟩:=he K Ξ hlog ℓ hℓ s S p f U D hDl hDu r r' hr hrd hrank
    hs hS.first hS.second hS.joint hS.firstFiber hS.secondFiber hsdef hp hinc
    (fun i=>(hU i).first) (fun i=>(hU i).second) (fun i=>(hU i).joint)
    (fun i=>(hU i).firstFiber) (fun i=>(hU i).secondFiber) hdef hcon
  let E:=univ.filter (fun z : Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)=>
    highGoodFirst s (1024*(Nat.card K:ℝ)^r') ((d:ℝ)*σ) (scaleK σ η D)
      (exp (scaleK σ η D-(r':ℝ)*σ)) z.1 ∧
    highGoodSecond s (1024*(Nat.card K:ℝ)^r) ((d:ℝ)*σ) (scaleK σ η D)
      (exp (scaleK σ η D-(r:ℝ)*σ)) z.2)
  have hE0 : 0<s.event E := by dsimp only [E]; linarith
  let row:=s.onEvent E hE0
  let h:=rawRows σ η
  let DD:=fun z=>rawDomain (K:=K) (d:=d) (h:=h) z r (rawThreshold σ η)
  let B₀:=highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D)
  have extract:=replacement_of_weight_success (h:=h) (ℓ:=ℓ) p E row f DD B₀
  have hex : Nonempty (Replacement p f DD B₀ (2*(h:ℝ)*log (Fintype.card
      (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))))) := by
    apply extract
    dsimp only at hgood
    simpa only [DD, B₀, row, E, h] using hgood
  obtain ⟨e⟩:=hex
  refine ⟨e.cost_mono ?_⟩
  have hdim : Module.finrank K (Fin (d+1)→K)=d+1 := by simp
  have hc:=mul_le_mul_of_nonneg_left (flag_card_log hdim) (by positivity : 0≤2*(h:ℝ))
  rw [hlog] at hc
  calc
    _ ≤ 2*(h:ℝ)*(2*(log 2+(d:ℝ)*σ)) := hc
    _ = _ := by dsimp only [h]; ring

end
end SharpLogRamsey.ActualHighRank

end

end OAI
