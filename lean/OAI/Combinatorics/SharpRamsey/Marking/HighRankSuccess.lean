import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRankBudgets

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local instance flat_ActualHighRankSuccess_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankSuccess_2 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankSuccess_3 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)
local notation "q" => (Nat.card K:ℝ)

def rawDomain {h : ℕ} (z : (Fin h→A×B)×(Fin h→A×B)) (r T : ℕ) : Finset (A×B) :=
  (HighRankSize.domain (fun z : A×B=>z.1.rep) (fun z : A×B=>z.2) z.1 z.2 r T).image Prod.swap

def highPrefactor (d : ℕ) : ℝ :=
  8*(10*((d:ℝ)+1)*1024/richDensity)^(d+1)*1024*(1+2^(d+2))

lemma highPrefactor_pos (d : ℕ) : 0<highPrefactor d := by
  have hh:=density_positive
  unfold highPrefactor
  positivity

lemma highSize_eq (σ η D : ℝ) (d : ℕ) (Q : ℝ) :
    4*((10*((d:ℝ)+1)*1024*exp (scaleK σ η D)/richDensity)^(d+1)*1024*(1+2^(d+2))*(2*Q^d))=
      highPrefactor d*Q^d*exp (((d:ℝ)+1)*scaleK σ η D) := by
  rw [show ((d:ℝ)+1)*scaleK σ η D=((d+1:ℕ):ℝ)*scaleK σ η D by
    simp only [Nat.cast_add, Nat.cast_one],
    exp_nat_mul,highPrefactor]
  rw [show 10*((d:ℝ)+1)*1024*exp (scaleK σ η D)/richDensity=
    (10*((d:ℝ)+1)*1024/richDensity)*exp (scaleK σ η D) by ring,mul_pow]
  ring

theorem eventually_success {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ξ : Type) [Field K] [Fintype K] [Fintype Ξ],
      log (Nat.card K:ℝ)=σ →
      ∀ (ℓ : ℕ), 0<ℓ →
      ∀ (s : Law (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (S : Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (p : Law Ξ) (f : Ξ→Fin ℓ→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (U : Fin ℓ→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D : ℝ), σ^beta η≤D → D≤σ^(1-η/2) →
      ∀ r r' : ℕ, 2≤r → r≤d → d+2≤r+r' →
      (∀ z,z∉S→s.mass z=0) →
      (((S.image Prod.fst).card:ℝ)≤1024*(Nat.card K:ℝ)^r') →
      (((S.image Prod.snd).card:ℝ)≤1024*(Nat.card K:ℝ)^r) →
      ((S.card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ)) →
      (∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ)) →
      ((d:ℝ)*σ-entropy s≤D*σ^beta η) →
      (∀ x,p.mass x≠0→∀ i,f x i∈U i) →
      (∀ x,p.mass x≠0→∀ i,(f x i).1.rep (f x i).2.rep=0) →
      (∀ i,(((U i).image Prod.fst).card:ℝ)≤1024*(Nat.card K:ℝ)^r') →
      (∀ i,(((U i).image Prod.snd).card:ℝ)≤1024*(Nat.card K:ℝ)^r) →
      (∀ i,((U i).card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∀ i a,((univ.filter (fun b=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ)) →
      (∀ i b,((univ.filter (fun a=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ)) →
      (∀ i,(d:ℝ)*σ-entropy (p.map (fun x=>f x i))≤D*σ^beta η) →
      (∀ i,(∑ x,p.mass x*∑ z,s.mass z*FiniteEventBounds.indicator
        (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))≤2*σ^(-2000*beta η)/(Nat.card K:ℝ)) →
      let E:=univ.filter (fun z=>
        highGoodFirst s (1024*(Nat.card K:ℝ)^r') ((d:ℝ)*σ) (scaleK σ η D)
          (exp (scaleK σ η D-(r':ℝ)*σ)) z.1 ∧
        highGoodSecond s (1024*(Nat.card K:ℝ)^r) ((d:ℝ)*σ) (scaleK σ η D)
          (exp (scaleK σ η D-(r:ℝ)*σ)) z.2)
      ∃ hE : (1:ℝ)/2≤ s.event E,
        let row:=s.onEvent E (by linarith)
        let h:=rawRows σ η
        let W:=fun z : (Fin h→E)×(Fin h→E)=>ProductLaw.weight row.mass z.1*ProductLaw.weight row.mass z.2
        let code:=fun z : (Fin h→E)×(Fin h→E)=>(fun i=>(z.1 i).val,fun i=>(z.2 i).val)
        let DD:=fun z=>rawDomain (code z) r (rawThreshold σ η)
        (1:ℝ)/2≤∑ v∈univ.filter (fun v : Ξ×((Fin h→E)×(Fin h→E))=>
          ((DD v.2).card:ℝ)≤highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D) ∧
          ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f v.1 (e i)∈DD v.2), p.mass v.1*W v.2 := by
  filter_upwards [eventual_budgets hη d (by omega)] with σ hσ
  intro K Ξ _ _ _ hlog ℓ hℓ s S p f U D hDl hDu r r' hr hrd hrank
    hs hSA hSB hS hsfA hsfB hsdef hp hinc hUA hUB hU hufA hufB hdef hcon
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.card_pos (α:=K)
  have heq : exp σ=(Nat.card K:ℝ) := by rw [←hlog,exp_log hq]
  obtain ⟨hσ1,hh,hT,hTlo,hThi,huA,hsmall,hescape,herr⟩:=hσ D hDl hDu
  rw [heq] at hTlo hThi hescape
  have H:=extraction hd hℓ s S p f U σ (beta η) D hσ1 (by unfold beta; positivity) hlog hDl
    (rawRows σ η) r r' (rawThreshold σ η) hr hrd hrank hh richDensity
    (2*σ^(-2000*beta η)/(Nat.card K:ℝ)) density_positive huA density_small density_scaled hsmall
    hs hSA hSB hS hsfA hsfB hsdef hp hinc hUA hUB hU hufA hufB hdef hcon hTlo hThi hT hescape
  dsimp only at H ⊢
  obtain ⟨hE,H⟩:=H
  refine ⟨hE,?_⟩
  have herr' : 1/2≤1-2*rawError σ η D d-1/4 := by linarith
  apply herr'.trans
  unfold rawError at herr' ⊢
  rw [heq]
  apply H.trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨hc,e,he⟩:=(mem_filter.mp hv).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,e,?_⟩
    · rw [←highSize_eq]
      rw [rawDomain, card_image_of_injective _ Prod.swap_injective]
      convert hc using 1 <;> try rfl
    · intro i
      apply mem_image.mpr
      exact ⟨(f v.1 (e i)).swap,he i,Prod.swap_swap _⟩
  · intro v _ _
    apply mul_nonneg (p.nonneg _)
    apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro j hj <;> exact (s.onEvent _ _).nonneg _
end
end SharpLogRamsey.ActualHighRank

end

end OAI
