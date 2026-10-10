import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodRows
import OAI.Combinatorics.SharpRamsey.Parameters.HighRankScales

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real FiniteMarginals HighRankCoverageProbability FiniteEventBounds
open scoped Classical BigOperators
noncomputable section

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
lemma Law.swap_map_marginal (p : Law X) (f : X→A×B) (a : A) (b : B) :
    FiniteMarginals.marginal p.mass (fun x=>(f x).swap) (b,a)=(p.map f).mass (a,b) := by
  simp only [FiniteMarginals.marginal,Law.map,sum_filter]
  apply sum_congr rfl
  intro x _
  have he : (f x).swap=(b,a) ↔ f x=(a,b) := by
    rcases f x with ⟨c,d⟩
    simp only [Prod.swap_prod_mk,Prod.mk.injEq,and_comm]
  simp only [he]
  split_ifs <;> rfl
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection FiniteMarginals HighRankCoverageProbability FiniteEventBounds HighRankAssembly
open scoped Classical BigOperators
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local instance flat_ActualHighRankExtraction_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankExtraction_2 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankExtraction_3 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)
local notation "q" => (Nat.card K:ℝ)

theorem extraction (hd : 2≤d) {ℓ : ℕ} (hℓ : 0<ℓ)
    (s : Law (A×B)) (S : Finset (A×B))
    (p : Law Ξ) (f : Ξ→Fin ℓ→A×B) (U : Fin ℓ→Finset (A×B))
    (σ β D : ℝ) (hσ : 1≤σ) (hβ : 0≤β) (hlog : log q=σ) (hD : σ^β≤D)
    (h r r' T : ℕ) (hr : 2≤r) (hrd : r≤d) (hrank : d+2≤r+r') (hhd : 2*d≤h)
    (u I : ℝ) (hu : 0<u) (huA : u≤2048*exp (D*σ^(3*β)))
    (hu20 : u≤1/20) (hCu : 20*exp (1/2)*u≤1)
    (hsmall : 4300*σ^(-2*β)≤1/4)
    (hs : ∀ z,z∉S→s.mass z=0)
    (hSA : ((S.image Prod.fst).card:ℝ)≤1024*q^r')
    (hSB : ((S.image Prod.snd).card:ℝ)≤1024*q^r)
    (hS : (S.card:ℝ)≤64*q^d)
    (hsfA : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ))
    (hsfB : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ))
    (hsdef : (d:ℝ)*σ-entropy s≤D*σ^β)
    (hp : ∀ x,p.mass x≠0→∀ i,f x i∈U i)
    (hinc : ∀ x,p.mass x≠0→∀ i,(f x i).1.rep (f x i).2.rep=0)
    (hUA : ∀ i,(((U i).image Prod.fst).card:ℝ)≤1024*q^r')
    (hUB : ∀ i,(((U i).image Prod.snd).card:ℝ)≤1024*q^r)
    (hU : ∀ i,((U i).card:ℝ)≤64*q^d)
    (hufA : ∀ i a,((univ.filter (fun b=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ))
    (hufB : ∀ i b,((univ.filter (fun a=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ))
    (hdef : ∀ i,(d:ℝ)*σ-entropy (p.map (fun x=>f x i))≤D*σ^β)
    (hconflict : ∀ i,(∑ x,p.mass x*∑ z,s.mass z*
      indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))≤I)
    (hTlo : (h:ℝ)/(10*q)≤T) (hThi : (T:ℝ)≤(h:ℝ)/(10*q)+1)
    (hTn : d+2≤T) (hescape : 20480*exp (D*σ^(3*β))≤q) :
    let κ:=D*σ^(3*β)
    let E:=univ.filter (fun z : A×B=>
      highGoodFirst s (1024*q^r') ((d:ℝ)*σ) κ (exp (κ-(r':ℝ)*σ)) z.1 ∧
      highGoodSecond s (1024*q^r) ((d:ℝ)*σ) κ (exp (κ-(r:ℝ)*σ)) z.2)
    ∃ hE : (1:ℝ)/2≤ s.event E,
      let w:=(s.onEvent E (by linarith)).mass
      let Sz:=(10*(d+1)*1024*exp κ/u)^(d+1)*1024*(1+2^(d+2))*(2*q^d)
      let err:=4365*σ^(-2*β)+100*1024^2*exp (2*κ)/q+
        (d*exp (-3*(h:ℝ)/(20*d*q))+exp (1-(h:ℝ)/(10*q)))+4*h*I+2048*exp κ/q
      let W:=fun z : (Fin h→E)×(Fin h→E)=>ProductLaw.weight w z.1*ProductLaw.weight w z.2
      let DD:=fun z : (Fin h→E)×(Fin h→E)=>HighRankSize.domain (fun z : E=>z.val.1.rep)
        (fun z : E=>z.val.2) z.1 z.2 r T
      1-2*err-1/4≤∑ v∈univ.filter (fun v : Ξ×((Fin h→E)×(Fin h→E))=>
        ((DD v.2).card:ℝ)≤4*Sz ∧ ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,(f v.1 (e i)).swap∈DD v.2),
        p.mass v.1*W v.2 := by
  dsimp only
  let κ:=D*σ^(3*β)
  have hq : 0<q := by exact_mod_cast Nat.card_pos (α:=K)
  have he (j : ℕ) : exp ((j:ℝ)*σ)=q^j := by rw [←hlog,exp_nat_mul,exp_log hq]
  have hm:=actual_high_endpoint_errors s S σ β D d r r' hσ hβ hD hs
    (by simpa only [he] using hSA) (by simpa only [he] using hSB)
    (by simpa only [he] using hS) hsfA hsfB hsdef
  dsimp only at hm
  simp only [he] at hm
  let E:=univ.filter (fun z : A×B=>
    highGoodFirst s (1024*q^r') ((d:ℝ)*σ) κ (exp (κ-(r':ℝ)*σ)) z.1 ∧
    highGoodSecond s (1024*q^r) ((d:ℝ)*σ) κ (exp (κ-(r:ℝ)*σ)) z.2)
  obtain ⟨hE,hfirst,hsecond,hmean⟩:=high_good_rows s (1024*q^r') (1024*q^r) ((d:ℝ)*σ) κ
    (exp (κ-(r':ℝ)*σ)) (exp (κ-(r:ℝ)*σ)) (4300*σ^(-2*β))
    (exp_nonneg _) (exp_nonneg _) hsmall hm.1 hm.2.1
  change (1:ℝ)/2≤ s.event E at hE
  refine ⟨hE,?_⟩
  let row:=s.onEvent E (by linarith : 0<s.event E)
  let tp:=fun i=>p.map (fun x=>f x i)
  have hsup i : ∀ z,z∉U i→(tp i).mass z=0 := by
    intro z hz
    by_contra hh
    obtain ⟨x,hx,heq⟩:=p.map_support (fun x=>f x i) z hh
    exact hz (heq ▸ hp x hx i)
  have htarg i:=actual_high_endpoint_errors (tp i) (U i) σ β D d r r' hσ hβ hD (hsup i)
    (by simpa only [he] using hUA i) (by simpa only [he] using hUB i)
    (by simpa only [he] using hU i) (hufA i) (hufB i) (hdef i)
  dsimp only at htarg
  simp only [he] at htarg
  let good:=fun i b=>highGoodSecond (tp i) (1024*q^r) ((d:ℝ)*σ) κ (exp (κ-(r:ℝ)*σ)) b
  have hsw i a b : FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) (b,a)=(tp i).mass (a,b) :=
    p.swap_map_marginal _ a b
  have hsum i b : (∑ a,FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) (b,a))=(tp i).snd.mass b := by
    simp only [hsw]
    rfl
  have hcap (j : ℕ) : 2*exp (κ-(j:ℝ)*σ)≤1024*exp κ/q^j := by
    rw [exp_sub,he]
    have hp0 : 0≤exp κ/q^j := by positivity
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤1024) hp0
  have HC:=extraction_source hd hℓ row.mass row.nonneg row.total
    (fun z : E=>z.val.1) (fun z : E=>z.val.2) p.mass p.nonneg p.total
    (fun x i=>(f x i).swap) (fun i=>(U i).image Prod.snd) good h r r' T hr hrd hrank hhd
    1024 κ u (4300*σ^(-2*β)) (65*σ^(-2*β)) (2*I) (by norm_num) hu
    (by simpa only [show (2:ℝ)*1024=2048 by norm_num] using huA) hu20 hCu
    (fun a=>(hfirst a).trans (hcap r')) (fun b=>(hsecond b).trans (hcap r))
    (S.image Prod.snd) ?_ hSB ?_ ?_ ?_ hUB ?_ ?_ ?_ hTlo hThi hTn
    (by simpa only [show (20:ℝ)*1024=20480 by norm_num] using hescape)
  · convert HC using 1
    dsimp only [κ]
    ring
  · intro b hb
    have hzero:=s.map_image_support S Prod.snd hs b hb
    rw [Law.map_snd] at hzero
    have hh:=s.onEvent_map_le_two E hE Prod.snd b
    rw [Law.map_snd,hzero,mul_zero,row.map_mass_eq_marginal] at hh
    exact le_antisymm hh (marginal_nonneg row.mass row.nonneg _ b)
  · intro i ⟨b,a⟩ hmass
    rw [hsw] at hmass
    obtain ⟨x,hx,heq⟩:=p.map_support (fun x=>f x i) (a,b) hmass
    simpa only [heq] using hinc x hx i
  · intro i ⟨b,a⟩ hmass
    rw [hsw] at hmass
    have hz : (a,b)∈U i := by by_contra hh; exact hmass (hsup i (a,b) hh)
    exact mem_image.mpr ⟨(a,b),hz,rfl⟩
  · intro i b hb
    rw [hsum]
    exact hb.2.trans (by
      rw [exp_sub,he]
      have hp0 : 0≤exp κ/q^r := by positivity
      simpa only [one_mul,mul_div_assoc] using mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)≤1024) hp0)
  · intro i
    simp only [hsum]
    exact (htarg i).2.1
  · intro i
    have hh:=(htarg i).2.2
    rw [exp_sub,he] at hh
    simp only [Law.event,sum_filter] at hh
    calc
      _ ≤ ∑ t : B×A, if exp κ/q^d<FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) t
          then FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) t else 0 :=
        sum_le_univ_sum_of_nonneg (fun t=>by split_ifs; exact marginal_nonneg p.mass p.nonneg _ t; rfl)
      _ = ∑ z : A×B, if exp κ/q^d<(tp i).mass z then (tp i).mass z else 0 := by
        rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_comm]
        simp only [hsw]
      _ ≤ _ := hh
  · intro i
    rw [sum_marginal]
    calc
      _ ≤ ∑ x,p.mass x*(2*∑ z,s.mass z*
          indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0)) := by
        apply sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
        exact hmean (fun z=>indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))
          (fun z=>indicator_nonneg _)
      _ = 2*(∑ x,p.mass x*∑ z,s.mass z*
          indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0)) := by simp only [mul_sum]; ring_nf
      _ ≤ 2*I := mul_le_mul_of_nonneg_left (hconflict i) (by norm_num)
end
end SharpLogRamsey.ActualHighRank

end

end OAI
