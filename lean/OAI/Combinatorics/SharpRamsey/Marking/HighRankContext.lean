import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRankSuccess

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma Law.prod_map_left (p : Law X) (s : Law Y) (f : X→Z) :
    (p.prod s).map (fun z=>f z.1)=p.map f := by
  ext a
  simp only [Law.map,Law.prod,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  by_cases h : f x=a
  · simp only [h,ite_true,←mul_sum,s.total,mul_one]
  · simp only [h,ite_false,sum_const_zero]

lemma raw_rows_entropy {F Ω : Type*} [Fintype F] [Fintype Ω] (h : ℕ)
    (p : Law Ω) (code : Ω→(Fin h→F)×(Fin h→F)) :
    entropy (p.map code)≤2*(h:ℝ)*log (Fintype.card F) := by
  have hh:=entropy_le_log_card (p.map code) univ (by simp)
  simp only [card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_pow] at hh
  rw [←pow_two,log_pow,log_pow] at hh
  convert hh using 1
  ring

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {F Ξ Z : Type*} [Fintype F] [Fintype Ξ] [Fintype Z]

theorem context_replacement {h ℓ : ℕ} (p : Law Ξ) (E : Finset F) (row : Law E)
    (f : Ξ→Fin ℓ→F) (DD : ((Fin h→F)×(Fin h→F))→Finset F) (B : ℝ)
    (Q : F→F→Prop)
    (hQ : ∀ x,p.mass x≠0→∀ i j,i<j→Q (f x i) (f x j))
    (stream : Ξ→Z) :
    let rows:=(Law.pi (fun _ : Fin h=>row)).prod (Law.pi (fun _ : Fin h=>row))
    let μ:=p.prod rows
    let code:=fun z : Ξ×((Fin h→E)×(Fin h→E))=>
      (fun i=>(z.2.1 i).val,fun i=>(z.2.2 i).val)
    let G:=univ.filter (fun z=>((DD (code z)).card:ℝ)≤B ∧
      ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f z.1 (e i)∈DD (code z))
    (1:ℝ)/2≤μ.event G →
    ∃ hG : 0<μ.event G,
      let ν:=μ.onEvent G hG
      ∃ choose : G→Fin (ℓ/2)↪o Fin ℓ,
      (∀ (z : G) i,f z.val.1 (choose z i)∈DD (code z)) ∧
      (∀ z : G,((DD (code z)).card:ℝ)≤B) ∧
      (∀ z : G,ν.mass z≠0→∀ i j,i<j→Q (f z.val.1 (choose z i)) (f z.val.1 (choose z j))) ∧
      (∀ a,(ν.map (fun z=>stream z.val.1)).mass a≤2*(p.map stream).mass a) ∧
      entropy (ν.map (fun z=>code z))≤2*(h:ℝ)*log (Fintype.card F) := by
  intro rows μ code G hG
  have hG0 : 0<μ.event G := by linarith
  let ν:=μ.onEvent G hG0
  have hx : ∀ z : G,∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f z.val.1 (e i)∈DD (code z) :=
    fun z=>(mem_filter.mp z.property).2.2
  choose ch hc using hx
  refine ⟨hG0,ch,hc,fun z=>(mem_filter.mp z.property).2.1,?_,?_,?_⟩
  · intro z hz i j hij
    have hp : p.mass z.val.1≠0 := by
      intro hp
      apply hz
      change p.mass z.val.1*rows.mass z.val.2/μ.event G=0
      rw [hp,zero_mul,zero_div]
    exact hQ z.val.1 hp _ _ ((ch z).strictMono hij)
  · intro a
    have hh:=μ.onEvent_map_le_two G hG (fun z=>stream z.1) a
    rw [Law.prod_map_left] at hh
    exact hh
  · exact raw_rows_entropy h _ _

end
end SharpLogRamsey.ActualHighRank

end

end OAI
