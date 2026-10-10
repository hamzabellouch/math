import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRankEndpoints
import OAI.Combinatorics.SharpRamsey.Marking.AtomEscape

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]

lemma Law.event_filter_mean (p : Law X) (P : X→Prop) :
    p.event (univ.filter P)=∑ x,p.mass x*(if P x then 1 else 0) := by
  simp only [Law.event,sum_filter]
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp

lemma Law.onEvent_mean_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→ℝ) (hf : ∀ x,0≤f x) :
    ∑ x : E,(p.onEvent E (by linarith)).mass x*f x≤2*∑ x,p.mass x*f x := by
  rw [p.onEvent_mean]
  apply (div_le_iff₀ (by linarith : 0<p.event E)).mpr
  have hn : 0≤∑ x,p.mass x*f x := sum_nonneg (fun x _=>mul_nonneg (p.nonneg x) (hf x))
  calc
    _ ≤ ∑ x,p.mass x*f x := sum_le_univ_sum_of_nonneg (fun x=>mul_nonneg (p.nonneg x) (hf x))
    _ ≤ _ := by nlinarith

lemma Law.map_mass_eq_marginal (p : Law X) (f : X→Y) (y : Y) :
    (p.map f).mass y=FiniteMarginals.marginal p.mass f y := by
  simp only [Law.map,FiniteMarginals.marginal,sum_filter]

lemma Law.onEvent_map_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→Y) (y : Y) :
    ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y≤2*(p.map f).mass y := by
  have hh:=p.onEvent_mean_le_two E hE (fun x=>if f x=y then 1 else 0) (by intro x; split_ifs <;> positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using hh

lemma good_pair_event (p : Law (A×B)) (PA : A→Prop) (PB : B→Prop) (εA εB : ℝ)
    (hA : p.fst.event (univ.filter (fun a=>¬PA a))≤εA)
    (hB : p.snd.event (univ.filter (fun b=>¬PB b))≤εB) :
    1-εA-εB≤p.event (univ.filter (fun z=>PA z.1∧PB z.2)) := by
  have he : 1-p.event (univ.filter (fun z=>PA z.1∧PB z.2)) =
      p.event (univ.filter (fun z=>¬(PA z.1∧PB z.2))) := by
    simp only [Law.event,sum_filter]
    rw [←p.total,←sum_sub_distrib]
    apply sum_congr rfl
    intro z _
    by_cases h : PA z.1∧PB z.2 <;> simp [h]
  have hh:=p.event_not_and (fun z=>PA z.1) (fun z=>PB z.2)
  have ha : p.event (univ.filter (fun z=>¬PA z.1))=p.fst.event (univ.filter (fun a=>¬PA a)) := by
    have hh:=p.sum_map Prod.fst (fun a=>if ¬PA a then 1 else 0)
    rw [Law.map_fst] at hh
    simpa only [Law.event,sum_filter,mul_ite,mul_one,mul_zero] using hh.symm
  have hb : p.event (univ.filter (fun z=>¬PB z.2))=p.snd.event (univ.filter (fun b=>¬PB b)) := by
    have hh:=p.sum_map Prod.snd (fun b=>if ¬PB b then 1 else 0)
    rw [Law.map_snd] at hh
    simpa only [Law.event,sum_filter,mul_ite,mul_one,mul_zero] using hh.symm
  rw [ha,hb] at hh
  linarith

lemma Law.onEvent_map_cap (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→Y) (U : ℝ) (hU : 0≤U)
    (hcap : ∀ x∈E,(p.map f).mass (f x)≤U) (y : Y) :
    ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y≤2*U := by
  by_cases hy : ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y=0
  · rw [hy]; positivity
  obtain ⟨x,hx,he⟩:=(p.onEvent E (by linarith)).map_support (fun x : E=>f x) y hy
  have hh:=p.onEvent_map_le_two E hE f y
  rw [←he] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_left (hcap x x.property) (by norm_num))

theorem high_good_rows (p : Law (A×B)) (MA MB L κ UA UB ε : ℝ)
    (hUA : 0≤UA) (hUB : 0≤UB) (hε : ε≤1/4)
    (hA : p.fst.event (univ.filter (fun a=>¬highGoodFirst p MA L κ UA a))≤ε)
    (hB : p.snd.event (univ.filter (fun b=>¬highGoodSecond p MB L κ UB b))≤ε) :
    let E:=univ.filter (fun z : A×B=>highGoodFirst p MA L κ UA z.1∧highGoodSecond p MB L κ UB z.2)
    ∃ hE : (1:ℝ)/2≤p.event E,
      (∀ a,FiniteMarginals.marginal (p.onEvent E (by linarith)).mass (fun z=>z.val.1) a≤2*UA) ∧
      (∀ b,FiniteMarginals.marginal (p.onEvent E (by linarith)).mass (fun z=>z.val.2) b≤2*UB) ∧
      (∀ f : A×B→ℝ,(∀ z,0≤f z)→
        (∑ z : E,(p.onEvent E (by linarith)).mass z*f z)≤2*∑ z,p.mass z*f z) := by
  let E:=univ.filter (fun z : A×B=>highGoodFirst p MA L κ UA z.1∧highGoodSecond p MB L κ UB z.2)
  have hE : (1:ℝ)/2≤p.event E := by
    have hh:=good_pair_event p _ _ ε ε hA hB
    change 1-ε-ε≤p.event E at hh
    linarith
  refine ⟨hE,?_,?_,fun f hf=>p.onEvent_mean_le_two E hE f hf⟩
  · intro a
    rw [←Law.map_mass_eq_marginal]
    apply p.onEvent_map_cap E hE Prod.fst UA hUA
    intro z hz
    rw [Law.map_fst]
    exact (mem_filter.mp hz).2.1.2
  · intro b
    rw [←Law.map_mass_eq_marginal]
    apply p.onEvent_map_cap E hE Prod.snd UB hUB
    intro z hz
    rw [Law.map_snd]
    exact (mem_filter.mp hz).2.2.2
end
end SharpLogRamsey.Selection

end

end OAI
