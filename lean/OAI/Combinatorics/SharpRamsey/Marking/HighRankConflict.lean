import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodRows
import OAI.Combinatorics.SharpRamsey.Trees.GoodChronology

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real FiniteEventBounds
open scoped Classical BigOperators
noncomputable section
variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]

theorem original_forbidden_product (p : Law X) (f : X→A) (g : X→B) (R : A→B→Prop)
    (hc : ∀ x,p.mass x≠0→¬R (f x) (g x)) :
    (∑ x,p.mass x*∑ a,(p.map f).mass a*indicator (R a (g x)))≤
      2*mutualInfo (p.map (fun x=>(f x,g x))) := by
  let joint:=p.map (fun x=>(f x,g x))
  let E:=univ.filter (fun z : A×B=>R z.1 z.2)
  have hzero : joint.event E=0 := by
    apply sum_eq_zero
    intro z hz
    by_contra hh
    obtain ⟨x,hx,he⟩:=p.map_support (fun x=>(f x,g x)) z hh
    have hr := (mem_filter.mp hz).2
    rw [←he] at hr
    exact hc x hx hr
  have hf : joint.fst=p.map f := by
    rw [←Law.map_fst,Law.map_map]
    rfl
  have hg : joint.snd=p.map g := by
    rw [←Law.map_snd,Law.map_map]
    rfl
  have hh:=mutualInfo_event_transfer joint E
  rw [hzero,add_zero,hf,hg] at hh
  have he : ((p.map f).prod (p.map g)).event E=
      ∑ x,p.mass x*∑ a,(p.map f).mass a*indicator (R a (g x)) := by
    simp only [Law.event,E,sum_filter,Law.prod,Fintype.sum_prod_type]
    have hz : ∀ a b,(if R a b then (p.map f).mass a*(p.map g).mass b else 0)=
        (p.map g).mass b*((p.map f).mass a*indicator (R a b)) := by
      intro a b
      by_cases h : R a b <;> simp [indicator,h,mul_comm]
    simp only [hz]
    rw [sum_comm]
    simp only [←mul_sum]
    exact p.sum_map g _
  rw [he] at hh
  exact hh

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional K V] in
theorem high_original_conflict (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι)
    (hc : ∀ x,p.mass x≠0→(x i).1.rep (x j).2.rep=0→(x j).1.rep (x i).2.rep=0) :
    (∑ x,p.mass x*∑ z,(p.marginal i).mass z*
      indicator (z.1.rep (x j).2.rep=0∧(x j).1.rep z.2.rep≠0))≤2*(pairInformation p i j:ℝ) := by
  exact original_forbidden_product p (fun x=>x i) (fun x=>x j)
    (fun z t=>z.1.rep t.2.rep=0∧t.1.rep z.2.rep≠0)
    (fun x hx hh=>hh.2 (hc x hx hh.1))
end
end SharpLogRamsey.Selection

end

end OAI
