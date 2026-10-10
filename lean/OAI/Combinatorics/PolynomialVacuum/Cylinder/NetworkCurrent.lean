import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkDecomposition
import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkFromFlow

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
namespace ClosedNetwork
variable {M : ℕ} (C : ClosedNetwork M)

noncomputable def flow : Edge M →₀ ℤ := ∑ v : C.sites,dartFlow (v.val,C.exit v)

 

theorem oriented_flow : orientedFlow C.flow =
    ∑ v : C.sites,(Finsupp.single (v.val,C.exit v) 1-Finsupp.single (v.val,C.enter v) 1) := by
  simp only [flow,map_sum,orientedFlow_dartFlow,Finset.sum_sub_distrib]
  congr 1
  have hs := Equiv.sum_comp C.next (fun v : C.sites => Finsupp.single (v.val,C.enter v) (1 : ℤ))
  rw [← hs]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  change (neighbor v.val (C.exit v),C.exit v)=((C.next v).val,C.enter (C.next v))
  rw [C.incident,C.matching]

theorem oriented_flow_at (v : C.sites) (k : Fin 3) :
    orientedFlow C.flow (v.val,k)=(if k=C.exit v then 1 else 0)-(if k=C.enter v then 1 else 0) := by
  rw [C.oriented_flow]
  simp only [Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.sub_apply]
  rw [Finset.sum_eq_single v]
  · simp [Finsupp.single_apply,eq_comm]
  · intro u _ huv
    have h : u.val≠v.val := fun he => huv (Subtype.ext he)
    simp [h]
  · simp

theorem oriented_flow_off (x : Vertex M) (hx : x∉C.sites) (k : Fin 3) :
    orientedFlow C.flow (x,k)=0 := by
  rw [C.oriented_flow]
  simp only [Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.sub_apply]
  apply Finset.sum_eq_zero
  intro v _
  have h : v.val≠x := by intro he; exact hx (he ▸ v.property)
  simp [h]

theorem flow_localIce (v : Vertex M) : LocalIce C.flow v := by
  by_cases hv : v∈C.sites
  · right
    let u : C.sites:=⟨v,hv⟩
    exact ⟨C.enter u,C.exit u,C.distinct u,C.oriented_flow_at u⟩
  · exact Or.inl (C.oriented_flow_off v hv)

theorem word_flow (k : ℕ) (v : C.sites) :
    wordFlow (C.germ v) (C.word k v)=
      ∑ j∈Finset.range k,dartFlow ((C.next^[j] v).val,C.exit (C.next^[j] v)) := by
  induction k generalizing v with
  | zero => simp [word,wordFlow]
  | succ k ih =>
    simp only [word,wordFlow,C.outgoing_turn,C.advance_turn,ih]
    rw [Finset.sum_range_succ']
    simp only [Function.iterate_zero,Function.id_def,Function.iterate_succ_apply]
    exact add_comm _ _

end ClosedNetwork

theorem orientedFlow_injective {M : ℕ} : Function.Injective (orientedFlow (M:=M)) := by
  intro q r h
  ext e
  rcases e with ⟨⟨i,j⟩,k⟩
  have hh := congrArg (fun f : Germ M →₀ ℤ => f (.up i j,k)) h
  simpa only [orientedFlow_up] using hh

namespace IceNetwork
variable {M : ℕ} (q : Edge M →₀ ℤ) (hq : ∀ v,LocalIce q v)
include hq

 

theorem recover_flow : (network q hq).flow=q := by
  apply orientedFlow_injective
  ext g
  rcases g with ⟨v,k⟩
  by_cases hv : v∈activeSites q
  · rw [(network q hq).oriented_flow_at ⟨v,hv⟩]
    exact (at_slot q hq ⟨v,hv⟩ k).symm
  · rw [(network q hq).oriented_flow_off v hv]
    exact (not_ne_iff.mp (fun hc => hv ((mem_activeSites q v).mpr ⟨k,hc⟩))).symm

end IceNetwork
end PolynomialVacuumCylinder

end OAI
