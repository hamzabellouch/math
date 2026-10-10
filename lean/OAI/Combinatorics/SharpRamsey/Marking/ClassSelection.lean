import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.ClassConditioning

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ ι κ : Type*} [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ]

def classSlots (U : Γ→Finset ι) (colour : Γ→ι→κ) (z : Γ) (c : κ) : Finset ι :=
  (U z).filter (fun i=>colour z i=c)

theorem exists_fixed_class (p : Law Ω) (θ : Ω→Γ) (U : Γ→Finset ι)
    (colour : Γ→ι→κ) (n : ℕ)
    (hcard : ∀ x,p.mass x≠0→Fintype.card κ*n≤(U (θ x)).card) :
    ∃ c : κ,1/(Fintype.card κ:ℝ)≤
      (p.map θ).event (univ.filter (fun z=>n≤(classSlots U colour z c).card)) := by
  have hex z (hz : (p.map θ).mass z≠0) :
      ∃ c : κ,n≤(classSlots U colour z c).card := by
    obtain ⟨x,hx,rfl⟩ := p.map_support θ z hz
    obtain ⟨c,_,hc⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s:=U (θ x)) (t:=univ) (f:=colour (θ x)) (n:=n)
      (fun _ _=>mem_univ _) univ_nonempty (by simpa using hcard x hx)
    exact ⟨c,hc⟩
  let win : Γ→κ := fun z=>if hz : (p.map θ).mass z≠0 then Classical.choose (hex z hz)
    else Classical.choice inferInstance
  have hw z (hz : (p.map θ).mass z≠0) : n≤(classSlots U colour z (win z)).card := by
    simp only [win,dite_eq_left hz]
    exact Classical.choose_spec (hex z hz)
  have hp : (0:ℝ)<Fintype.card κ := by exact_mod_cast Fintype.card_pos
  obtain ⟨c,hc⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum
    (f:=win) (w:=(p.map θ).mass) (b:=1/(Fintype.card κ:ℝ)) (by
      rw [nsmul_eq_mul,(p.map θ).total]
      exact le_of_eq (mul_one_div_cancel (ne_of_gt hp)))
  refine ⟨c,hc.trans ?_⟩
  simp only [Law.event,sum_filter]
  apply sum_le_sum
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp [hz]
  by_cases hc' : win z=c
  · rw [ite_eq_left hc',ite_eq_left (by simpa only [hc'] using hw z hz)]
  · rw [ite_eq_right hc']
    split_ifs
    · exact (p.map θ).nonneg z
    · exact le_refl 0

omit [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ] in

def fixedSubset (A : Finset ι) (n : ℕ) : Finset ι :=
  if hn : n≤A.card then Classical.choose (exists_subset_card_eq hn) else ∅

omit [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ] in
lemma fixedSubset_spec (A : Finset ι) (n : ℕ) (hn : n≤A.card) :
    fixedSubset A n⊆A ∧ (fixedSubset A n).card=n := by
  simp only [fixedSubset,dite_eq_left hn]
  exact Classical.choose_spec (exists_subset_card_eq hn)

theorem common_class_extraction (p : Law Ω) (θ : Ω→Γ) (U : Γ→Finset ι)
    (colour : Γ→ι→κ) (n : ℕ)
    (hcard : ∀ x,p.mass x≠0→Fintype.card κ*n≤(U (θ x)).card) :
    ∃ (c : κ) (E : Finset Γ) (S : Γ→Finset ι),
      1/(Fintype.card κ:ℝ)≤(p.map θ).event E ∧
      (∀ z∈E,(S z).card=n ∧ S z⊆U z ∧ ∀ i∈S z,colour z i=c) := by
  obtain ⟨c,hc⟩ := exists_fixed_class p θ U colour n hcard
  refine ⟨c,univ.filter (fun z=>n≤(classSlots U colour z c).card),
    (fun z=>fixedSubset (classSlots U colour z c) n),hc,?_⟩
  intro z hz
  obtain ⟨hs,hn⟩ := fixedSubset_spec (classSlots U colour z c) n (mem_filter.mp hz).2
  refine ⟨hn,hs.trans (filter_subset _ _),?_⟩
  intro i hi
  exact (mem_filter.mp (hs hi)).2

end
end SharpLogRamsey.Selection

end

end OAI
