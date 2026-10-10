import OAI.Probability.ContinuumTransition.PackingGeometry

namespace OAI

universe u_1

section
open scoped BigOperators
open Set
namespace ContinuumTemperature
open Classical

def FreeConfig {ι : Type u_1} (t : ℝ) (x : ι → Space) : Prop :=
  ∀ i j, i ≠ j → ‖x i-x j‖ < 1 →
    Real.exp (-t) ≤ ‖x i-x j‖ ∧ ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)

theorem freeConfig_injective {ι : Type u_1} {t : ℝ} {x : ι → Space}
    (hx : FreeConfig t x) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have hh := (hx i j hne (by rw [hij, sub_self, norm_zero]; norm_num)).1
  rw [hij,sub_self,norm_zero] at hh
  exact (not_le_of_gt (Real.exp_pos _)) hh

theorem freeConfig_close_trans {ι : Type u_1} {t : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x)
    {i j k : ι} (hij : ‖x i-x j‖ < 1) (hjk : ‖x j-x k‖ < 1) :
    ‖x i-x k‖ < 1 := by
  by_cases he : i = j
  · simpa only [he] using hjk
  by_cases hf : j = k
  · simpa only [hf] using hij
  have hi := (hx i j he hij).2
  have hj := (hx j k hf hjk).2
  have hh := norm_sub_le_norm_sub_add_norm_sub (x i) (x j) (x k)
  linarith only [hi,hj,hh,ht]

noncomputable def freeSetoid {ι : Type u_1} {t : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x) : Setoid ι where
  r i j := ‖x i-x j‖ < 1
  iseqv := ⟨by intro i; simp,
    by intro i j h; rwa [norm_sub_rev],
    by intro i j k; exact freeConfig_close_trans ht hx⟩

noncomputable def freeCluster {ι : Type u_1} [Fintype ι] (x : ι → Space) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => ‖x i-x j‖ < 1)

theorem mem_freeCluster {ι : Type u_1} [Fintype ι] {x : ι → Space} {i j : ι} :
    j ∈ freeCluster x i ↔ ‖x i-x j‖ < 1 := by simp [freeCluster]

theorem freeCluster_card_le_four {ι : Type u_1} [Fintype ι] {t : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x) (i : ι) :
    (freeCluster x i).card ≤ 4 := by
  have hc : (shellGraph x (Real.exp (-t))).IsClique (freeCluster x i : Set ι) := by
    intro j hj k hk hjk
    have hi : ‖x j-x i‖ < 1 := by simpa only [norm_sub_rev] using mem_freeCluster.mp hj
    have hh := freeConfig_close_trans ht hx hi (mem_freeCluster.mp hk)
    exact ⟨hjk,hx j k hjk hh⟩
  have hcf := shellGraph_cliqueFree x (Real.exp_pos (-t))
  by_contra hn
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ (freeCluster x i).card)
  exact hcf s ⟨hc.subset (by exact_mod_cast hs), hcard⟩

theorem freeCluster_close_root {ι : Type u_1} [Fintype ι] {t : ℝ} {x : ι → Space}
    (hx : FreeConfig t x) {i j : ι} (hj : j ∈ freeCluster x i) :
    ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t) := by
  by_cases he : i=j
  · rw [he,sub_self,norm_zero]
    unfold shellDelta
    positivity
  exact (hx i j he (mem_freeCluster.mp hj)).2

theorem free_component_card_le_packing {ι : Type u_1} [Fintype ι] {t L : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x)
    (hL : ∀ i, x i ∈ cube L) :
    Fintype.card (Quotient (freeSetoid ht hx)) ≤ packingNumber L := by
  let f : Quotient (freeSetoid ht hx) → Space := fun c => x c.out
  apply card_le_packingNumber f (fun c => hL c.out)
  intro a b hab
  by_contra hlt
  have hh : (freeSetoid ht hx).r a.out b.out := lt_of_not_ge hlt
  have he := Quotient.sound hh
  exact hab (by simpa only [Quotient.out_eq] using he)

end ContinuumTemperature
end

end OAI
