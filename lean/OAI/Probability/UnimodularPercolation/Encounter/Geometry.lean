import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! Cut vertices and connected branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open SimpleGraph
universe u w
variable {V : Type u} {W : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

def cutVertex (H : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ≠ x ∧ b ≠ x
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩

noncomputable def branchCount (H : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  ((S.erase x).image (cutVertex H x).connectedComponentMk).card

theorem walk_reachable_cut (H : SimpleGraph V) (T : SimpleGraph W)
    (f : W → V) (hf : ∀ {a b}, T.Adj a b → H.Adj (f a) (f b))
    (x : V) {a b : W} (p : T.Walk a b)
    (hp : ∀ z ∈ p.support, f z ≠ x) :
    (cutVertex H x).Reachable (f a) (f b) := by
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih =>
      apply Reachable.trans (Adj.reachable (G := cutVertex H x) ?_) (ih ?_)
      · exact ⟨hf hab,hp a (by simp),hp b (by simp [p.start_mem_support])⟩
      · intro z hz
        exact hp z (by simp [hz])

theorem branchCount_le_degree [Fintype W] (H : SimpleGraph V) (T : SimpleGraph W)
    (f : W ↪ V) (hf : ∀ {a b}, T.Adj a b → H.Adj (f a) (f b))
    (hT : T.Connected) (S : Finset V) (hS : ∀ z ∈ S, ∃ y, f y = z) (x : W) :
    branchCount H S (f x) ≤ T.degree x := by
  classical
  let g : W → (cutVertex H (f x)).ConnectedComponent :=
    fun y => (cutVertex H (f x)).connectedComponentMk (f y)
  have hsub : (S.erase (f x)).image (cutVertex H (f x)).connectedComponentMk ⊆
      (T.neighborFinset x).image g := by
    intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hyx,hzS⟩ := Finset.mem_erase.mp hz
    obtain ⟨y,rfl⟩ := hS z hzS
    obtain ⟨p,hp⟩ := hT.exists_isPath x y
    cases p with
    | nil => exact False.elim (hyx rfl)
    | @cons x a y hab p =>
        refine Finset.mem_image.mpr ⟨a,(T.mem_neighborFinset x a).mpr hab,?_⟩
        apply ConnectedComponent.sound
        apply walk_reachable_cut H T f hf (f x) p
        intro z hz he
        have hzx := f.injective he
        subst z
        exact (List.nodup_cons.mp hp.support_nodup).1 hz
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))

theorem connected_erase_leaf (H : SimpleGraph V) (D : Finset V)
    (T : SimpleGraph (D:Set V)) (hTH : T ≤ H.induce (D:Set V))
    (hT : T.Connected) (z : (D:Set V)) (hz : T.degree z = 1) :
    (H.induce ((D.erase z.val):Set V)).Connected := by
  let f : ({z}ᶜ : Set (D:Set V)) → ((D.erase z.val):Set V) :=
    fun y => ⟨y.val.val,Finset.mem_erase.mpr ⟨by
      intro h
      apply y.property
      exact Subtype.ext h,y.val.property⟩⟩
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨⟨y.val,(Finset.mem_erase.mp y.property).2⟩,?_⟩,rfl⟩
    intro h
    exact (Finset.mem_erase.mp y.property).1 (congrArg Subtype.val h)
  apply (hT.induce_compl_singleton_of_degree_eq_one hz).map (f := ⟨f,?_⟩) hf
  intro a b hab
  exact hTH hab

theorem exists_pruned_connector (H : SimpleGraph V) (S D : Finset V)
    (hS : S.Nonempty) (hSD : S ⊆ D) (hD : (H.induce (D:Set V)).Connected) :
    ∃ D' : Finset V, D' ⊆ D ∧ S ⊆ D' ∧
      ∃ T : SimpleGraph (D':Set V), T ≤ H.induce (D':Set V) ∧ T.IsTree ∧
        ∀ z : (D':Set V), z.val ∉ S → 2 ≤ T.degree z := by
  classical
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
      obtain ⟨T,hTH,hT⟩ := hD.exists_isTree_le
      by_cases hp : ∀ z : (D:Set V), z.val ∉ S → 2 ≤ T.degree z
      · exact ⟨D,Finset.Subset.refl _,hSD,T,hTH,hT,hp⟩
      push Not at hp
      obtain ⟨z,hzS,hzdeg⟩ := hp
      obtain ⟨s,hs⟩ := hS
      have hsz : s ≠ z.val := fun h => hzS (h ▸ hs)
      have hnon : Nontrivial (D:Set V) := ⟨⟨⟨s,hSD hs⟩,z,fun he => hsz (congrArg Subtype.val he)⟩⟩
      let := hnon
      have hdeg : T.degree z = 1 := by
        have hh := hT.connected.preconnected.minDegree_pos_of_nontrivial
        have hl := T.minDegree_le_degree z
        omega
      have hDel := connected_erase_leaf H D T hTH hT.connected z hdeg
      have hSD' : S ⊆ D.erase z.val := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun he => hzS (he ▸ ha),hSD ha⟩
      obtain ⟨D',hD'D,hSD',T',hT'H,hT',hpr⟩ :=
        ih (D.erase z.val).card (by rw [←hn]; exact Finset.card_erase_lt_of_mem z.property)
          (D.erase z.val) hSD' hDel rfl
      exact ⟨D',hD'D.trans (Finset.erase_subset _ _),hSD',T',hT'H,hT',hpr⟩

theorem sum_branchCount_le (H : SimpleGraph V) (S D : Finset V)
    (hS : S.Nonempty) (hSD : S ⊆ D) (hD : (H.induce (D:Set V)).Connected) :
    (∑ x ∈ S, branchCount H S x) + 2 ≤ 2*S.card := by
  classical
  obtain ⟨D',_,hSD',T,hTH,hT,hpr⟩ := exists_pruned_connector H S D hS hSD hD
  let f : (D':Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hb (z : (D':Set V)) : branchCount H S z.val ≤ T.degree z :=
    branchCount_le_degree H T f (fun h => hTH h) hT.connected S
      (fun y hy => ⟨⟨y,hSD' hy⟩,rfl⟩) z
  have hsum : (∑ z : (D':Set V), if z.val ∈ S then branchCount H S z.val else 2) ≤
      ∑ z : (D':Set V), T.degree z := by
    apply Finset.sum_le_sum
    intro z _
    split_ifs with hz
    · exact hb z
    · exact hpr z hz
  have hsplit : (∑ z : (D':Set V), if z.val ∈ S then branchCount H S z.val else 2) =
      (∑ z ∈ S, branchCount H S z) + 2*(D'.card-S.card) := by
    rw [Finset.sum_finset_coe (fun z => if z ∈ S then branchCount H S z else 2) D']
    rw [Finset.sum_ite]
    simp only [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hSD',
      ←Finset.sdiff_eq_filter]
    simp only [Finset.sum_const,smul_eq_mul,Finset.card_sdiff_of_subset hSD',mul_comm]
  rw [hsplit,T.sum_degrees_eq_twice_card_edges] at hsum
  have hcard := hT.card_edgeFinset
  have hDcard : Fintype.card (D':Set V) = D'.card := by simp
  rw [hDcard] at hcard
  have hle := Finset.card_le_card hSD'
  omega

end Percolation

end OAI
