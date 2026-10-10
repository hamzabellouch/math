import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedGeometry
import OAI.Combinatorics.SharpRamsey.Geometry.RadialPairCount
import OAI.Combinatorics.SharpRamsey.Geometry.SpanPairLine

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β γ : Type*}

lemma list_union_inter_card_le (U : β → Finset α) (bs : List β)
    (L : Finset α) (hL : ∀ b ∈ bs, (U b ∩ L).card ≤ 1) :
    (bs.toFinset.biUnion U ∩ L).card ≤ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.toFinset_cons,biUnion_insert,union_inter_distrib_right]
    have h1 := hL b (by simp)
    have h2 := ih (fun c hc => hL c (by simp [hc]))
    have hh := card_union_le (U b ∩ L) (bs.toFinset.biUnion U ∩ L)
    simp only [List.length_cons]
    omega

theorem prepared_list_radial {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs)
    (A : Finset α) (G : Finset γ) (L : γ → Finset α) (r : ℕ) (hr0 : 0 < r)
    (hplane : ∀ b ∈ bs, ∀ j ∈ G, ¬ L j ⊆ U b → (U b ∩ L j).card ≤ 1)
    (hunique : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → (L i ∩ L j).card ≤ 1) :
    ((A ×ˢ G).filter (fun z => z.1 ∈ L z.2 ∧
      bs.length+r ≤ ((removed S U bs \ own S U bs z.1) ∩ L z.2).card)).card *
      (r*(r-1)) ≤ (removed S U bs).card^2 := by
  let C := indexedCell S U bs
  let E : Fin bs.length → Finset γ := fun i => G.filter (fun j =>
    L j ⊆ U bs[i.val] ∧ (∀ b ∈ bs.take i.val, ¬ L j ⊆ U b) ∧
    r ≤ (C i ∩ L j).card)
  let centers : Fin bs.length → γ → Finset α := fun i j =>
    (bs.take i.val).toFinset.biUnion U ∩ L j
  have hcenter (i : Fin bs.length) (j : γ) (hj : j ∈ E i) :
      (centers i j).card ≤ i.val := by
    have hj' := mem_filter.mp hj
    have hh := list_union_inter_card_le U (bs.take i.val) (L j) (fun b hb =>
      hplane b (List.mem_of_mem_take hb) j hj'.1 (hj'.2.2.1 b hb))
    exact hh.trans (List.length_take_le _ _)
  have hcover : (A ×ˢ G).filter (fun z => z.1 ∈ L z.2 ∧
      bs.length+r ≤ ((removed S U bs \ own S U bs z.1) ∩ L z.2).card) ⊆
      univ.biUnion (fun i => (E i).biUnion (fun j => centers i j ×ˢ {j})) := by
    intro z hz
    obtain ⟨hzAG,hzx,hzrich⟩ := mem_filter.mp hz
    have hjG := (mem_product.mp hzAG).2
    have hex : ∃ b ∈ bs, L z.2 ⊆ U b := by
      by_contra hn
      push Not at hn
      have hb := removed_inter_card_le S U bs (L z.2)
        (fun b hb => hplane b hb z.2 hjG (hn b hb))
      have hs : ((removed S U bs \ own S U bs z.1) ∩ L z.2).card ≤
          (removed S U bs ∩ L z.2).card :=
        card_le_card (inter_subset_inter_right sdiff_subset)
      omega
    obtain ⟨pre,b,post,he,hLb,hpre⟩ := first_containing U bs (L z.2) hex
    have hplen : pre.length < bs.length := by rw [he,List.length_append,List.length_cons]; omega
    let i : Fin bs.length := ⟨pre.length,hplen⟩
    have htake : bs.take i.val = pre := by simp [i,he]
    have hget : bs[i.val] = b := by simp [i,he,List.getElem_append_right]
    have hpreline : ∀ c ∈ pre, (U c ∩ L z.2).card ≤ 1 := by
      intro c hc
      exact hplane c (by rw [he]; simp [hc]) z.2 hjG (hpre c hc)
    have hci : r ≤ (C i ∩ L z.2).card := by
      have hh := removed_line_le_prefix_cell S U pre b post (L z.2) hLb hpreline
      have hs : ((removed S U bs \ own S U bs z.1) ∩ L z.2).card ≤
          (removed S U bs ∩ L z.2).card :=
        card_le_card (inter_subset_inter_right sdiff_subset)
      have hce : C i = residual S U pre ∩ U b := by
        dsimp [C,indexedCell]
        rw [htake,hget]
      rw [hce]
      rw [← he] at hh
      omega
    have hearlier : z.1 ∈ pre.toFinset.biUnion U := by
      by_contra hn
      have hxpre : ∀ c ∈ pre, z.1 ∉ U c := by
        intro c hc hxc
        exact hn (mem_biUnion.mpr ⟨c,List.mem_toFinset.mpr hc,hxc⟩)
      have hh := outside_inter_prefix S U pre b post (L z.2) hLb z.1 hzx hxpre hpreline
      rw [← he] at hh
      omega
    refine mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨z.2,?_,?_⟩⟩
    · apply mem_filter.mpr
      refine ⟨hjG,?_,?_,hci⟩
      · rw [hget]; exact hLb
      · simpa only [htake] using hpre
    · exact mem_product.mpr ⟨by simpa only [centers,htake] using
        (mem_inter.mpr ⟨hearlier,hzx⟩),mem_singleton_self _⟩
  calc
    _ ≤ ((univ.biUnion (fun i => (E i).biUnion (fun j => centers i j ×ˢ {j}))).card)*
        (r*(r-1)) := Nat.mul_le_mul_right _ (card_le_card hcover)
    _ ≤ (∑ i, (C i).card)^2 :=
      RadialPairCount.centered_rich_lines C E L centers r
        (fun _ _ hj => (mem_filter.mp hj).2.2.2)
        (fun a ha b hb hab => hunique a
          (by obtain ⟨i,_,hi⟩ := mem_biUnion.mp ha; exact (mem_filter.mp hi).1)
          b (by obtain ⟨i,_,hi⟩ := mem_biUnion.mp hb; exact (mem_filter.mp hi).1) hab)
        hcenter (indexedCell_antitone h)
    _ = _ := by rw [indexedCell_sum]

end
end SharpLogRamsey.GreedyPreparation
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedRadial_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedRadial_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedPreparedRadial_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPreparedRadial_4 : Fintype (Submodule K V) := Fintype.ofFinite _

def planePoints (W : Submodule K V) : Finset (Projectivization K V) :=
  univ.filter (fun x => x.submodule ≤ W)

@[simp] lemma mem_planePoints {W : Submodule K V} {x : Projectivization K V} :
    x ∈ planePoints W ↔ x.submodule ≤ W := by simp [planePoints]

lemma points_mono {U W : Submodule K V} (h : U ≤ W) : planePoints U ⊆ planePoints W := by
  intro x hx
  exact mem_planePoints.mpr ((mem_planePoints.mp hx).trans h)

omit [Finite K] in

lemma join_eq_line (x y : Projectivization K V) (hne : x ≠ y)
    (W : Submodule K V) (hW : Module.finrank K W = 2)
    (hx : x.submodule ≤ W) (hy : y.submodule ≤ W) :
    x.submodule ⊔ y.submodule = W :=
  Submodule.eq_of_le_of_finrank_eq (sup_le hx hy) ((finrank_join x y hne).trans hW.symm)

lemma line_inter_points_le_one (W U : Submodule K V) (hW : Module.finrank K W = 2)
    (hnot : ¬ planePoints W ⊆ planePoints U) :
    (planePoints U ∩ planePoints W).card ≤ 1 := by
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < (planePoints U ∩ planePoints W).card)
  have hx' := mem_inter.mp hx
  have hy' := mem_inter.mp hy
  have he := join_eq_line x y hxy W hW (mem_planePoints.mp hx'.2) (mem_planePoints.mp hy'.2)
  apply hnot
  apply points_mono
  rw [← he]
  exact sup_le (mem_planePoints.mp hx'.1) (mem_planePoints.mp hy'.1)

lemma distinct_lines_inter_le_one (W U : Submodule K V)
    (hW : Module.finrank K W = 2) (hU : Module.finrank K U = 2) (hne : W ≠ U) :
    (planePoints W ∩ planePoints U).card ≤ 1 := by
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < (planePoints W ∩ planePoints U).card)
  have hx' := mem_inter.mp hx
  have hy' := mem_inter.mp hy
  have heW := join_eq_line x y hxy W hW (mem_planePoints.mp hx'.1) (mem_planePoints.mp hy'.1)
  have heU := join_eq_line x y hxy U hU (mem_planePoints.mp hx'.2) (mem_planePoints.mp hy'.2)
  exact hne (heW.symm.trans heU)

def ProjectiveLine := {W : Submodule K V // Module.finrank K W = 2}
instance flat_JoinedPreparedRadial_5 : Fintype (ProjectiveLine (K:=K) (V:=V)) := by unfold ProjectiveLine; infer_instance

theorem projective_prepared_radial (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (r : ℕ) (hr : 0 < r) :
    ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
      (fun z => z.1 ∈ planePoints z.2.1 ∧ bs.length+r ≤
        ((GreedyPreparation.removed S planePoints bs \
          (GreedyPreparation.own S planePoints bs z.1 ∪ {z.1})) ∩ planePoints z.2.1).card)).card *
      (r*(r-1)) ≤ (GreedyPreparation.removed S planePoints bs).card^2 := by
  have hh := GreedyPreparation.prepared_list_radial h univ univ
    (fun W : ProjectiveLine (K:=K) (V:=V) => planePoints W.1) r hr
    (fun b _ W _ hn => line_inter_points_le_one W.1 b W.2 hn)
    (fun W _ U _ hne => distinct_lines_inter_le_one W.1 U.1 W.2 U.2
      (fun he => hne (Subtype.ext he)))
  apply le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) hh
  intro z hz
  have hz' := (mem_filter.mp hz).2
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_univ _,mem_univ _⟩,hz'.1,hz'.2.trans ?_⟩
  apply card_le_card
  apply inter_subset_inter_right
  exact sdiff_subset_sdiff subset_rfl subset_union_left

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
