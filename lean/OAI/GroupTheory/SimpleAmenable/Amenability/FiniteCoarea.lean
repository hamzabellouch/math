import Mathlib
import OAI.GroupTheory.SimpleAmenable.Model

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCoarea

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def graphVariation (u v : E → V) (w : V → ℝ) : ℝ :=
  ∑ e, |w (u e) - w (v e)|

noncomputable def graphBoundary (u v : E → V) (A : Finset V) : ℝ := by
  classical
  exact graphVariation u v (fun x => if x ∈ A then 1 else 0)

theorem finite_coarea (u v : E → V) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ε : ℝ) (h : graphVariation u v w < ε * ∑ x, w x) :
    ∃ A : Finset V, A.Nonempty ∧ (∀ x ∈ A, 0 < w x) ∧
      graphBoundary u v A < ε * A.card := by
  classical
  let S : Finset V := Finset.univ.filter (fun x => 0 < w x)
  suffices aux : ∀ n : ℕ, ∀ w : V → ℝ, (∀ x, 0 ≤ w x) →
      (Finset.univ.filter (fun x => 0 < w x)).card = n →
      graphVariation u v w < ε * ∑ x, w x →
      ∃ A : Finset V, A.Nonempty ∧ (∀ x ∈ A, 0 < w x) ∧
        graphBoundary u v A < ε * A.card from aux S.card w hw rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro w hw hn h
      let S : Finset V := Finset.univ.filter (fun x => 0 < w x)
      have hs : ∀ x, x ∈ S ↔ 0 < w x := by simp [S]
      have hS : S.Nonempty := by
        by_contra he
        have hz (x : V) : w x = 0 := by
          have : ¬ 0 < w x := fun hp => he ⟨x,(hs x).mpr hp⟩
          linarith [hw x]
        simp [graphVariation,hz] at h
      obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image S w hS
      let δ := w i
      have hd : 0 < δ := (hs i).mp hi
      let q : V → ℝ := fun x => if x ∈ S then w x - δ else 0
      have hq (x : V) : 0 ≤ q x := by
        dsimp only [q]
        split_ifs with hx
        · exact sub_nonneg.mpr (hmin x hx)
        · rfl
      have hw0 (x : V) (hx : x ∉ S) : w x = 0 := by
        have : ¬ 0 < w x := fun hp => hx ((hs x).mpr hp)
        linarith [hw x]
      have hwq (x : V) : w x = q x + δ * (if x ∈ S then 1 else 0) := by
        by_cases hx : x ∈ S
        · simp [q,hx]
        · simp [q,hx,hw0 x hx]
      have coeff (x y : V) :
          |w x - w y| = |q x - q y| + δ *
            |(if x ∈ S then (1 : ℝ) else 0) - (if y ∈ S then 1 else 0)| := by
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · simp [q,hx,hy]
        · have hqx : 0 ≤ w x - δ := by simpa [q,hx] using hq x
          simp only [q,hx,hy,ite_true,ite_false,hw0 y hy,sub_zero,abs_one,mul_one]
          rw [abs_of_nonneg (hw x),abs_of_nonneg hqx]
          ring
        · have hqy : 0 ≤ w y - δ := by simpa [q,hy] using hq y
          simp only [q,hx,hy,ite_true,ite_false,hw0 x hx,zero_sub,abs_neg,abs_one,mul_one]
          rw [abs_of_nonneg (hw y),abs_of_nonneg hqy]
          ring
        · simp [q,hx,hy,hw0 x hx,hw0 y hy]
      have hvar : graphVariation u v w = graphVariation u v q + δ * graphBoundary u v S := by
        unfold graphBoundary graphVariation
        simp_rw [coeff]
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      have hmass : (∑ x, w x) = (∑ x, q x) + δ * S.card := by
        simp only [hwq,Finset.sum_add_distrib,← Finset.mul_sum]
        congr 1
        simp
      by_cases hb : graphBoundary u v S < ε * S.card
      · exact ⟨S,hS,fun x hx => (hs x).mp hx,hb⟩
      · have hrec : graphVariation u v q < ε * ∑ x, q x := by
          rw [hvar,hmass] at h
          have hbd : ε * S.card ≤ graphBoundary u v S := le_of_not_gt hb
          nlinarith
        let T := Finset.univ.filter (fun x => 0 < q x)
        have hTS : T ⊆ S := by
          intro x hx
          have hqx : 0 < q x := (Finset.mem_filter.mp hx).2
          by_contra hxS
          simp [q,hxS] at hqx
        have hiT : i ∉ T := by simp [T,q,hi,δ]
        have hc : T.card < n := by
          rw [← hn]
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hTS,fun he => hiT (he.symm ▸ hi)⟩)
        obtain ⟨A,hA,hAw,hAb⟩ := ih T.card hc q hq rfl hrec
        refine ⟨A,hA,?_,hAb⟩
        intro x hx
        have hp := hAw x hx
        have hqS : x ∈ S := hTS (by simp [T,hp])
        exact (hs x).mp hqS

end FiniteCoarea

section WeightedGroupCoarea

variable {G : Type*} [Group G] [DecidableEq G]

noncomputable def translationWindow (K S : Finset G) : Finset G := by
  classical
  exact S ∪ K.biUnion (fun k => S.image (fun x => k*x))

noncomputable def weightedVariation (K S : Finset G) (p : G → ℝ) : ℝ :=
  ∑ k ∈ K, ∑ x ∈ translationWindow K S, |p (k⁻¹*x) - p x|

theorem weighted_group_coarea (K S : Finset G) (p : G → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∀ x ∉ S, p x = 0) (ε : ℝ)
    (h : weightedVariation K S p < ε * ∑ x ∈ S, p x) :
    ∃ D : Finset G, D.Nonempty ∧ D ⊆ S ∧
      (∑ k ∈ K, ((symmDiff (D.image (fun x => k*x)) D).card : ℝ)) < ε * D.card := by
  classical
  let B := translationWindow K S
  let node : G → Option {x // x ∈ S} := fun x => if hx : x ∈ S then some ⟨x,hx⟩ else none
  let w : Option {x // x ∈ S} → ℝ := fun z => match z with
    | none => 0
    | some x => p x.val
  let u : {k // k ∈ K} × {x // x ∈ B} → Option {x // x ∈ S} :=
    fun e => node (e.1.val⁻¹ * e.2.val)
  let v : {k // k ∈ K} × {x // x ∈ B} → Option {x // x ∈ S} :=
    fun e => node e.2.val
  have hwnode (x : G) : w (node x) = p x := by
    by_cases hx : x ∈ S
    · simp [node,w,hx]
    · simp [node,w,hx,hs x hx]
  have hw : ∀ z, 0 ≤ w z := by intro z; cases z with
    | none => exact le_rfl
    | some z => exact hp z.val
  have hm : (∑ z, w z) = ∑ x ∈ S, p x := by
    simp [w,Fintype.sum_option,Finset.sum_attach]
  have hv : graphVariation u v w = weightedVariation K S p := by
    simp only [graphVariation,Fintype.sum_prod_type,u,v,hwnode]
    unfold weightedVariation
    rw [← Finset.sum_coe_sort K]
    apply Fintype.sum_congr
    intro k
    rw [← Finset.sum_coe_sort (translationWindow K S)]
  obtain ⟨A,hA,hpos,hbd⟩ := finite_coarea u v w hw ε (by rwa [hv,hm])
  have hn : (none : Option {x // x ∈ S}) ∉ A := by
    intro hn
    have hh := hpos none hn
    exact (lt_irrefl 0) hh
  let D : Finset G := S.filter (fun x => node x ∈ A)
  have hDS : D ⊆ S := Finset.filter_subset _ _
  have hnode (x : G) : node x ∈ A ↔ x ∈ D := by
    by_cases hx : x ∈ S
    · simp [D,hx]
    · simp [node,D,hx,hn]
  have hmap : D.image node = A := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact (hnode x).mpr hx
    · intro hz
      cases z with
      | none => exact False.elim (hn hz)
      | some x =>
          have he : node x.val = some x := by simp [node,x.property]
          exact Finset.mem_image.mpr ⟨x.val,(hnode x.val).mp (he ▸ hz),he⟩
  have hc : A.card = D.card := by
    rw [← hmap]
    apply Finset.card_image_iff.mpr
    intro x hx y hy he
    have hxS := hDS hx
    have hyS := hDS hy
    simp only [node,hxS,hyS,dite_eq_left,Option.some.injEq,Subtype.mk.injEq] at he
    exact he
  have hDn : D.Nonempty := by
    rw [← hmap] at hA
    exact Finset.Nonempty.of_image hA
  have hb (k : G) (hk : k ∈ K) : symmDiff (D.image (fun x => k*x)) D ⊆ B := by
    intro x hx
    have hx' := Finset.mem_symmDiff.mp hx
    rcases hx' with ⟨him,_⟩ | ⟨hD,_⟩
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp him
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k,hk,Finset.mem_image.mpr ⟨y,hDS hy,rfl⟩⟩)
    · exact Finset.mem_union_left _ (hDS hD)
  have hf (k x : G) :
      |(if node (k⁻¹*x) ∈ A then (1 : ℝ) else 0) -
        (if node x ∈ A then 1 else 0)| =
      if x ∈ symmDiff (D.image (fun y => k*y)) D then 1 else 0 := by
    have hi : x ∈ D.image (fun y => k*y) ↔ k⁻¹*x ∈ D := by
      constructor
      · rintro h
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
        simpa using hy
      · intro hx
        exact Finset.mem_image.mpr ⟨k⁻¹*x,hx,by group⟩
    simp only [hnode,Finset.mem_symmDiff,hi]
    by_cases h1 : k⁻¹*x ∈ D <;> by_cases h2 : x ∈ D <;> simp [h1,h2]
  have hbound : graphBoundary u v A =
      ∑ k ∈ K, ((symmDiff (D.image (fun x => k*x)) D).card : ℝ) := by
    unfold graphBoundary graphVariation
    simp only [u,v]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_coe_sort K]
    apply Fintype.sum_congr
    intro k
    have hinner : (∑ x : B, |(if node (k.val⁻¹*x.val) ∈ A then (1 : ℝ) else 0) -
        (if node x.val ∈ A then 1 else 0)|) =
        ∑ x : B, if x.val ∈ symmDiff (D.image (fun y => k.val*y)) D then (1 : ℝ) else 0 := by
      apply Fintype.sum_congr
      intro x
      exact hf k.val x.val
    refine Eq.trans ?_ hinner |>.trans ?_
    · apply Fintype.sum_congr
      intro x
      split_ifs <;> simp_all
    have hcSum := Finset.sum_coe_sort B (fun (x : G) =>
      if x ∈ symmDiff (D.image (fun y => k.val*y)) D then (1 : ℝ) else 0)
    have he : B.filter (fun x => x ∈ symmDiff (D.image (fun x => k.val*x)) D) =
        symmDiff (D.image (fun x => k.val*x)) D := by
      exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hb k.val k.property))
    calc
      _ = ∑ x ∈ B, if x ∈ symmDiff (D.image (fun y => k.val*y)) D then (1 : ℝ) else 0 := by
        simpa using hcSum
      _ = _ := by rw [Finset.sum_boole,he]
  refine ⟨D,hDn,hDS,?_⟩
  rwa [hbound,hc] at hbd

end WeightedGroupCoarea

noncomputable def FiniteSupportReiter (G : Type*) [Group G] : Prop := by
  classical
  exact ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ (S : Finset G) (p : G → ℝ), (∀ x, 0 ≤ p x) ∧
        (∀ x ∉ S, p x = 0) ∧ (∑ x ∈ S, p x) = 1 ∧
        weightedVariation K S p < ε

theorem folner_of_finite_reiter {G : Type*} [Group G]
    (h : FiniteSupportReiter G) : FolnerAmenable G := by
  classical
  intro K ε hε
  obtain ⟨S,p,hp,hs,hm,hv⟩ := h K ε hε
  obtain ⟨D,hD,_,hb⟩ := weighted_group_coarea K S p hp hs ε (by simpa only [hm,mul_one] using hv)
  refine ⟨D,hD,?_⟩
  intro k hk
  have hn (j : G) (_ : j ∈ K) : 0 ≤ ((symmDiff (D.image (fun x => j*x)) D).card : ℝ) :=
    Nat.cast_nonneg _
  have hi := Finset.single_le_sum hn hk
  exact lt_of_le_of_lt hi hb

end SimpleAmenable
end
end

end OAI
