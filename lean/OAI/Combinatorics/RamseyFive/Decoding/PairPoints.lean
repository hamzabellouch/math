import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.CardFilterContainment
import OAI.Combinatorics.RamseyFive.Decoding.OffFiberPairs

namespace OAI

namespace SharpRamseyFive.ActualOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

noncomputable def pairPoints (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) := onPlane x X (A ⊓ B)

theorem nondominant_pair_count (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (E : Finset (Submodule K V × Submodule K V)) (hE : E ⊆ F ×ˢ F)
    (hne : ∀ p ∈ E, p.1 ≠ p.2) (M : ℕ)
    (hM : ∀ p ∈ E, M ≤ (pairPoints x X p.1 p.2).card)
    (hnd : ∀ p ∈ E, ∀ l : RadialLine x,
      2*((pairPoints x X p.1 p.2).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X p.1 p.2).card) :
    E.card*M^2 ≤ 2*X.card^2*(Nat.card K+1)^2 := by
  let L := E.image fun p => p.1 ⊓ p.2
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 3 := by
    obtain ⟨⟨A,B⟩,hAB,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨hA,hB⟩ := Finset.mem_product.mp (hE hAB)
    exact hyperplane_intersection_rank (d := 4) hdim A B (hF A hA) (hF B hB) (hne _ hAB)
  have hxL (W : Submodule K V) (hW : W ∈ L) : x.submodule ≤ W := by
    obtain ⟨⟨A,B⟩,hAB,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨hA,hB⟩ := Finset.mem_product.mp (hE hAB)
    exact le_inf (hxF A hA) (hxF B hB)
  have hplanes := rich_nondominant_plane_count x X L hL hxL M (by
    intro W hW
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hW
    exact hM p hp) (by
    intro W hW l
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hW
    exact hnd p hp l)
  have hpairs := pair_count_by_intersection (d := 4) hdim F hF L 3 hL E hE (by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hQ : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  rw [hQ] at hpairs
  calc
    E.card*M^2 ≤ (L.card*(Nat.card K+1)^2)*M^2 := Nat.mul_le_mul_right _ hpairs
    _ = (L.card*M^2)*(Nat.card K+1)^2 := by ring
    _ ≤ (2*X.card^2)*(Nat.card K+1)^2 := Nat.mul_le_mul_right _ hplanes

theorem nondominant_degree_count (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F)
    (hne : ∀ A ∈ E, H ≠ A) (M : ℕ)
    (hM : ∀ A ∈ E, M ≤ (pairPoints x X H A).card)
    (hnd : ∀ A ∈ E, ∀ l : RadialLine x,
      2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X H A).card) :
    E.card*M^2 ≤ 2*(onPlane x X H).card^2*(Nat.card K+1) := by
  let L := E.image fun A => H ⊓ A
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 3 := by
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    exact hyperplane_intersection_rank (d := 4) hdim H A hH (hF A (hE hA)) (hne A hA)
  have hxL (W : Submodule K V) (hW : W ∈ L) : x.submodule ≤ W := by
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    exact le_inf hxH (hxF A (hE hA))
  have hpoints (A : Submodule K V) :
      onPlane x (onPlane x X H) (H ⊓ A) = pairPoints x X H A := by
    ext y
    simp only [onPlane,pairPoints,Finset.mem_filter,le_inf_iff]
    tauto
  have hplanes := rich_nondominant_plane_count x (onPlane x X H) L hL hxL M (by
    intro W hW
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    rw [hpoints]
    exact hM A hA) (by
    intro W hW l
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    rw [hpoints]
    exact hnd A hA l)
  have hpairs := neighbor_count_by_intersection (d := 4) hdim F hF L 3 hL H E hE (by
    intro A hA
    exact Finset.mem_image.mpr ⟨A,hA,rfl⟩)
  have hQ : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  rw [hQ] at hpairs
  calc
    E.card*M^2 ≤ (L.card*(Nat.card K+1))*M^2 := Nat.mul_le_mul_right _ hpairs
    _ = (L.card*M^2)*(Nat.card K+1) := by ring
    _ ≤ (2*(onPlane x X H).card^2)*(Nat.card K+1) := Nat.mul_le_mul_right _ hplanes

noncomputable def richRadials [Fintype (RadialLine x)]
    (X : Finset {y : ℙ K V // x ≠ y}) (W : Submodule K V) (M : ℕ) :=
  (RadialLine.inFlat W).filter fun l => M ≤ (RadialLine.trainingOnLine X l).card

theorem dominant_degree_count [Fintype (RadialLine x)] {d : ℕ}
    (hdim : finrank K V = d+1) (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (H : Submodule K V) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F) (M : ℕ)
    (hdom : ∀ A ∈ E, ∃ l : RadialLine x, l.val ≤ H ⊓ A ∧
      M ≤ (RadialLine.trainingOnLine X l).card) :
    E.card*M ≤ (onPlane x X H).card * (∑ i ∈ Finset.range (d-1), Nat.card K^i) := by
  let R := richRadials x X H M
  let L := R.image Subtype.val
  have hcR : R.card*M ≤ (onPlane x X H).card :=
    rich_radial_count X H hxH R (Finset.filter_subset _ _) M (by
      intro l hl
      exact (Finset.mem_filter.mp hl).2)
  have hcL : L.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 2 := by
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hW
    exact l.property.1
  have hN := neighbor_count_by_contained_witness hdim F hF L 2 hL E hE (by
    intro A hA
    obtain ⟨l,hl,hM⟩ := hdom A hA
    refine ⟨l.val,Finset.mem_image.mpr ⟨l,?_,rfl⟩,hl.trans inf_le_right⟩
    refine Finset.mem_filter.mpr ⟨?_,hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := RadialLine x) l, hl.trans inf_le_left⟩)
  rw [hcL] at hN
  have he : d+1-2 = d-1 := by omega
  rw [he] at hN
  calc
    E.card*M ≤ (R.card*(∑ i ∈ Finset.range (d-1), Nat.card K^i))*M := Nat.mul_le_mul_right _ hN
    _ = (R.card*M)*(∑ i ∈ Finset.range (d-1), Nat.card K^i) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hcR

theorem dominant_pair_count [Fintype (RadialLine x)] {d : ℕ}
    (hdim : finrank K V = d+1) (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (E : Finset (Submodule K V × Submodule K V)) (hE : E ⊆ F ×ˢ F) (M : ℕ)
    (hdom : ∀ p ∈ E, ∃ l : RadialLine x, l.val ≤ p.1 ⊓ p.2 ∧
      M ≤ (RadialLine.trainingOnLine X l).card) :
    E.card ≤ (richRadials x X ⊤ M).card * (∑ i ∈ Finset.range (d-1), Nat.card K^i)^2 := by
  let R := richRadials x X ⊤ M
  let L := R.image Subtype.val
  have hcL : L.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 2 := by
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hW
    exact l.property.1
  have hN := pair_count_by_contained_witness hdim F hF L 2 hL E hE (by
    intro p hp
    obtain ⟨l,hl,hM⟩ := hdom p hp
    refine ⟨l.val,Finset.mem_image.mpr ⟨l,?_,rfl⟩,hl⟩
    refine Finset.mem_filter.mpr ⟨?_,hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := RadialLine x) l, le_top⟩)
  rw [hcL] at hN
  have he : d+1-2 = d-1 := by omega
  simpa only [he] using hN

omit [Finite K] in

theorem intersection_radial_three (hdim : finrank K V = 4)
    (A B : Submodule K V) (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B) (hne : A ≠ B)
    (X : Finset {y : ℙ K V // x ≠ y}) :
    ∃ l : RadialLine x, l.val = A ⊓ B ∧
      RadialLine.trainingOnLine X l = pairPoints x X A B := by
  let l : RadialLine x := ⟨A ⊓ B,
    hyperplane_intersection_rank (d := 3) hdim A B hA hB hne, le_inf hxA hxB⟩
  exact ⟨l,rfl,rfl⟩

omit [Finite K] in

theorem overlap_dichotomy (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B)
    (M : ℕ) (hM : 2*M ≤ (pairPoints x X A B).card) :
    (∀ l : RadialLine x,
      2*((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X A B).card) ∨
    (∃ l : RadialLine x, l.val ≤ A ⊓ B ∧
      M ≤ (RadialLine.trainingOnLine X l).card) := by
  classical
  by_cases h : ∀ l : RadialLine x,
      2*((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X A B).card
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨l,hl⟩ := h
    have hp : 0 < ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card := by omega
    obtain ⟨y,hy⟩ := Finset.card_pos.mp hp
    obtain ⟨hyP,hyl⟩ := Finset.mem_filter.mp hy
    have hyAB : y.val.submodule ≤ A ⊓ B := (Finset.mem_filter.mp hyP).2
    have he : RadialLine.through x y.val y.property = l :=
      (RadialLine.through_eq_iff y.property l).mpr hyl
    refine ⟨l,?_,?_⟩
    · rw [← he]
      exact (RadialLine.through_le_iff _ _).mpr ⟨le_inf hxA hxB,hyAB⟩
    · have hs : ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val) ⊆
          RadialLine.trainingOnLine X l := by
        intro z hz
        obtain ⟨hzP,hzl⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzP).1,hzl⟩
      have hc := Finset.card_le_card hs
      omega

theorem pair_count_three [Fintype (RadialLine x)] (hdim : finrank K V = 4)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (E : Finset (Submodule K V × Submodule K V)) (hE : E ⊆ F ×ˢ F)
    (hne : ∀ p ∈ E, p.1 ≠ p.2) (M : ℕ)
    (hM : ∀ p ∈ E, M ≤ (pairPoints x X p.1 p.2).card) :
    E.card ≤ (richRadials x X ⊤ M).card * (Nat.card K+1)^2 := by
  have h := dominant_pair_count x (d := 3) hdim X F hF E hE M (by
    intro p hp
    obtain ⟨hA,hB⟩ := Finset.mem_product.mp (hE hp)
    obtain ⟨l,hl,he⟩ := intersection_radial_three x hdim p.1 p.2
      (hF _ hA) (hF _ hB) (hxF _ hA) (hxF _ hB) (hne p hp) X
    exact ⟨l,hl.le,he ▸ hM p hp⟩)
  simpa [Finset.sum_range_succ, Nat.add_comm] using h

theorem degree_count_three [Fintype (RadialLine x)] (hdim : finrank K V = 4)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 3) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F)
    (hne : ∀ A ∈ E, H ≠ A) (M : ℕ)
    (hM : ∀ A ∈ E, M ≤ (pairPoints x X H A).card) :
    E.card*M ≤ (onPlane x X H).card * (Nat.card K+1) := by
  have h := dominant_degree_count x (d := 3) hdim X F hF H hxH E hE M (by
    intro A hA
    obtain ⟨l,hl,he⟩ := intersection_radial_three x hdim H A hH (hF _ (hE hA))
      hxH (hxF _ (hE hA)) (hne A hA) X
    exact ⟨l,hl.le,he ▸ hM A hA⟩)
  simpa [Finset.sum_range_succ, Nat.add_comm] using h

noncomputable def overlapPairs (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (M : ℕ) :=
  (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ M ≤ (pairPoints x X p.1 p.2).card

noncomputable def overlapNeighbors (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (H : Submodule K V) (M : ℕ) :=
  F.filter fun A => H ≠ A ∧ M ≤ (pairPoints x X H A).card

theorem actual_pair_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) (M : ℕ) :
    (overlapPairs x X F (2*M)).card * M^2 ≤
      (richRadials x X ⊤ M).card * (Nat.card K^2+Nat.card K+1)^2 * M^2 +
      2*X.card^2*(Nat.card K+1)^2 := by
  classical
  let E := overlapPairs x X F (2*M)
  let nd (p : Submodule K V × Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X p.1 p.2).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X p.1 p.2).card
  let N := E.filter nd
  let D := E.filter (fun p => ¬nd p)
  have hE : E ⊆ F ×ˢ F := Finset.filter_subset _ _
  have hne (p) (hp : p ∈ E) : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.1
  have hM (p) (hp : p ∈ E) : 2*M ≤ (pairPoints x X p.1 p.2).card :=
    (Finset.mem_filter.mp hp).2.2
  have hN := nondominant_pair_count x hdim X F hF hxF N
    ((Finset.filter_subset _ _).trans hE) (fun p hp => hne p (Finset.mem_filter.mp hp).1)
    M (fun p hp => (by omega : M ≤ 2*M).trans (hM p (Finset.mem_filter.mp hp).1))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hD := dominant_pair_count x (d := 4) hdim X F hF D
    ((Finset.filter_subset _ _).trans hE) M (by
      intro p hp
      obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hE hp)
      exact (overlap_dichotomy x X p.1 p.2 (hxF _ ha) (hxF _ hb) M (hM p hp)).resolve_left hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have he : N.card + D.card = E.card := Finset.card_filter_add_card_filter_not nd
  calc
    E.card*M^2 = D.card*M^2+N.card*M^2 := by rw [← he]; ring
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ hD) hN

theorem actual_degree_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H) (M : ℕ) :
    (overlapNeighbors x X F H (2*M)).card * M^2 ≤
      (onPlane x X H).card * (Nat.card K^2+Nat.card K+1) * M +
      2*(onPlane x X H).card^2*(Nat.card K+1) := by
  classical
  let E := overlapNeighbors x X F H (2*M)
  let nd (A : Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X H A).card
  let N := E.filter nd
  let D := E.filter (fun A => ¬nd A)
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hne (A) (hA : A ∈ E) : H ≠ A := (Finset.mem_filter.mp hA).2.1
  have hM (A) (hA : A ∈ E) : 2*M ≤ (pairPoints x X H A).card :=
    (Finset.mem_filter.mp hA).2.2
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH N
    ((Finset.filter_subset _ _).trans hE) (fun A hA => hne A (Finset.mem_filter.mp hA).1)
    M (fun A hA => (by omega : M ≤ 2*M).trans (hM A (Finset.mem_filter.mp hA).1))
    (fun A hA => (Finset.mem_filter.mp hA).2)
  have hD := dominant_degree_count x (d := 4) hdim X F hF H hxH D
    ((Finset.filter_subset _ _).trans hE) M (by
      intro A hA
      obtain ⟨hA,hn⟩ := Finset.mem_filter.mp hA
      exact (overlap_dichotomy x X H A hxH (hxF _ (hE hA)) M (hM A hA)).resolve_left hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have he : N.card + D.card = E.card := Finset.card_filter_add_card_filter_not nd
  calc
    E.card*M^2 = (D.card*M)*M+N.card*M^2 := by rw [← he]; ring
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ hD) hN

end SharpRamseyFive.ActualOverlap

end OAI
