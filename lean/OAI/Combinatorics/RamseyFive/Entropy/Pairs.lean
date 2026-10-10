import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.PairPoints

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

noncomputable def pairs (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (δ a : ℝ) :=
  (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ a ≤ δ*(pairPoints x X p.1 p.2).card

noncomputable def neighbors (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (H : Submodule K V) (δ a : ℝ) :=
  F.filter fun A => H ≠ A ∧ a ≤ δ*(pairPoints x X H A).card

omit [Finite K] in
lemma dominant_witness (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B)
    {δ a : ℝ} (hδ : 0 < δ) (ha : a ≤ δ*(pairPoints x X A B).card)
    (hnd : ¬∀ l : RadialLine x,
      2*((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X A B).card) :
    ∃ l : RadialLine x, l.val ≤ A ⊓ B ∧
      ⌈a/(2*δ)⌉₊ ≤ (RadialLine.trainingOnLine X l).card := by
  classical
  push Not at hnd
  obtain ⟨l,hl⟩ := hnd
  have hp : 0 < ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card := by omega
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hp
  obtain ⟨hyP,hyl⟩ := Finset.mem_filter.mp hy
  have hyAB : y.val.submodule ≤ A ⊓ B := (Finset.mem_filter.mp hyP).2
  have he : RadialLine.through x y.val y.property = l :=
    (RadialLine.through_eq_iff y.property l).mpr hyl
  refine ⟨l,?_,?_⟩
  · rw [←he]
    exact (RadialLine.through_le_iff _ _).mpr ⟨le_inf hxA hxB,hyAB⟩
  · have hs : ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val) ⊆
        RadialLine.trainingOnLine X l := by
      intro z hz
      obtain ⟨hzP,hzl⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzP).1,hzl⟩
    have hc := Finset.card_le_card hs
    have hcr : (pairPoints x X A B).card < 2*((RadialLine.trainingOnLine X l).card:ℝ) := by
      exact_mod_cast (by omega : (pairPoints x X A B).card < 2*(RadialLine.trainingOnLine X l).card)
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (mul_pos (by norm_num) hδ)).mpr
    nlinarith

theorem pair_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    ((pairs x X F δ a).card:ℝ)*a^2 ≤
      (richRadials x X ⊤ ⌈a/(2*δ)⌉₊).card * ((Nat.card K:ℝ)^2+Nat.card K+1)^2*a^2 +
      2*δ^2*X.card^2*((Nat.card K:ℝ)+1)^2 := by
  classical
  let E := pairs x X F δ a
  let nd (p : Submodule K V × Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X p.1 p.2).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X p.1 p.2).card
  let N := E.filter nd
  let D := E.filter (fun p => ¬nd p)
  have hE : E ⊆ F ×ˢ F := Finset.filter_subset _ _
  have hne (p) (hp : p ∈ E) : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.1
  have hM (p) (hp : p ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X p.1 p.2).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hp).2.2))
  have hN := nondominant_pair_count x hdim X F hF hxF N
    ((Finset.filter_subset _ _).trans hE) (fun p hp => hne p (Finset.mem_filter.mp hp).1)
    ⌈a/δ⌉₊ (fun p hp => hM p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hD := dominant_pair_count x (d := 4) hdim X F hF D
    ((Finset.filter_subset _ _).trans hE) ⌈a/(2*δ)⌉₊ (by
      intro p hp
      obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hE hp)
      exact dominant_witness x X p.1 p.2 (hxF _ h1) (hxF _ h2) hδ
        (Finset.mem_filter.mp hp).2.2 hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have hcD : (D.card:ℝ) ≤ (richRadials x X ⊤ ⌈a/(2*δ)⌉₊).card *
      ((Nat.card K:ℝ)^2+Nat.card K+1)^2 := by exact_mod_cast hD
  have hcN : (N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤ 2*(X.card:ℝ)^2*((Nat.card K:ℝ)+1)^2 := by
    exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) := (div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ)) |>.trans_eq (mul_comm _ _)
  have ha2 := pow_le_pow_left₀ ha hceil 2
  have hN' : (N.card:ℝ)*a^2 ≤ 2*δ^2*X.card^2*((Nat.card K:ℝ)+1)^2 := by
    calc
      _ ≤ (N.card:ℝ)*(δ*⌈a/δ⌉₊)^2 := mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ = δ^2*((N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
      _ ≤ δ^2*(2*(X.card:ℝ)^2*((Nat.card K:ℝ)+1)^2) :=
        mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
      _ = _ := by ring
  have he : N.card+D.card=E.card := Finset.card_filter_add_card_filter_not nd
  have her : (N.card:ℝ)+(D.card:ℝ)=E.card := by exact_mod_cast he
  change (E.card:ℝ)*a^2 ≤ _
  rw [←her,add_mul]
  exact (add_le_add hN' (mul_le_mul_of_nonneg_right hcD (sq_nonneg a))).trans_eq (by ring)

end SharpRamseyFive.WeightedOverlap

end OAI
