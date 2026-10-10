import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Pairs

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

theorem degree_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    ((neighbors x X F H δ a).card:ℝ)*a^2 ≤
      2*δ*(onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1)*a +
      2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
  classical
  let E := neighbors x X F H δ a
  let nd (A : Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X H A).card
  let N := E.filter nd
  let D := E.filter (fun A => ¬nd A)
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hne (A) (hA : A ∈ E) : H ≠ A := (Finset.mem_filter.mp hA).2.1
  have hM (A) (hA : A ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X H A).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hA).2.2))
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH N
    ((Finset.filter_subset _ _).trans hE) (fun A hA => hne A (Finset.mem_filter.mp hA).1)
    ⌈a/δ⌉₊ (fun A hA => hM A (Finset.mem_filter.mp hA).1)
    (fun A hA => (Finset.mem_filter.mp hA).2)
  have hD := dominant_degree_count x (d := 4) hdim X F hF H hxH D
    ((Finset.filter_subset _ _).trans hE) ⌈a/(2*δ)⌉₊ (by
      intro A hA
      obtain ⟨hA,hn⟩ := Finset.mem_filter.mp hA
      exact dominant_witness x X H A hxH (hxF A (hE hA)) hδ
        (Finset.mem_filter.mp hA).2.2 hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have hcD : (D.card:ℝ)*⌈a/(2*δ)⌉₊ ≤ (onPlane x X H).card *
      ((Nat.card K:ℝ)^2+Nat.card K+1) := by exact_mod_cast hD
  have hcN : (N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤
      2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1) := by exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  have hceil₂ : a ≤ 2*δ*(⌈a/(2*δ)⌉₊:ℝ) :=
    ((div_le_iff₀ (mul_pos (by norm_num) hδ)).mp (Nat.le_ceil (a/(2*δ)))).trans_eq (mul_comm _ _)
  have hD' : (D.card:ℝ)*a ≤
      2*δ*(onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1) := by
    calc
      _ ≤ (D.card:ℝ)*(2*δ*⌈a/(2*δ)⌉₊) := mul_le_mul_of_nonneg_left hceil₂ (by positivity)
      _ = 2*δ*((D.card:ℝ)*⌈a/(2*δ)⌉₊) := by ring
      _ ≤ 2*δ*((onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1)) :=
        mul_le_mul_of_nonneg_left hcD (by positivity)
      _ = _ := by ring
  have hN' : (N.card:ℝ)*a^2 ≤ 2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
    calc
      _ ≤ (N.card:ℝ)*(δ*⌈a/δ⌉₊)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hceil 2) (by positivity)
      _ = δ^2*((N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
      _ ≤ δ^2*(2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
      _ = _ := by ring
  have he : N.card+D.card=E.card := Finset.card_filter_add_card_filter_not nd
  have her : (N.card:ℝ)+(D.card:ℝ)=E.card := by exact_mod_cast he
  change (E.card:ℝ)*a^2 ≤ _
  rw [←her,add_mul]
  have hDa := mul_le_mul_of_nonneg_right hD' ha
  nlinarith

theorem nondominant_weighted_degree (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a)
    (hline : ∀ l : RadialLine x, δ*(RadialLine.trainingOnLine X l).card < a/2) :
    ((neighbors x X F H δ a).card:ℝ)*a^2 ≤
      2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
  classical
  let E := neighbors x X F H δ a
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hM (A) (hA : A ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X H A).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hA).2.2))
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH E hE
    (fun A hA => (Finset.mem_filter.mp hA).2.1) ⌈a/δ⌉₊ hM (by
      intro A hA
      by_contra hn
      obtain ⟨l,_,hl⟩ := dominant_witness x X H A hxH (hxF A (hE hA)) hδ
        (Finset.mem_filter.mp hA).2.2 hn
      have hlg : a/(2*δ) ≤ ((RadialLine.trainingOnLine X l).card:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hl)
      have hh := (div_le_iff₀ (mul_pos (by norm_num) hδ)).mp hlg
      have hh' := hline l
      nlinarith)
  have hcN : (E.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤
      2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1) := by exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  calc
    _ ≤ (E.card:ℝ)*(δ*⌈a/δ⌉₊)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hceil 2) (by positivity)
    _ = δ^2*((E.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
    _ ≤ δ^2*(2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
    _ = _ := by ring

end SharpRamseyFive.WeightedOverlap

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

end OAI
