import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.CommonNeighborDichotomy
import OAI.Combinatorics.RamseyFive.Decoding.Nonpairs

namespace OAI

namespace SharpRamseyFive.RichPlaneOverlap

section
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
open SharpRamseyFive.SkewPairCounting
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem plane_common_neighbors (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (A B : Submodule K V) (hA : A ∈ F) (hB : B ∈ F)
    (hAB : finrank K (A ⊓ B : Submodule K V) = 2) :
    (F.filter fun C => finrank K (A ⊓ C : Submodule K V) = 2 ∧
      finrank K (B ⊓ C : Submodule K V) = 2).card ≤ 2*u := by
  classical
  have hsub : (F.filter fun C => finrank K (A ⊓ C : Submodule K V) = 2 ∧
      finrank K (B ⊓ C : Submodule K V) = 2) ⊆
      (F.filter fun C => A ⊓ B ≤ C) ∪ (F.filter fun C => C ≤ A ⊔ B) := by
    intro C hC
    obtain ⟨hCF, hCA, hCB⟩ := Finset.mem_filter.mp hC
    have hd := common_neighbor_dichotomy A B C (hF C hCF) hAB
      (by rw [inf_comm]; exact hCA) (by rw [inf_comm]; exact hCB)
    simpa only [Finset.mem_union, Finset.mem_filter, hCF, true_and] using hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := hline (A ⊓ B) hAB
  have h2 := hhyper (A ⊔ B) (finrank_sup_of_plane_intersection A B (hF A hA) (hF B hB) hAB)
  omega

theorem inf_eq_point_of_not_line (x : ℙ K V) (A B : Submodule K V)
    (hA : finrank K A = 3) (hB : finrank K B = 3) (hAB : A ≠ B)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B)
    (hnot : finrank K (A ⊓ B : Submodule K V) ≠ 2) : A ⊓ B = x.submodule := by
  have hle : x.submodule ≤ A ⊓ B := le_inf hxA hxB
  have hge := Submodule.finrank_mono hle
  rw [x.finrank_submodule] at hge
  have hlt : A ⊓ B < A := lt_of_le_of_ne inf_le_left (by
    intro he
    have hab : A ≤ B := he ▸ inf_le_right
    exact hAB (Submodule.eq_of_le_of_finrank_eq hab (hA.trans hB.symm)))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hA] at hd
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [x.finrank_submodule]; omega)).symm

theorem local_skew_pairs (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (x : ℙ K V)
    (hsize : 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card) :
    ((F.filter fun A => x.submodule ≤ A).card : ℝ)^2 ≤
      16 * ((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card := by
  classical
  let S := F.filter fun A => x.submodule ≤ A
  let R (A B : Submodule K V) := A ≠ B ∧ finrank K (A ⊓ B : Submodule K V) = 2
  have hc (A : Submodule K V) (hA : A ∈ S) (B : Submodule K V) (hB : B ∈ S)
      (hAB : R A B) : (S.filter fun C => R A C ∧ R B C).card ≤ 2*u := by
    apply (Finset.card_le_card ?_).trans
      (plane_common_neighbors F hF u hline hhyper A B
        (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hAB.2)
    intro C hC
    obtain ⟨hCS, hAC, hBC⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hCS).1,hAC.2,hBC.2⟩
  have hm := many_nonpairs R (fun A h => h.1 rfl) S (2*u) hc hsize
  have hsub : nonpairs R S ⊆
      (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule := by
    rintro ⟨A,B⟩ hp
    obtain ⟨hmem, hne,hnot⟩ := Finset.mem_filter.mp hp
    obtain ⟨hAS,hBS⟩ := Finset.mem_product.mp hmem
    obtain ⟨hAF, hxA⟩ := Finset.mem_filter.mp hAS
    obtain ⟨hBF, hxB⟩ := Finset.mem_filter.mp hBS
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hAF,hBF⟩,hne,?_⟩
    exact inf_eq_point_of_not_line x A B (hF A hAF) (hF B hBF) hne hxA hxB
      (fun h => hnot ⟨hne,h⟩)
  have hmc : ((nonpairs R S).card:ℝ) ≤
      ((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hm.trans (mul_le_mul_of_nonneg_left hmc (by norm_num))

end

open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in

theorem sum_point_pairs_le (F : Finset (Submodule K V)) (X : Finset (ℙ K V)) :
    ∑ x ∈ X, ((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card
      ≤ F.card^2 := by
  let P (x : ℙ K V) := (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule
  have hd : (X : Set (ℙ K V)).PairwiseDisjoint P := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro p hpx hpy
    have h1 := (Finset.mem_filter.mp hpx).2.2
    have h2 := (Finset.mem_filter.mp hpy).2.2
    exact hxy (Projectivization.submodule_injective (h1.symm.trans h2))
  have hsub : X.biUnion P ⊆ F ×ˢ F := by
    intro p hp
    obtain ⟨x,_,hpx⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpx).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hd, Finset.card_product] at hc
  simpa only [P, pow_two] using hc

theorem high_degree_second_moment (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (X : Finset (ℙ K V)) :
    ∑ x ∈ X.filter (fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card),
      ((F.filter fun A => x.submodule ≤ A).card:ℝ)^2 ≤ 16*(F.card:ℝ)^2 := by
  let Y := X.filter fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card
  have hs := Finset.sum_le_sum (s := Y) (fun x hx =>
    local_skew_pairs F hF u hline hhyper x (Finset.mem_filter.mp hx).2)
  have hp : (∑ x ∈ Y,
      (((F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ p.1 ⊓ p.2 = x.submodule).card:ℝ)) ≤ (F.card:ℝ)^2 := by
    exact_mod_cast sum_point_pairs_le F Y
  exact hs.trans (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hp (by norm_num))

omit [FiniteDimensional K V] in

theorem plane_point_double_count (F : Finset (Submodule K V)) (X : Finset (ℙ K V)) :
    ∑ x ∈ X, (F.filter fun A => x.submodule ≤ A).card =
      ∑ A ∈ F, (X.filter fun x => x.submodule ≤ A).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem rich_plane_count (F : Finset (Submodule K V))
    (hF : ∀ A ∈ F, finrank K A = 3) (u : ℕ)
    (hline : ∀ L : Submodule K V, finrank K L = 2 → (F.filter fun C => L ≤ C).card ≤ u)
    (hhyper : ∀ H : Submodule K V, finrank K H = 4 → (F.filter fun C => C ≤ H).card ≤ u)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hlarge : 64*X.card ≤ M^2) :
    (F.card:ℝ)*M ≤ 16*X.card*(2*(u:ℝ)+1) := by
  let d (x : ℙ K V) : ℝ := (F.filter fun A => x.submodule ≤ A).card
  let Y := X.filter fun x => 8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card
  let Z := X.filter fun x => ¬8*(2*u+1) ≤ (F.filter fun A => x.submodule ≤ A).card
  have hsum : (∑ x ∈ Y, d x) + ∑ x ∈ Z, d x = ∑ x ∈ X, d x :=
    Finset.sum_filter_add_sum_filter_not X _ _
  have hlow : (∑ x ∈ Z, d x) ≤ (X.card:ℝ)*(8*(2*(u:ℝ)+1)) := by
    have hl (x : ℙ K V) (hx : x ∈ Z) : d x ≤ 8*(2*(u:ℝ)+1) := by
      have hh := (Finset.mem_filter.mp hx).2
      have hnat : (F.filter fun A => x.submodule ≤ A).card ≤ 8*(2*u+1) := (lt_of_not_ge hh).le
      dsimp [d]
      exact_mod_cast hnat
    have hle := Finset.sum_le_sum hl
    have hsub : Z.card ≤ X.card := Finset.card_le_card (Finset.filter_subset _ _)
    calc
      _ ≤ (Z.card:ℝ)*(8*(2*(u:ℝ)+1)) := by simpa using hle
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
  have htotal : (F.card:ℝ)*M ≤ ∑ x ∈ X, d x := by
    have hs := Finset.sum_le_sum hM
    simp only [Finset.sum_const_nat, ← plane_point_double_count] at hs
    dsimp [d]
    exact_mod_cast hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ => (1:ℝ)) d
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsecond := high_degree_second_moment F hF u hline hhyper X
  have hY : (Y.card:ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hsq : (∑ x ∈ Y, d x)^2 ≤ 16*(X.card:ℝ)*(F.card:ℝ)^2 := by
    calc
      _ ≤ (Y.card:ℝ)*∑ x ∈ Y, d x^2 := hcs
      _ ≤ (Y.card:ℝ)*(16*(F.card:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hY (sq_nonneg (F.card:ℝ))]
  have hr : (0:ℝ) ≤ (F.card:ℝ)*M := by positivity
  have hs0 : 0 ≤ ∑ x ∈ Y, d x := Finset.sum_nonneg (fun x _ => Nat.cast_nonneg _)
  have hlg : 64*(X.card:ℝ) ≤ (M:ℝ)^2 := by exact_mod_cast hlarge
  have hprod := mul_le_mul_of_nonneg_right hlg (sq_nonneg (F.card:ℝ))
  have hhigh : 2*(∑ x ∈ Y, d x) ≤ (F.card:ℝ)*M := by
    nlinarith [sq_nonneg ((F.card:ℝ)*M+2*(∑ x ∈ Y, d x))]
  linarith

end SharpRamseyFive.RichPlaneOverlap

end OAI
