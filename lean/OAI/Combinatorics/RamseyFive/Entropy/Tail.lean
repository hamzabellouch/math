import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.LargeCells

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

noncomputable def tail (J cap : ℕ) : Finset (ℙ K V) :=
  remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
    remaining F hF (fun i => flatPoints (P i)) X J

noncomputable def tailPlanes (L : Finset (Submodule K V)) (J cap M : ℕ) :=
  L.filter fun A => M ≤ ((tail F hF P X J cap).filter fun x => x.submodule ≤ A).card

noncomputable def headAt (L : Finset (Submodule K V)) (J cap M : ℕ) (c : ℝ) (x : ℙ K V) :=
  L.filter fun A => x ∈ headPlaneCenters F hF P X J
    (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A

noncomputable def richAt (L : Finset (Submodule K V)) (J M : ℕ) (x : ℙ K V) :=
  L.filter fun A => x.submodule ≤ A ∧ 2*M ≤
    (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
      ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card

lemma rich_planes_split (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M : ℕ) (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (x : ℙ K V)
    (hx : x ∉ largeCellIntersections F hF P X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) c) :
    richAt F hF P X L J M x ⊆ headAt F hF P X L J cap M c x ∪
      (tailPlanes F hF P X L J cap M).filter (fun A => x.submodule ≤ A) := by
  intro A hA
  obtain ⟨hAL,hxA,hAr⟩ := Finset.mem_filter.mp hA
  by_cases hc : ∃ j < headIndex F hF (fun i => flatPoints (P i)) X J cap,
      A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hAL,Finset.mem_filter.mpr ⟨(mem_flatPoints A x).mpr hxA,hc,?_,hx⟩⟩
    apply hAr.trans
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro y hy
    obtain ⟨hy,hyn⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,hyn⟩
  · have hhead := head_plane_points F hF P X J cap A (hL A hAL) (by
      intro j hj hAj
      exact hc ⟨j,hj,hAj⟩)
    have hsub : (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A) ⊆
        ((X \ remaining F hF (fun i => flatPoints (P i)) X
          (headIndex F hF (fun i => flatPoints (P i)) X J cap)).filter fun y => y.submodule ≤ A) ∪
        ((tail F hF P X J cap).filter fun y => y.submodule ≤ A) := by
      intro y hy
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,tail] at *
      tauto
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hAL,by omega⟩,hxA⟩

lemma head_degree_sum (L : Finset (Submodule K V)) (J cap M : ℕ) (c : ℝ)
    (Y : Finset (ℙ K V)) :
    ∑ x ∈ Y, (headAt F hF P X L J cap M c x).card ≤
      ∑ A ∈ L, (headPlaneCenters F hF P X J
        (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A).card := by
  simp only [headAt,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  have hs : Y.filter (fun x => x ∈ headPlaneCenters F hF P X J
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A) ⊆
      headPlaneCenters F hF P X J
        (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  simpa only [Finset.card_filter] using Finset.card_le_card hs

theorem head_exceptions (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M : ℕ) (hM : 0 < M)
    (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*c ≤ M) (D : ℕ) (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D ≤ (headAt F hF P X L J cap M c x).card).card:ℝ)*D*M^2 ≤
      4*(Nat.card K:ℝ)^2*(Nat.card K+1)*
        headIndex F hF (fun i => flatPoints (P i)) X J cap*X.card := by
  let E := Y.filter fun x => D ≤ (headAt F hF P X L J cap M c x).card
  have hs : E.card*D ≤ ∑ x ∈ E,(headAt F hF P X L J cap M c x).card := by
    calc
      _ = ∑ _x ∈ E,D := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
  have hs' : (E.card:ℝ)*D ≤ ∑ A ∈ L,
      ((headPlaneCenters F hF P X J
        (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A).card:ℝ) := by
    exact_mod_cast hs.trans (head_degree_sum F hF P X L J cap M c E)
  exact (mul_le_mul_of_nonneg_right hs' (sq_nonneg _)).trans
    (head_center_plane_count F hF P X hP L hL J
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) M
      (headIndex_le F hF _ X J cap) hM hHM c hmean)

theorem rich_count_outside_exceptions
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M : ℕ) (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (D₁ D₂ : ℕ) (Y : Finset (ℙ K V)) (x : ℙ K V) (hxY : x ∈ Y)
    (hxL : x ∉ largeCellIntersections F hF P X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) c)
    (hxH : x ∉ Y.filter fun x => D₁ ≤ (headAt F hF P X L J cap M c x).card)
    (hxT : x ∉ Y.filter fun x => D₂ ≤
      ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card) :
    (richAt F hF P X L J M x).card < D₁+D₂ := by
  have hcard := (Finset.card_le_card (rich_planes_split F hF P X L hL J cap M hHM c x hxL)).trans
    (Finset.card_union_le _ _)
  have hh : (headAt F hF P X L J cap M c x).card < D₁ := by
    by_contra hn
    exact hxH (Finset.mem_filter.mpr ⟨hxY,by omega⟩)
  have ht : ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card < D₂ := by
    by_contra hn
    exact hxT (Finset.mem_filter.mpr ⟨hxY,by omega⟩)
  omega

end

open Module GreedyTraining ProjectiveTraining RichPlaneGeometry HyperplaneOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

theorem tail_exceptions
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J cap M u D : ℕ) (hMpos : 0 < M)
    (hlineLarge : 2*(Nat.card K+1) ≤ M) (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*cap ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*cap ≤ (u:ℝ)*M^2)
    (hlarge : 64*X.card ≤ M^2) (hD : 8*(2*u+1) ≤ D) (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D ≤
      ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card).card:ℝ)*D^2*M^2 ≤
      4096*(X.card:ℝ)^2*(2*(u:ℝ)+1)^2 := by
  apply actual_tail_rich_plane_exceptions F hF P X hcover J cap M u D hMpos
    (tailPlanes F hF P X L J cap M) (fun A hA => hL A (Finset.mem_filter.mp hA).1)
  · intro A hA
    exact (Finset.mem_filter.mp hA).2
  · exact hlineLarge
  · exact hlineNum
  · exact hmean
  · exact hhyperNum
  · exact hlarge
  · exact hD

noncomputable def capturedPairs (G : Finset (Submodule K V)) (J M : ℕ) (x : ℙ K V) :=
  (G ×ˢ G).filter fun p => p.1 ≠ p.2 ∧ 2*M ≤
    (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
      ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ p.1 ⊓ p.2).card

theorem captured_pair_count (hdim : finrank K V = 5)
    (G : Finset (Submodule K V)) (hG : ∀ A ∈ G, finrank K A = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hcomplete : ∀ A : Submodule K V, finrank K A = 3 → A ∈ L)
    (J M : ℕ) (x : ℙ K V) (hxG : ∀ A ∈ G,x.submodule ≤ A) :
    (capturedPairs F hF P X G J M x).card ≤
      (richAt F hF P X L J M x).card*(Nat.card K+1)^2 := by
  have hh := pair_count_by_intersection (d := 4) hdim G hG
    (richAt F hF P X L J M x) 3 (fun A hA => hL A (Finset.mem_filter.mp hA).1)
    (capturedPairs F hF P X G J M x) (Finset.filter_subset _ _) (by
      intro p hp
      obtain ⟨hp,hne,hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hcomplete _ (hyperplane_intersection_rank (d := 4) hdim p.1 p.2
        (hG _ h1) (hG _ h2) hne),le_inf (hxG _ h1) (hxG _ h2),hpc⟩)
  have he : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ,Nat.add_comm]
  simpa only [he] using hh

theorem captured_pairs_outside_exceptions (hdim : finrank K V = 5)
    (G : Finset (Submodule K V)) (hG : ∀ A ∈ G, finrank K A = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hcomplete : ∀ A : Submodule K V, finrank K A = 3 → A ∈ L)
    (J cap M : ℕ) (hHM : headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) ≤ M)
    (c : ℝ) (D₁ D₂ : ℕ) (Y : Finset (ℙ K V)) (x : ℙ K V) (hxY : x ∈ Y)
    (hxG : ∀ A ∈ G,x.submodule ≤ A)
    (hxL : x ∉ largeCellIntersections F hF P X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap) c)
    (hxH : x ∉ Y.filter fun x => D₁ ≤ (headAt F hF P X L J cap M c x).card)
    (hxT : x ∉ Y.filter fun x => D₂ ≤
      ((tailPlanes F hF P X L J cap M).filter fun A => x.submodule ≤ A).card) :
    (capturedPairs F hF P X G J M x).card ≤ (D₁+D₂)*(Nat.card K+1)^2 := by
  exact (captured_pair_count F hF P X hdim G hG L hL hcomplete J M x hxG).trans
    (Nat.mul_le_mul_right _ (rich_count_outside_exceptions F hF P X L hL J cap M hHM c D₁ D₂
      Y x hxY hxL hxH hxT).le)

end SharpRamseyFive.HighPlaneBudget

end OAI
