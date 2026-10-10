import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.LinearForm

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.SpanRank
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma mem_pair_iff_rank [FiniteDimensional K V] (x y z : V)
    (hxy : finrank K (Submodule.span K {x,y}) = 2) :
    z ∈ Submodule.span K {x,y} ↔ finrank K (Submodule.span K {x,y,z}) ≤ 2 := by
  have hle : Submodule.span K {x,y} ≤ Submodule.span K {x,y,z} := by
    apply Submodule.span_mono
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    tauto
  constructor
  · intro hz
    have he : Submodule.span K {x,y,z} ≤ Submodule.span K {x,y} := by
      apply Submodule.span_le.mpr
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · exact hz
    simpa only [hxy] using Submodule.finrank_mono he
  · intro hr
    have he := Submodule.eq_of_le_of_finrank_le hle (by simpa only [hxy] using hr)
    rw [he]
    exact Submodule.subset_span (by simp)
end SharpRamseyFive.SpanRank

namespace SharpRamseyFive.AffineRealization

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι : Type*} [Field K] [Field L] [Fintype I] [DecidableEq ι]

omit [DecidableEq ι] in
lemma span_pair_eq_line (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : Submodule K (I → K)) (hW : finrank K W = 2)
    {i j : ι} (hij : i ≠ j) (hi : (p i).rep ∈ W) (hj : (p j).rep ∈ W) :
    Submodule.span K {(p i).rep, (p j).rep} = W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | hv
    · exact hi
    · exact (Set.mem_singleton_iff.mp hv) ▸ hj
  · rw [projective_pair_rank (fun he => hij (hp he)), hW]

theorem line_incidence_of_ranks
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (W : Submodule K (I → K)) (hW : finrank K W = 2)
    {i j : ι} (hij : i ≠ j) (hi : (p i).rep ∈ W) (hj : (p j).rep ∈ W) (k : ι) :
    (p k).rep ∈ W ↔ a k ∈ Set.range (fun t : L => a i + t • (a j-a i)) := by
  classical
  have hpij : p i ≠ p j := fun he => hij (hp he)
  have hpair : finrank L (Submodule.span L {((1 : L), a i), ((1 : L), a j)}) = 2 := by
    have h := hr {i,j}
    rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair, Set.image_pair,
      projective_pair_rank hpij] at h
    exact h
  have htriple := hr {i,j,k}
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton,
    Set.image_insert_eq, Set.image_pair, Set.image_insert_eq, Set.image_pair] at htriple
  rw [← span_pair_eq_line p hp W hW hij hi hj, SpanRank.mem_pair_iff_rank _ _ _ (projective_pair_rank hpij)]
  rw [Set.mem_range, ← AffineChart.lift_mem_span_pair, SpanRank.mem_pair_iff_rank _ _ _ hpair, htriple]
  omega

theorem distinct_lines_of_ranks {J : Type*}
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W) (i j : J → ι) (hij : ∀ l, i l ≠ j l)
    (hi : ∀ l, (p (i l)).rep ∈ W l) (hj : ∀ l, (p (j l)).rep ∈ W l) :
    Function.Injective (fun l => Set.range (fun t : L => a (i l)+t • (a (j l)-a (i l)))) := by
  intro l m hlm
  dsimp only at hlm
  apply hWinj
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← span_pair_eq_line p hp (W l) (hW l) (hij l) (hi l) (hj l)]
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with rfl | hz
    · apply (line_incidence_of_ranks p hp a hr (W m) (hW m) (hij m) (hi m) (hj m) _).mpr
      rw [← hlm]
      exact ⟨0, by simp⟩
    · rw [Set.mem_singleton_iff] at hz
      subst z
      apply (line_incidence_of_ranks p hp a hr (W m) (hW m) (hij m) (hi m) (hj m) _).mpr
      rw [← hlm]
      exact ⟨1, by simp⟩
  · rw [hW, hW]
end

open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι : Type*} [Field K] [Field L] [Fintype I] [Fintype ι]

theorem line_count_of_ranks
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L) (ha : Function.Injective a)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (W : Submodule K (I → K)) (hW : finrank K W = 2)
    {i j : ι} (hij : i ≠ j) (hi : (p i).rep ∈ W) (hj : (p j).rep ∈ W) :
    (Finset.univ.filter (fun k => (p k).rep ∈ W)).card =
      ((Finset.univ.image a).filter (fun y =>
        y ∈ Set.range (fun t : L => a i+t • (a j-a i)))).card := by
  classical
  apply Finset.card_bij (fun k _ => a k)
  · intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (line_incidence_of_ranks p hp a hr W hW hij hi hj k).mp (Finset.mem_filter.mp hk).2
  · intro k hk l hl hkl
    exact ha hkl
  · intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (line_incidence_of_ranks p hp a hr W hW hij hi hj k).mpr (Finset.mem_filter.mp hy).2

omit [Fintype I] in

theorem exists_line_indices {J : Type*}
    (p : ι → ℙ K (I → K)) (W : J → Submodule K (I → K))
    (hM : ∀ l, 2 ≤ (Finset.univ.filter (fun k => (p k).rep ∈ W l)).card) :
    ∃ i j : J → ι, (∀ l, i l ≠ j l) ∧
      (∀ l, (p (i l)).rep ∈ W l) ∧ (∀ l, (p (j l)).rep ∈ W l) := by
  classical
  have H (l : J) := Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) (hM l))
  choose i hi j hj hij using H
  exact ⟨i, j, hij, fun l => (Finset.mem_filter.mp (hi l)).2,
    fun l => (Finset.mem_filter.mp (hj l)).2⟩

theorem projective_line_card_le_sq {J : Type*} [Fintype J]
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W)
    (hM : ∀ l, 2 ≤ (Finset.univ.filter (fun k => (p k).rep ∈ W l)).card) :
    Fintype.card J ≤ (Fintype.card ι)^2 := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := exists_line_indices p W hM
  have hf : Function.Injective (fun l => (i l,j l)) := by
    intro l m hlm
    have hi' : i l = i m := congrArg Prod.fst hlm
    have hj' : j l = j m := congrArg Prod.snd hlm
    apply hWinj
    rw [← span_pair_eq_line p hp _ (hW l) (hij l) (hi l) (hj l),
      ← span_pair_eq_line p hp _ (hW m) (hij m) (hi m) (hj m), hi', hj']
  simpa [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective _ hf
end SharpRamseyFive.AffineRealization

end OAI
