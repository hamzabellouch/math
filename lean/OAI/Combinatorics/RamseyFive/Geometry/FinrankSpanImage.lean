import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SplitEquiv

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScalarExtension
open Module
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

theorem finrank_span_image [Finite I] (s : Set (I → K)) :
    finrank L (Submodule.span L (coordinateMap (L := L) '' s)) =
      finrank K (Submodule.span K s) := by
  have h := finrank_span_range (L := L) (fun v : s => v.val)
  rw [Set.range_comp, Subtype.range_val] at h
  exact h
end SharpRamseyFive.ScalarExtension

namespace SharpRamseyFive.AffineChart
open Module
variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V]

lemma span_lift_normalize {ι : Type*} (v : ι → K × U) (hv : ∀ i, (v i).1 ≠ 0) :
    Submodule.span K (Set.range (fun i => ((1 : K), normalize (v i)))) =
      Submodule.span K (Set.range v) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨i, rfl⟩
    change ((1 : K), normalize (v i)) ∈ _
    rw [lift_normalize _ (hv i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    rw [← reconstruct _ (hv i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma finrank_lift_normalize {ι : Type*} (e : V ≃ₗ[K] K × U)
    (v : ι → V) (hv : ∀ i, (e (v i)).1 ≠ 0) :
    finrank K (Submodule.span K (Set.range (fun i => ((1 : K), normalize (e (v i)))))) =
      finrank K (Submodule.span K (Set.range v)) := by
  rw [span_lift_normalize _ hv]
  change finrank K (Submodule.span K (Set.range (e.toLinearMap ∘ v))) = _
  rw [Set.range_comp, Submodule.span_image, LinearEquiv.finrank_map_eq]

lemma lift_mem_span_pair (x y z : U) :
    ((1 : K), z) ∈ Submodule.span K {((1 : K), x), ((1 : K), y)} ↔
      ∃ a : K, x + a • (y - x) = z := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    have h1 : a + b = 1 := by simpa using congrArg Prod.fst h
    have h2 : a • x + b • y = z := congrArg Prod.snd h
    refine ⟨b, ?_⟩
    rw [← h2, smul_sub, show a = 1-b by linear_combination h1]
    simp only [sub_smul, one_smul]
    abel
  · rintro ⟨a, rfl⟩
    refine ⟨1-a, a, ?_⟩
    ext
    · simp
    · change (1-a) • x + a • y = x + a • (y-x)
      simp only [sub_smul, one_smul, smul_sub]
      abel
end SharpRamseyFive.AffineChart

namespace SharpRamseyFive.ProjectiveReduction
open Module Submodule
variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem exists_to_four [FiniteDimensional K V]
    (hdim : finrank K V = 4 ∨ finrank K V = 5) (X : Finset V) :
    ∃ f : V →ₗ[K] (Fin 4 → K), Function.Surjective f ∧
      ∀ Y : Finset V, Y ⊆ X →
        finrank K (Submodule.span K (f '' (Y : Set V))) =
          min (finrank K (Submodule.span K (Y : Set V))) 4 := by
  rcases hdim with hd | hd
  · let e : V ≃ₗ[K] (Fin 4 → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
    refine ⟨e.toLinearMap, e.surjective, ?_⟩
    intro Y _
    rw [Submodule.span_image, LinearEquiv.finrank_map_eq]
    exact (min_eq_left (by simpa [hd] using (Submodule.span K (Y : Set V)).finrank_le)).symm
  · exact exists_projection_preserving_ranks 4 hd X

omit [Infinite K] in
lemma nonzero_of_rank_preserved {U : Type*} [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] U) (X : Finset V) (hf : ∀ Y : Finset V, Y ⊆ X →
      finrank K (Submodule.span K (f '' (Y : Set V))) =
        min (finrank K (Submodule.span K (Y : Set V))) 4)
    {v : V} (hv : v ∈ X) (hv0 : v ≠ 0) : f v ≠ 0 := by
  classical
  have h := hf {v} (by simpa)
  rw [Finset.coe_singleton, Set.image_singleton] at h
  rw [finrank_span_singleton hv0] at h
  intro h0
  rw [Submodule.span_singleton_eq_bot.mpr h0] at h
  simp at h
end SharpRamseyFive.ProjectiveReduction

namespace SharpRamseyFive.AffineRealization
open Module
open AffineChart ScalarExtension ProjectiveReduction
variable {K L I ι : Type*} [Field K] [Field L] [Algebra K L] [Infinite L]
    [Fintype I] [Fintype ι] [Nonempty ι]

theorem exists_realization (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (v : ι → I → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a : ι → Fin 3 → L, ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K (v '' (Y : Set ι)))) 4 := by
  classical
  let w : ι → I → L := coordinateMap ∘ v
  let X : Finset (I → L) := Finset.univ.image w
  obtain ⟨f, _, hr⟩ := exists_to_four (K := L)
    (V := I → L) (by simpa using hI) X
  have hw (i : ι) : f (w i) ≠ 0 :=
    nonzero_of_rank_preserved f X hr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (coordinateMap_ne_zero _ (hv i))
  obtain ⟨e, he⟩ := exists_coordinates_of_vectors (K := L) 3 (by simp)
    (fun i => f (w i)) hw
  refine ⟨fun i => normalize (e (f (w i))), ?_⟩
  intro Y
  have hnorm := finrank_lift_normalize e (fun i : Y => f (w i.val)) (fun i => he i.val)
  have hrY := hr (Y.image w) (Finset.image_subset_image (Finset.subset_univ Y))
  have hscalar := finrank_span_image (L := L) (v '' (Y : Set ι))
  have hn : Set.range (fun i : Y => f (w i.val)) = f '' (w '' (Y : Set ι)) := by
    ext z
    simp
  have hn' : Set.range (fun i : Y => ((1 : L), normalize (e (f (w i.val))))) =
      (fun i => ((1 : L), normalize (e (f (w i))))) '' (Y : Set ι) := by
    ext z
    simp
  rw [hn, hn'] at hnorm
  rw [Finset.coe_image] at hrY
  rw [hnorm, hrY]
  congr 1
  rw [Set.image_image] at hscalar
  exact hscalar
end SharpRamseyFive.AffineRealization

namespace SharpRamseyFive.SubspaceExtension
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

theorem exists_add_rank (W : Submodule K V) (k : ℕ)
    (hk : finrank K W + k ≤ finrank K V) :
    ∃ U : Submodule K V, W ≤ U ∧ finrank K U = finrank K W + k := by
  induction k with
  | zero => exact ⟨W, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨U, hWU, hU⟩ := ih (by omega)
    have hUt : U ≠ ⊤ := by
      intro he
      rw [he, finrank_top] at hU
      omega
    have hx : ∃ x : V, x ∉ U := by
      by_contra! h
      apply hUt
      ext x
      simp [h]
    obtain ⟨x, hx⟩ := hx
    refine ⟨U ⊔ K ∙ x, hWU.trans le_sup_left, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hx, hU]
    omega

theorem exists_rank (W : Submodule K V) (n : ℕ)
    (hW : finrank K W ≤ n) (hn : n ≤ finrank K V) :
    ∃ U : Submodule K V, W ≤ U ∧ finrank K U = n := by
  obtain ⟨U, hU, hr⟩ := exists_add_rank W (n - finrank K W) (by omega)
  exact ⟨U, hU, by omega⟩
end SharpRamseyFive.SubspaceExtension

end OAI
