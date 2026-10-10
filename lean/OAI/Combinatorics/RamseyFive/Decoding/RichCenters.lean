import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FlatPoints

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def richCenters (S : Finset (ℙ K V))
    (O : ℙ K V → Finset (ℙ K V)) (δ a : ℝ) (A : Submodule K V) : Finset (ℙ K V) :=
  (flatPoints A).filter fun x => a ≤ δ*((S \ (O x ∪ {x})).filter
    fun y => y.submodule ≤ A).card

lemma richCenters_mono (S T : Finset (ℙ K V))
    (O U : ℙ K V → Finset (ℙ K V)) (δ a : ℝ) (hδ : 0 ≤ δ)
    (hS : S ⊆ T) (hO : ∀ x, U x ⊆ O x) (A : Submodule K V) :
    richCenters S O δ a A ⊆ richCenters T U δ a A := by
  intro x hx
  obtain ⟨hxA,hx⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxA,hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hδ
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.sdiff_subset_sdiff hS (Finset.union_subset_union_left (hO x))))

lemma exists_scale {δ a : ℝ} (hδ : 0 < δ) (ha : 4*δ ≤ a) :
    ∃ M : ℕ, 0 < M ∧ 2*δ*M ≤ a ∧ a ≤ 4*δ*M := by
  have hx : 2 ≤ a/(2*δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hp : 1 ≤ ⌊a/(2*δ)⌋₊ := Nat.le_floor (by linarith)
  refine ⟨⌊a/(2*δ)⌋₊,by omega,?_,?_⟩
  · have hf := Nat.floor_le (by linarith : 0 ≤ a/(2*δ))
    have hh := (le_div_iff₀ (by positivity)).mp hf
    nlinarith
  · have hf := Nat.lt_floor_add_one (a/(2*δ))
    have hn : (1:ℝ) ≤ ⌊a/(2*δ)⌋₊ := by exact_mod_cast hp
    have hh : a/(2*δ) ≤ 2*⌊a/(2*δ)⌋₊ := by linarith
    have := (div_le_iff₀ (by positivity)).mp hh
    nlinarith

variable {I : Type*} [LinearOrder I]

theorem captured_rich_centers (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X : Finset (ℙ K V))
    (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2)
    (J M : ℕ) (hM : 0 < M) (hJM : J ≤ M)
    (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card)
    (O : ℙ K V → Finset (ℙ K V))
    (hO : ∀ x, ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (δ a : ℝ) (hδ : 0 < δ) (ha : 2*δ*M ≤ a) (ha' : a ≤ 4*δ*M) :
    (∑ A ∈ L, ((richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A).card:ℝ))*a^2 ≤
      192*δ^2*(X.card:ℝ)^2 := by
  have ha0 : 0 ≤ a := (by positivity : 0 ≤ 2*δ*M).trans ha
  have hsub (A : Submodule K V) : richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A ⊆
      capturedLineCenters F hF P X J (2*M) A := by
    intro x hx
    obtain ⟨hxA,hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxA,?_⟩
    have hs : (X \ remaining F hF (fun i => flatPoints (P i)) X J) \ (O x ∪ {x}) ⊆
        (X \ remaining F hF (fun i => flatPoints (P i)) X J) \
          ownCell F hF (fun i => flatPoints (P i)) X J x :=
      Finset.sdiff_subset_sdiff_right _ ((hO x).trans Finset.subset_union_left)
    have hc : ((((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        (O x ∪ {x})).filter fun y => y.submodule ≤ A).card:ℝ) ≤
        (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter
          fun y => y.submodule ≤ A).card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hs)
    have hh := ha.trans (hx.trans (mul_le_mul_of_nonneg_left hc hδ.le))
    have hm : ((2*M:ℕ):ℝ) ≤ (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter
          fun y => y.submodule ≤ A).card := by
      push_cast
      nlinarith
    exact_mod_cast hm
  have hsum : (∑ A ∈ L, ((richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A).card:ℝ)) ≤
      ∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) := by
    apply Finset.sum_le_sum
    intro A _
    exact_mod_cast Finset.card_le_card (hsub A)
  have hc := captured_center_line_count F hF P X hP L hL J M hM hJM hJq
  have ha2 := pow_le_pow_left₀ ha0 ha' 2
  calc
    _ ≤ (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*a^2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ ≤ (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(4*δ*M)^2 :=
      mul_le_mul_of_nonneg_left ha2 (Finset.sum_nonneg fun _ _ => by positivity)
    _ = 16*δ^2*((∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(M:ℝ)^2) := by ring
    _ ≤ 16*δ^2*(12*(X.card:ℝ)^2) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end SharpRamseyFive.GlobalRadial

end OAI
