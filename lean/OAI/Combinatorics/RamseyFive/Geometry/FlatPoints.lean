import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.CardFilterContainment
import OAI.Combinatorics.RamseyFive.Decoding.Best
import OAI.Combinatorics.RamseyFive.Entropy.IndexMul

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def flatPoints (A : Submodule K V) : Finset (ℙ K V) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  exact Finset.univ.filter fun x => x.submodule ≤ A

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

lemma inter_flatPoints (X : Finset (ℙ K V)) (A : Submodule K V) :
    X ∩ flatPoints A = X.filter fun x => x.submodule ≤ A := by
  ext x
  simp only [Finset.mem_inter,mem_flatPoints,Finset.mem_filter]

lemma line_covered_cap {I : Type*} [DecidableEq I] (T : Finset I)
    (P : I → Submodule K V) (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A = 2) (hn : ∀ i ∈ T, ¬A ≤ P i)
    (hcover : ∀ x ∈ X, x.submodule ≤ A → ∃ i ∈ T, x.submodule ≤ P i) :
    (X.filter fun x => x.submodule ≤ A).card ≤ T.card := by
  let Y (i : I) := X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ P i
  have hsub : X.filter (fun x => x.submodule ≤ A) ⊆ T.biUnion Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxX hxA
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxX,hxA,hxi⟩⟩
  have hsum : ∑ i ∈ T, (Y i).card ≤ ∑ _i ∈ T, (1:ℕ) :=
    Finset.sum_le_sum (fun i hi => line_noncontaining_flat_cap X A (P i) hA (hn i hi))
  exact (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans (by simpa using hsum))

lemma plane_covered_cap {I : Type*} [DecidableEq I] (T : Finset I)
    (P : I → Submodule K V) (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A = 3) (hn : ∀ i ∈ T, ¬A ≤ P i)
    (hcover : ∀ x ∈ X, x.submodule ≤ A → ∃ i ∈ T, x.submodule ≤ P i) :
    (X.filter fun x => x.submodule ≤ A).card ≤ T.card*(Nat.card K+1) := by
  let Y (i : I) := X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ P i
  have hsub : X.filter (fun x => x.submodule ≤ A) ⊆ T.biUnion Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxX hxA
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxX,hxA,hxi⟩⟩
  have hsum : ∑ i ∈ T, (Y i).card ≤ ∑ _i ∈ T, (Nat.card K+1) :=
    Finset.sum_le_sum (fun i hi => plane_noncontaining_flat_cap X A (P i) hA (hn i hi))
  exact (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans (by simpa using hsum))

variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma captured_cover (J : ℕ) (x : ℙ K V)
    (hx : x ∈ X \ remaining F hF (fun i => flatPoints (P i)) X J) :
    ∃ j ∈ Finset.range J, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  rw [remaining_eq_sdiff_union] at hx
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hxX := (Finset.mem_sdiff.mp hx).1
  have hm : x ∈ (Finset.range J).biUnion (fun j => flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X j))) := by
    by_contra hn
    exact hxnot (Finset.mem_sdiff.mpr ⟨hxX,hn⟩)
  obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hm
  exact ⟨j,hj,(mem_flatPoints _ _).mp hxj⟩

lemma rich_line_has_containing_flat (J M : ℕ) (hJM : J < M)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hM : M ≤ ((X \ remaining F hF (fun i => flatPoints (P i)) X J).filter
      fun x => x.submodule ≤ A).card) :
    ∃ j < J, A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  by_contra hn
  push Not at hn
  have hc := line_covered_cap (Finset.range J)
    (fun j => P (chosen F hF (fun i => flatPoints (P i)) X j))
    (X \ remaining F hF (fun i => flatPoints (P i)) X J) A hA
    (fun j hj => hn j (Finset.mem_range.mp hj))
    (fun x hx _ => captured_cover F hF P X J x hx)
  rw [Finset.card_range] at hc
  omega

lemma head_plane_points (J cap : ℕ) (A : Submodule K V) (hA : finrank K A = 3)
    (hn : ∀ j < headIndex F hF (fun i => flatPoints (P i)) X J cap,
      ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) :
    ((X \ remaining F hF (fun i => flatPoints (P i)) X
      (headIndex F hF (fun i => flatPoints (P i)) X J cap)).filter
      fun x => x.submodule ≤ A).card ≤
        headIndex F hF (fun i => flatPoints (P i)) X J cap*(Nat.card K+1) := by
  have hh := plane_covered_cap (Finset.range (headIndex F hF (fun i => flatPoints (P i)) X J cap))
    (fun j => P (chosen F hF (fun i => flatPoints (P i)) X j))
    (X \ remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap)) A hA
    (fun j hj => hn j (Finset.mem_range.mp hj))
    (fun x hx _ => captured_cover F hF P X _ x hx)
  simpa only [Finset.card_range] using hh

lemma atlas_head_tail_cap (J cap : ℕ) (a : I) (ha : a ∈ F) :
    ((remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
      remaining F hF (fun i => flatPoints (P i)) X J).filter
      fun x => x.submodule ≤ P a).card ≤ cap := by
  have hh := head_tail_cap F hF (fun i => flatPoints (P i)) X J cap a ha
  simpa only [inter_flatPoints] using hh

lemma outside_cell_earlier (j : ℕ) (A : Submodule K V)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (y : ℙ K V) (hyX : y ∈ X) (hyA : y.submodule ≤ A)
    (hycell : y ∉ cell F hF (fun i => flatPoints (P i)) X j) :
    y ∈ X \ remaining F hF (fun i => flatPoints (P i)) X j := by
  refine Finset.mem_sdiff.mpr ⟨hyX, ?_⟩
  intro hyr
  exact hycell (Finset.mem_inter.mpr ⟨hyr, (mem_flatPoints _ _).mpr (hyA.trans hAj)⟩)

lemma earliest_line_outside_cell_cap (j : ℕ) (A : Submodule K V)
    (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      fun y => y.submodule ≤ A).card ≤ j := by
  have hs : (X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      (fun y => y.submodule ≤ A) ⊆
      (X \ remaining F hF (fun i => flatPoints (P i)) X j).filter
        (fun y => y.submodule ≤ A) := by
    intro y hy
    obtain ⟨hy,hya⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyX,hyc⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_filter.mpr ⟨outside_cell_earlier F hF P X j A hAj y hyX hya hyc,hya⟩
  have hc := line_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i))
    (X \ remaining F hF (fun i => flatPoints (P i)) X j) A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi))
    (fun y hy _ => captured_cover F hF P X j y hy)
  exact (Finset.card_le_card hs).trans (by simpa only [Finset.card_range] using hc)

lemma earliest_plane_outside_cell_cap (j : ℕ) (A : Submodule K V)
    (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      fun y => y.submodule ≤ A).card ≤ j*(Nat.card K+1) := by
  have hs : (X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      (fun y => y.submodule ≤ A) ⊆
      (X \ remaining F hF (fun i => flatPoints (P i)) X j).filter
        (fun y => y.submodule ≤ A) := by
    intro y hy
    obtain ⟨hy,hya⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyX,hyc⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_filter.mpr ⟨outside_cell_earlier F hF P X j A hAj y hyX hya hyc,hya⟩
  have hc := plane_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i))
    (X \ remaining F hF (fun i => flatPoints (P i)) X j) A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi))
    (fun y hy _ => captured_cover F hF P X j y hy)
  exact (Finset.card_le_card hs).trans (by simpa only [Finset.card_range] using hc)

lemma surviving_line_center_earlier (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (x : ℙ K V) (hxA : x.submodule ≤ A)
    (hrich : j < ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card) :
    ∃ i < j, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
  by_contra hn
  push Not at hn
  have heq := ownCell_eq F hF (fun i => flatPoints (P i)) X J j x hj
    ((mem_flatPoints _ _).mpr (hxA.trans hAj))
    (fun i hi hmem => hn i hi ((mem_flatPoints _ _).mp hmem))
  rw [heq] at hrich
  exact (not_lt_of_ge (earliest_line_outside_cell_cap F hF P X j A hA hAj hearlier)) hrich

lemma surviving_plane_center_earlier (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (x : ℙ K V) (hxA : x.submodule ≤ A)
    (hrich : j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card) :
    ∃ i < j, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
  by_contra hn
  push Not at hn
  have heq := ownCell_eq F hF (fun i => flatPoints (P i)) X J j x hj
    ((mem_flatPoints _ _).mpr (hxA.trans hAj))
    (fun i hi hmem => hn i hi ((mem_flatPoints _ _).mp hmem))
  rw [heq] at hrich
  exact (not_lt_of_ge (earliest_plane_outside_cell_cap F hF P X j A hA hAj hearlier)) hrich

lemma surviving_line_centers_cap (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((flatPoints A).filter fun x => j <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card).card ≤ j := by
  let C := (flatPoints A).filter fun x => j <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card
  have hall (x : ℙ K V) (hx : x ∈ C) : x.submodule ≤ A :=
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp hx).1
  have hc := line_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i)) C A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi)) (by
      intro x hx hxa
      obtain ⟨i,hi,hxi⟩ := surviving_line_center_earlier F hF P X J j hj A hA hAj hearlier
        x hxa (Finset.mem_filter.mp hx).2
      exact ⟨i,Finset.mem_range.mpr hi,hxi⟩)
  rw [Finset.filter_eq_self.mpr hall,Finset.card_range] at hc
  exact hc

lemma surviving_plane_centers_cap (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((flatPoints A).filter fun x => j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card).card ≤ j*(Nat.card K+1) := by
  let C := (flatPoints A).filter fun x => j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card
  have hall (x : ℙ K V) (hx : x ∈ C) : x.submodule ≤ A :=
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp hx).1
  have hc := plane_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i)) C A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi)) (by
      intro x hx hxa
      obtain ⟨i,hi,hxi⟩ := surviving_plane_center_earlier F hF P X J j hj A hA hAj hearlier
        x hxa (Finset.mem_filter.mp hx).2
      exact ⟨i,Finset.mem_range.mpr hi,hxi⟩)
  rw [Finset.filter_eq_self.mpr hall,Finset.card_range] at hc
  exact hc

noncomputable def cellRichLines (L : Finset (Submodule K V)) (j M : ℕ) :
    Finset (Submodule K V) :=
  L.filter fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) ∧
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card

lemma cell_filter_own_flat (j : ℕ) :
    ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y =>
      y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cell F hF (fun i => flatPoints (P i)) X j := by
  apply Finset.filter_eq_self.mpr
  intro y hy
  exact (mem_flatPoints _ _).mp (Finset.mem_inter.mp hy).2

lemma card_cellRichLines_le (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (j M : ℕ) :
    (cellRichLines F hF P X L j M).card ≤ ProjectiveIncidence.Q (Nat.card K) 2 := by
  apply (Finset.card_le_card (show cellRichLines F hF P X L j M ⊆
      L.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) from
      fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,(Finset.mem_filter.mp hA).2.1⟩)).trans
  exact card_hyperplanes_inside _ (hP _ (chosen_mem F hF _ X j)) L hL

lemma cellRichLines_variance (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (j M : ℕ)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 1:ℝ)/ProjectiveIncidence.Q (Nat.card K) 2)*
      (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M) :
    ((cellRichLines F hF P X L j M).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)*(cell F hF (fun i => flatPoints (P i)) X j).card := by
  let C := cell F hF (fun i => flatPoints (P i)) X j
  let G := L.filter fun A => M ≤ (C.filter fun y => y.submodule ≤ A).card
  have hG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 2 :=
    hL A (Finset.mem_filter.mp hA).1
  have hm (A : Submodule K V) (hA : A ∈ G) : M ≤ (C.filter fun y => y.submodule ≤ A).card :=
    (Finset.mem_filter.mp hA).2
  have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) (2-1):ℝ)/ProjectiveIncidence.Q (Nat.card K) 2)*
      (C.filter fun y => y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)).card ≤ M := by
    simpa only [C,cell_filter_own_flat] using hmean
  have hh := rich_hyperplanes_inside_subspace (by omega : 1 ≤ (2:ℕ))
    (P (chosen F hF (fun i => flatPoints (P i)) X j)) (hP _ (chosen_mem F hF _ X j))
    G hG C M hm hμ
  have he : G.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cellRichLines F hF P X L j M := by
    ext A
    simp only [G,cellRichLines,Finset.mem_filter,C]
    tauto
  simpa only [he,C,cell_filter_own_flat,show (2:ℕ)-1=1 from rfl,pow_one] using hh

theorem weighted_cell_rich_lines (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (J M : ℕ)
    (hM : 0 < M) (hJ : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card) :
    (∑ j ∈ Finset.range J, (j:ℝ)*(cellRichLines F hF P X L j M).card)*(M:ℝ)^2 ≤
      12*(X.card:ℝ)^2 := by
  let q : ℝ := Nat.card K
  let N : ℝ := ProjectiveIncidence.Q (Nat.card K) 2
  let p : ℝ := (ProjectiveIncidence.Q (Nat.card K) 1:ℝ)/N
  let s (j : ℕ) : ℝ := (cell F hF (fun i => flatPoints (P i)) X j).card
  let m (j : ℕ) : ℝ := (cellRichLines F hF P X L j M).card
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (show 1 ≤ Nat.card K from (Finite.one_lt_card (α := K)).le)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 2
  have hpq : p*q ≤ 1 := by
    dsimp [p,q,N]
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 2)).mpr
    have he := ProjectiveIncidence.Q_recurrence (q := Nat.card K) (d := 2) (by omega)
    push_cast [he]
    nlinarith
  have hNq : N ≤ 3*q^2 := by
    have he : N = 1+q+q^2 := by
      simp [N,q,ProjectiveIncidence.Q,Finset.sum_range_succ]
    rw [he]
    nlinarith
  have hbudget : ∑ j ∈ Finset.range J, s j ≤ X.card := by
    have hh := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
    have hn : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
    dsimp [s]
    exact_mod_cast hn
  apply GreedyWeightedCount.weighted_rich_count J s m q M X.card p N
  · intro j; exact Nat.cast_nonneg _
  · intro i j hij
    dsimp [s]
    exact_mod_cast cell_card_antitone F hF (fun i => flatPoints (P i)) X hij
  · intro j _
    exact ⟨Nat.cast_nonneg _, by dsimp [m,N]; exact_mod_cast card_cellRichLines_le F hF P X hP L hL j M⟩
  · exact hq.trans' zero_le_one
  · exact_mod_cast hM
  · dsimp [p]; positivity
  · exact hN.le
  · exact hpq
  · exact hNq
  · exact hbudget
  · exact hJ
  · intro j _ hj
    exact cellRichLines_variance F hF P X hP L hL j M hj

noncomputable def capturedLineCenters (J M : ℕ) (A : Submodule K V) :
    Finset (ℙ K V) :=
  (flatPoints A).filter fun x => M ≤
    (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
      ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card

lemma earliest_line_cell_rich (j M : ℕ) (hj : j ≤ M)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (hrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card) :
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card := by
  have hcap := earliest_line_outside_cell_cap F hF P X j A hA hAj hearlier
  have hsub : X.filter (fun y => y.submodule ≤ A) ⊆
      ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) ∪
      ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) := by
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem captured_center_line_count (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (J M : ℕ)
    (hM : 0 < M) (hJM : J ≤ M) (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card) :
    (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(M:ℝ)^2 ≤
      12*(X.card:ℝ)^2 := by
  have hrow (A : Submodule K V) (hA : A ∈ L) :
      ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) ≤
        ∑ j ∈ Finset.range J, if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0 := by
    by_cases he : (capturedLineCenters F hF P X J (2*M) A).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxc := (Finset.mem_filter.mp hx).2
      have hcaprich : 2*M ≤ ((X \ remaining F hF (fun i => flatPoints (P i)) X J).filter
          fun y => y.submodule ≤ A).card :=
        hxc.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hfullrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card :=
        hcaprich.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hcont := rich_line_has_containing_flat F hF P X J (2*M) (by omega) A (hL A hA) hcaprich
      let j := Nat.find hcont
      have hj : j < J := (Nat.find_spec hcont).1
      have hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := (Nat.find_spec hcont).2
      have hearlier (i : ℕ) (hi : i < j) : ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
        intro hiA
        exact Nat.find_min hcont hi ⟨hi.trans hj,hiA⟩
      have hmem : A ∈ cellRichLines F hF P X L j M :=
        Finset.mem_filter.mpr ⟨hA,hAj,earliest_line_cell_rich F hF P X j M
          (hj.le.trans hJM) A (hL A hA) hAj hearlier hfullrich⟩
      have hsub : capturedLineCenters F hF P X J (2*M) A ⊆
          (flatPoints A).filter (fun z => j <
            ((X \ ownCell F hF (fun i => flatPoints (P i)) X J z).filter fun y => y.submodule ≤ A).card) := by
        intro z hz
        obtain ⟨hzA,hzr⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_filter.mpr ⟨hzA, ?_⟩
        have hc := hzr.trans (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.sdiff_subset_sdiff_left _ Finset.sdiff_subset)))
        omega
      have hc := (Finset.card_le_card hsub).trans
        (surviving_line_centers_cap F hF P X J j hj A (hL A hA) hAj hearlier)
      have hsingle : (j:ℝ) ≤ ∑ k ∈ Finset.range J,
          if A ∈ cellRichLines F hF P X L k M then (k:ℝ) else 0 := by
        have hh := Finset.single_le_sum (s := Finset.range J)
          (f := fun k => if A ∈ cellRichLines F hF P X L k M then (k:ℝ) else 0)
          (fun k _ => by positivity) (Finset.mem_range.mpr hj)
        simpa only [ite_eq_left hmem] using hh
      exact (by exact_mod_cast hc : ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) ≤ (j:ℝ)).trans hsingle
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
      exact Finset.sum_nonneg (fun j _ => by positivity)
  have hsum := Finset.sum_le_sum hrow
  have hcount (j : ℕ) :
      (∑ A ∈ L, if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0) =
        (j:ℝ)*(cellRichLines F hF P X L j M).card := by
    have hsub : cellRichLines F hF P X L j M ⊆ L := Finset.filter_subset _ _
    have hh := Finset.sum_subset hsub (f := fun A => if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0)
      (fun _ _ hn => ite_eq_right hn)
    rw [← hh]
    simp [mul_comm]
  rw [Finset.sum_comm] at hsum
  simp_rw [hcount] at hsum
  exact (mul_le_mul_of_nonneg_right hsum (sq_nonneg _)).trans
    (weighted_cell_rich_lines F hF P X hP L hL J M hM hJq)

end SharpRamseyFive.ProjectiveTraining

end OAI
