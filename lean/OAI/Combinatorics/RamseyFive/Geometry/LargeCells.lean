import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.MultiplicityBudgets
import OAI.Combinatorics.RamseyFive.Geometry.FlatPoints

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma chosen_shape_ne_of_positive_cell {i j : ℕ} (hij : i < j)
    (hpos : 0 < (cell F hF (fun i => flatPoints (P i)) X j).card) :
    P (chosen F hF (fun i => flatPoints (P i)) X i) ≠
      P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  intro he
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
  have hyr : y ∈ remaining F hF (fun i => flatPoints (P i)) X (i+1) :=
    remaining_antitone F hF _ X hij (cell_subset F hF _ X j hy)
  have hn := (Finset.mem_sdiff.mp hyr).2
  apply hn
  change y ∈ flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X i))
  rw [he]
  exact (Finset.mem_inter.mp hy).2

noncomputable def largeCells (J : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.range J).filter fun j => c ≤ (cell F hF (fun i => flatPoints (P i)) X j).card

lemma largeCells_card_budget (J : ℕ) (c : ℝ) :
    ((largeCells F hF P X J c).card:ℝ)*c ≤ X.card := by
  have hs := Finset.sum_le_sum (s := largeCells F hF P X J c)
    (fun j hj => (Finset.mem_filter.mp hj).2)
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (show largeCells F hF P X J c ⊆ Finset.range J from Finset.filter_subset _ _)
    (f := fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ))
    (fun _ _ _ => Nat.cast_nonneg _)
  have hh := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
  have hn : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
  exact (hs.trans hle).trans (by exact_mod_cast hn)

lemma earlier_mem_largeCells (J : ℕ) (c : ℝ) {i j : ℕ}
    (hj : j ∈ largeCells F hF P X J c) (hij : i ≤ j) :
    i ∈ largeCells F hF P X J c := by
  obtain ⟨hjJ,hjc⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hij.trans_lt (Finset.mem_range.mp hjJ)),
    hjc.trans (by exact_mod_cast cell_card_antitone F hF (fun i => flatPoints (P i)) X hij)⟩

noncomputable def largeCellIntersections (J : ℕ) (c : ℝ) : Finset (ℙ K V) :=
  ((largeCells F hF P X J c) ×ˢ (largeCells F hF P X J c)).biUnion fun ij =>
    if ij.1 = ij.2 then ∅ else
    flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.1)) ∩
    flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.2))

lemma hyperplane_intersection_cap (A H : Submodule K V)
    (hA : finrank K A = 4) (hH : finrank K H = 4) (hne : A ≠ H) :
    (flatPoints A ∩ flatPoints H).card ≤ ProjectiveIncidence.Q (Nat.card K) 2 := by
  have hnot : ¬A ≤ H := fun hh => hne (Submodule.eq_of_le_of_finrank_eq hh (hA.trans hH.symm))
  have hd := finrank_inf_lt_of_not_le A H hnot
  have hd' : finrank K (A ⊓ H : Submodule K V) ≤ 3 := by omega
  have he : flatPoints A ∩ flatPoints H =
      (flatPoints A ∩ flatPoints H).filter fun x => x.submodule ≤ A ⊓ H := by
    symm
    refine Finset.filter_eq_self.mpr ?_
    intro x hx
    exact le_inf ((mem_flatPoints _ _).mp (Finset.mem_inter.mp hx).1)
      ((mem_flatPoints _ _).mp (Finset.mem_inter.mp hx).2)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd')
    (f := fun i => Nat.card K^i) (fun _ _ _ => Nat.zero_le _)
  have hc := (card_filter_containment_le (flatPoints A ∩ flatPoints H) (A ⊓ H)).trans hsum
  rw [← he] at hc
  exact hc

lemma largeCellIntersections_card (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (J : ℕ) (c : ℝ) (hc : 0 < c) :
    (largeCellIntersections F hF P X J c).card ≤
      (largeCells F hF P X J c).card^2*ProjectiveIncidence.Q (Nat.card K) 2 := by
  let B := largeCells F hF P X J c
  have hrow (ij : ℕ × ℕ) (hij : ij ∈ B ×ˢ B) :
      (if ij.1 = ij.2 then (∅:Finset (ℙ K V)) else
        flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.1)) ∩
        flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.2))).card ≤
        ProjectiveIncidence.Q (Nat.card K) 2 := by
    by_cases he : ij.1 = ij.2
    · simp [he]
    rw [ite_eq_right he]
    apply hyperplane_intersection_cap _ _ (hP _ (chosen_mem F hF _ X _)) (hP _ (chosen_mem F hF _ X _))
    have hp (j : ℕ) (hj : j ∈ B) : 0 < (cell F hF (fun i => flatPoints (P i)) X j).card := by
      have hh := hc.trans_le (Finset.mem_filter.mp hj).2
      exact_mod_cast hh
    rcases lt_or_gt_of_ne he with hij' | hji'
    · exact chosen_shape_ne_of_positive_cell F hF P X hij' (hp _ (Finset.mem_product.mp hij).2)
    · exact (chosen_shape_ne_of_positive_cell F hF P X hji' (hp _ (Finset.mem_product.mp hij).1)).symm
  have hh := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,Finset.card_product,smul_eq_mul] at hh
  exact Finset.card_biUnion_le.trans (by simpa only [sq] using hh)

theorem largeCellIntersections_budget (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (J : ℕ) (c : ℝ) (hc : 0 < c) :
    ((largeCellIntersections F hF P X J c).card:ℝ)*c^2 ≤
      (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*(X.card:ℝ)^2 := by
  have hcard : ((largeCellIntersections F hF P X J c).card:ℝ) ≤
      ((largeCells F hF P X J c).card:ℝ)^2*(ProjectiveIncidence.Q (Nat.card K) 2:ℝ) := by
    exact_mod_cast largeCellIntersections_card F hF P X hP J c hc
  have hbudget := largeCells_card_budget F hF P X J c
  have hsquare := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hc.le) hbudget 2
  calc
    ((largeCellIntersections F hF P X J c).card:ℝ)*c^2 ≤
        ((largeCells F hF P X J c).card:ℝ)^2*(ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*c^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*
        (((largeCells F hF P X J c).card:ℝ)*c)^2 := by ring
    _ ≤ (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)*(X.card:ℝ)^2 :=
      mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg _)

lemma surviving_large_plane_center_mem (J j : ℕ) (hj : j < J) (c : ℝ)
    (hlarge : j ∈ largeCells F hF P X J c)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (x : ℙ K V) (hxA : x.submodule ≤ A)
    (hrich : j*(Nat.card K+1) <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card) :
    x ∈ largeCellIntersections F hF P X J c := by
  obtain ⟨i,hi,hxi⟩ := surviving_plane_center_earlier F hF P X J j hj A hA hAj hearlier x hxA hrich
  have hiB := earlier_mem_largeCells F hF P X J c hlarge hi.le
  refine Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hiB,hlarge⟩,?_⟩
  simp only [ite_eq_right (ne_of_lt hi)]
  exact Finset.mem_inter.mpr ⟨(mem_flatPoints _ _).mpr hxi,(mem_flatPoints _ _).mpr (hxA.trans hAj)⟩

lemma cellRichPlanes_variance (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3) (j M : ℕ)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*
      (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M) :
    ((cellRichLines F hF P X L j M).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^2*(cell F hF (fun i => flatPoints (P i)) X j).card := by
  let C := cell F hF (fun i => flatPoints (P i)) X j
  let G := L.filter fun A => M ≤ (C.filter fun y => y.submodule ≤ A).card
  have hG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 3 :=
    hL A (Finset.mem_filter.mp hA).1
  have hm (A : Submodule K V) (hA : A ∈ G) : M ≤ (C.filter fun y => y.submodule ≤ A).card :=
    (Finset.mem_filter.mp hA).2
  have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*
      (C.filter fun y => y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)).card ≤ M := by
    simpa only [C,cell_filter_own_flat] using hmean
  have hh := rich_planes_inside_hyperplane
    (P (chosen F hF (fun i => flatPoints (P i)) X j)) (hP _ (chosen_mem F hF _ X j))
    G hG C M hm hμ
  have he : G.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cellRichLines F hF P X L j M := by
    ext A
    simp only [G,cellRichLines,Finset.mem_filter,C]
    tauto
  simpa only [he,C,cell_filter_own_flat] using hh

theorem weighted_small_cell_rich_planes (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3) (J M : ℕ)
    (c : ℝ) (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*c ≤ M) :
    (∑ j ∈ (Finset.range J).filter (fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c),
      (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card)*(M:ℝ)^2 ≤
      4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*X.card := by
  let S := (Finset.range J).filter (fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c)
  have hr (j : ℕ) (hj : j ∈ S) :
      (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card*M^2 ≤
        4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*(cell F hF (fun i => flatPoints (P i)) X j).card := by
    have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*
        (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M :=
      (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hj).2.le (by positivity)).trans hmean
    have hv := cellRichPlanes_variance F hF P X hP L hL j M hμ
    have hjJ : (j:ℝ) ≤ J := by exact_mod_cast (Finset.mem_range.mp (Finset.mem_filter.mp hj).1).le
    calc
      _ = (j:ℝ)*(Nat.card K+1)*((cellRichLines F hF P X L j M).card*M^2) := by ring
      _ ≤ (j:ℝ)*(Nat.card K+1)*(4*(Nat.card K:ℝ)^2*(cell F hF (fun i => flatPoints (P i)) X j).card) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ (J:ℝ)*(Nat.card K+1)*(4*(Nat.card K:ℝ)^2*(cell F hF (fun i => flatPoints (P i)) X j).card) := by gcongr
      _ = _ := by ring
  have hs : (∑ j ∈ S, ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ)) ≤ X.card := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (show S ⊆ Finset.range J from Finset.filter_subset _ _)
      (f := fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
    have hn := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
    have hh : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
    exact hsub.trans (by exact_mod_cast hh)
  calc
    _ = ∑ j ∈ S, (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card*M^2 := by rw [Finset.sum_mul]
    _ ≤ ∑ j ∈ S, 4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*(cell F hF (fun i => flatPoints (P i)) X j).card := Finset.sum_le_sum hr
    _ = 4*(Nat.card K:ℝ)^2*(Nat.card K+1)*J*(∑ j ∈ S, ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

lemma earliest_plane_cell_rich (j M : ℕ) (hj : j*(Nat.card K+1) ≤ M)
    (A : Submodule K V) (hA : finrank K A = 3)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (hrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card) :
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card := by
  have hcap := earliest_plane_outside_cell_cap F hF P X j A hA hAj hearlier
  have hsub : X.filter (fun y => y.submodule ≤ A) ⊆
      ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) ∪
      ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) := by
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

noncomputable def headPlaneCenters (J H M : ℕ) (c : ℝ) (A : Submodule K V) : Finset (ℙ K V) :=
  (flatPoints A).filter fun x =>
    (∃ j < H, A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) ∧
    2*M ≤ ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card ∧
    x ∉ largeCellIntersections F hF P X H c

theorem head_center_plane_count (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3) (J H M : ℕ)
    (hHJ : H ≤ J) (hM : 0 < M) (hHM : H*(Nat.card K+1) ≤ M)
    (c : ℝ) (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*c ≤ M) :
    (∑ A ∈ L, ((headPlaneCenters F hF P X J H M c A).card:ℝ))*(M:ℝ)^2 ≤
      4*(Nat.card K:ℝ)^2*(Nat.card K+1)*H*X.card := by
  let S := (Finset.range H).filter (fun j => ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c)
  have hrow (A : Submodule K V) (hA : A ∈ L) :
      ((headPlaneCenters F hF P X J H M c A).card:ℝ) ≤
        ∑ j ∈ S, if A ∈ cellRichLines F hF P X L j M then (j:ℝ)*(Nat.card K+1) else 0 := by
    by_cases he : (headPlaneCenters F hF P X J H M c A).Nonempty
    · obtain ⟨x,hx⟩ := he
      obtain ⟨hxA,hcont,hxr,hxn⟩ := Finset.mem_filter.mp hx
      let j := Nat.find hcont
      have hjH : j < H := (Nat.find_spec hcont).1
      have hjJ := hjH.trans_le hHJ
      have hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := (Nat.find_spec hcont).2
      have hearlier (i : ℕ) (hi : i < j) : ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
        intro hiA
        exact Nat.find_min hcont hi ⟨hi.trans hjH,hiA⟩
      have hjM : j*(Nat.card K+1) ≤ M :=
        (Nat.mul_le_mul_right _ hjH.le).trans hHM
      have hjr : j*(Nat.card K+1) <
          ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card := by omega
      have hjSmall : ((cell F hF (fun i => flatPoints (P i)) X j).card:ℝ) < c := by
        by_contra hn
        have hjlarge : j ∈ largeCells F hF P X H c :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjH,le_of_not_gt hn⟩
        obtain ⟨i,hi,hxi⟩ := surviving_plane_center_earlier F hF P X J j hjJ A (hL A hA) hAj hearlier x
          ((mem_flatPoints _ _).mp hxA) hjr
        apply hxn
        have hiB := earlier_mem_largeCells F hF P X H c hjlarge hi.le
        refine Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hiB,hjlarge⟩,?_⟩
        simp only [ite_eq_right (ne_of_lt hi)]
        exact Finset.mem_inter.mpr ⟨(mem_flatPoints _ _).mpr hxi,
          (mem_flatPoints _ _).mpr (((mem_flatPoints _ _).mp hxA).trans hAj)⟩
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjH,hjSmall⟩
      have hfullrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card :=
        hxr.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hmem : A ∈ cellRichLines F hF P X L j M :=
        Finset.mem_filter.mpr ⟨hA,hAj,earliest_plane_cell_rich F hF P X j M hjM A (hL A hA)
          hAj hearlier hfullrich⟩
      have hsub : headPlaneCenters F hF P X J H M c A ⊆
          (flatPoints A).filter (fun z => j*(Nat.card K+1) <
            ((X \ ownCell F hF (fun i => flatPoints (P i)) X J z).filter fun y => y.submodule ≤ A).card) := by
        intro z hz
        obtain ⟨hzA,_,hzr,_⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzA,by omega⟩
      have hc := (Finset.card_le_card hsub).trans
        (surviving_plane_centers_cap F hF P X J j hjJ A (hL A hA) hAj hearlier)
      have hsingle : (j:ℝ)*(Nat.card K+1) ≤ ∑ k ∈ S,
          if A ∈ cellRichLines F hF P X L k M then (k:ℝ)*(Nat.card K+1) else 0 := by
        have hh := Finset.single_le_sum (s := S)
          (f := fun k => if A ∈ cellRichLines F hF P X L k M then (k:ℝ)*(Nat.card K+1) else 0)
          (fun k _ => by positivity) hjS
        simpa only [ite_eq_left hmem] using hh
      exact (by exact_mod_cast hc : ((headPlaneCenters F hF P X J H M c A).card:ℝ) ≤
        (j:ℝ)*(Nat.card K+1)).trans hsingle
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
      exact Finset.sum_nonneg (fun j _ => by positivity)
  have hsum := Finset.sum_le_sum hrow
  have hcount (j : ℕ) :
      (∑ A ∈ L, if A ∈ cellRichLines F hF P X L j M then (j:ℝ)*(Nat.card K+1) else 0) =
        (j:ℝ)*(Nat.card K+1)*(cellRichLines F hF P X L j M).card := by
    have hsub : cellRichLines F hF P X L j M ⊆ L := Finset.filter_subset _ _
    have hh := Finset.sum_subset hsub
      (f := fun A => if A ∈ cellRichLines F hF P X L j M then (j:ℝ)*(Nat.card K+1) else 0)
      (fun _ _ hn => ite_eq_right hn)
    rw [← hh]
    simp [mul_comm]
  rw [Finset.sum_comm] at hsum
  simp_rw [hcount] at hsum
  exact (mul_le_mul_of_nonneg_right hsum (sq_nonneg _)).trans
    (weighted_small_cell_rich_planes F hF P X hP L hL H M c hmean)

lemma actual_tail_hyperplane_cap
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (J cap : ℕ) (A : Submodule K V) (hA : finrank K A = 4) :
    ((remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
      remaining F hF (fun i => flatPoints (P i)) X J).filter fun x => x.submodule ≤ A).card ≤ cap := by
  obtain ⟨i,hi,rfl⟩ := hcover A hA
  exact atlas_head_tail_cap F hF P X J cap i hi

theorem actual_tail_rich_plane_exceptions
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (J cap M u D : ℕ) (hMpos : 0 < M)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hM : ∀ A ∈ L, M ≤
      ((remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
        remaining F hF (fun i => flatPoints (P i)) X J).filter fun x => x.submodule ≤ A).card)
    (hlineLarge : 2*(Nat.card K+1) ≤ M) (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/ProjectiveIncidence.Q (Nat.card K) 3)*cap ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*cap ≤ (u:ℝ)*M^2)
    (hlarge : 64*X.card ≤ M^2) (hD : 8*(2*u+1) ≤ D)
    (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D ≤ (L.filter fun A => x.submodule ≤ A).card).card:ℝ)*D^2*M^2 ≤
      4096*(X.card:ℝ)^2*(2*(u:ℝ)+1)^2 := by
  let T := remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
      remaining F hF (fun i => flatPoints (P i)) X J
  have hTX : T ⊆ X := fun _ hx => remaining_subset F hF _ X _ (Finset.mem_sdiff.mp hx).1
  have hc : T.card ≤ X.card := Finset.card_le_card hTX
  have hcap : ∀ A : Submodule K V, finrank K A = 4 → (T.filter fun x => x.submodule ≤ A).card ≤ cap :=
    actual_tail_hyperplane_cap F hF P X hcover J cap
  have hnum : 2*T.card ≤ u*M := (Nat.mul_le_mul_left _ hc).trans hlineNum
  have hlg : 64*T.card ≤ M^2 := (Nat.mul_le_mul_left _ hc).trans hlarge
  obtain ⟨hl,hh⟩ := multiplicity_budgets L hL T M cap u hMpos hM hcap hlineLarge hnum hmean hhyperNum
  have hr := capped_rich_plane_count L hL T M cap u hMpos hM hcap hlineLarge hnum hmean hhyperNum hlg
  have hex := RichPlaneOverlap.exceptional_centers L hL u hl hh Y D hD
  have hcr : (T.card:ℝ) ≤ X.card := by exact_mod_cast hc
  have hrX : (L.card:ℝ)*M ≤ 16*X.card*(2*(u:ℝ)+1) :=
    hr.trans (by gcongr)
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (L.card:ℝ)*M) hrX 2
  calc
    _ ≤ (16*(L.card:ℝ)^2)*(M:ℝ)^2 := mul_le_mul_of_nonneg_right hex (sq_nonneg _)
    _ = 16*((L.card:ℝ)*M)^2 := by ring
    _ ≤ 16*(16*X.card*(2*(u:ℝ)+1))^2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end SharpRamseyFive.ProjectiveTraining

end OAI
