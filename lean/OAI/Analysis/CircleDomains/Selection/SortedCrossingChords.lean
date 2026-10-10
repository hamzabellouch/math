import OAI.Analysis.CircleDomains.Selection.CrossingChords
import OAI.Analysis.CircleDomains.Rigidity.GapFluxTelescoping

namespace OAI

/-! Sorting the actual crossed disks gives a finite ordered hole family
with an injective owner map and exact signed flux accounting. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem horizontalChord_injective_on_crossing {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i))) {y a b : ℝ}
    {i j : I} (hi : i ∈ crossingDisks c r y a b) (hj : j ∈ crossingDisks c r y a b)
    (he : horizontalChord (c i) (r i) y = horizontalChord (c j) (r j) y) : i = j := by
  by_contra hij
  have hmem : (horizontalChord (c i) (r i) y).1 ∈
      Icc (horizontalChord (c i) (r i) y).1 (horizontalChord (c i) (r i) y).2 :=
    left_mem_Icc.mpr (horizontalChord_valid _ _ _)
  have hm1 := (mem_closedBall_iff_mem_horizontalChord _ (hr i) (crossingDisk_line_hit hi)).mpr hmem
  have hm2 := (mem_closedBall_iff_mem_horizontalChord _ (hr j) (crossingDisk_line_hit hj)).mpr (he ▸ hmem)
  exact disjoint_left.mp (hd hij) hm1 (by simpa only [← he] using hm2)

 structure SortedCrossingChords {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (y a b : ℝ) where
  count : ℕ
  hole : Fin count → ℝ × ℝ
  owner : Fin count → I
  owner_mem : ∀ i, owner i ∈ crossingDisks c r y a b
  owner_injective : Injective owner
  owner_surjective : ∀ j ∈ crossingDisks c r y a b, ∃ i, owner i = j
  hole_eq : ∀ i, hole i = horizontalChord (c (owner i)) (r (owner i)) y
  inside : ∀ i, a < (hole i).1 ∧ (hole i).1 ≤ (hole i).2 ∧ (hole i).2 < b
  separated : ∀ i j, i < j → (hole i).2 < (hole j).1

 theorem exists_sorted_crossing_chords {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i))) {y a b : ℝ}
    (ha : ∀ i, (⟨a,y⟩ : ℂ) ∉ closedBall (c i) (r i))
    (hb : ∀ i, (⟨b,y⟩ : ℂ) ∉ closedBall (c i) (r i)) :
    Nonempty (SortedCrossingChords c r y a b) := by
  classical
  let K := crossingChords c r y a b
  let H := K.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (i : Fin K.card) : H i ∈ K := K.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have honto (z : ℝ × ℝ) (hz : z ∈ K) : ∃ i, H i = z := by
    let z' : (K : Finset (ℝ ×ₗ ℝ)) := ⟨z,hz⟩
    exact ⟨(K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z',
      congrArg Subtype.val ((K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')⟩
  have howner (i : Fin K.card) : ∃ j ∈ crossingDisks c r y a b,
      horizontalChord (c j) (r j) y = H i := Finset.mem_image.mp (hmem i)
  choose owner howner heq using howner
  have hi := crossingChords_inside c r hr ha hb
  refine ⟨⟨K.card,H,owner,howner,?_,?_,(fun i => (heq i).symm),
    (fun i => hi _ (hmem i)),?_⟩⟩
  · intro i j hij
    apply H.injective
    rw [← heq i,← heq j,hij]
  · intro j hj
    obtain ⟨i,hi⟩ := honto _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    exact ⟨i,horizontalChord_injective_on_crossing c r hr hd (howner i) hj ((heq i).trans hi)⟩
  · exact sorted_holes_separated K (fun z hz => (hi z hz).2.1) (crossingChords_disjoint c r hr hd)

 namespace SortedCrossingChords
 variable {I : Type*} [Fintype I] {c : I → ℂ} {r : I → ℝ} {y a b : ℝ}

 theorem sum_hole_increments (S : SortedCrossingChords c r y a b) (v : ℝ → ℝ) :
    (∑ i, (v (S.hole i).2-v (S.hole i).1)) =
      ∑ j ∈ crossingDisks c r y a b,
        (v (horizontalChord (c j) (r j) y).2-v (horizontalChord (c j) (r j) y).1) := by
  classical
  apply Finset.sum_bij (fun i _ => S.owner i)
  · exact fun i _ => S.owner_mem i
  · exact fun i _ j _ h => S.owner_injective h
  · intro j hj
    obtain ⟨i,hi⟩ := S.owner_surjective j hj
    exact ⟨i,Finset.mem_univ _,hi⟩
  · intro i _
    rw [S.hole_eq]

 theorem monotone_first (S : SortedCrossingChords c r y a b) : Monotone (fun i => (S.hole i).1) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (S.inside i).2.1.trans (S.separated i j h).le

 theorem monotone_last (S : SortedCrossingChords c r y a b) : Monotone (fun i => (S.hole i).2) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (S.separated i j h).le.trans (S.inside j).2.1

 end SortedCrossingChords
end CircleDomainRigidity

end

end OAI
