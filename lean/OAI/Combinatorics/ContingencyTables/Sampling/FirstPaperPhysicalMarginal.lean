import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperProfiles
import OAI.Combinatorics.ContingencyTables.Transport.NestedReindex

namespace OAI

/-!
# The first paper's physical hard marginal and its proved raw signature

This bridges the finite balanced-pair elimination theorem to the actual
supported padded-completion count, in the original row/column coordinates.
-/

namespace ContingencyTables.FirstPaperPhysicalMarginal

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles FirstPaperProfiles CompletionCounts
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def fullHardFamily (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : (((I×J)×Bool) → ℕ) → ℝ :=
  hardWeight cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope

noncomputable def fullSoftFamily (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ) : (((I×J)×Bool) → ℕ) → ℝ :=
  softWeight cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope a

noncomputable def hardMarginal (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) : ℝ :=
  ∑ a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2),
    fullHardFamily small B r c L
      (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a)

noncomputable def softMarginal (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) : ℝ :=
  ∑ u : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2),
    fullSoftFamily small B r c L a
      (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z u)

private theorem hardMarginal_eq_eliminate (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => small a.1 a.2)) :
    hardMarginal small B r c L=
      BalancedFamily.eliminate (widths (fun k => B (e k).val.1 (e k).val.2))
        (fun q => fullHardFamily small B r c L
          (q ∘ (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e
            (fun k => B (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  symm
  rw [eliminate_eq_actual_cells (fun a : I×J => small a.1 a.2) e
    (fun k => B (e k).val.1 (e k).val.2) (fullHardFamily small B r c L) z,
    sum_joined_eq_physical (fun a : I×J => small a.1 a.2)
      (fun a : I×J => B a.1 a.2) e z (fullHardFamily small B r c L)]
  unfold hardMarginal
  congr 2
  exact Subsingleton.elim _ _

private theorem softMarginal_eq_eliminate (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => small a.1 a.2)) :
    softMarginal small B r c L a=
      BalancedFamily.eliminate (widths (fun k => B (e k).val.1 (e k).val.2))
        (fun q => fullSoftFamily small B r c L a
          (q ∘ (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e
            (fun k => B (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  symm
  rw [eliminate_eq_actual_cells (fun a : I×J => small a.1 a.2) e
    (fun k => B (e k).val.1 (e k).val.2) (fullSoftFamily small B r c L a) z,
    sum_joined_eq_physical (fun a : I×J => small a.1 a.2)
      (fun a : I×J => B a.1 a.2) e z (fullSoftFamily small B r c L a)]
  unfold softMarginal
  congr 2
  exact Subsingleton.elim _ _

/-- The literal positive soft count has its raw removal signature on
every required profile box and degree, before taking the hard limit. -/
theorem softMarginal_slices (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (a : ℝ) (ha : 0≤a)
    (m : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (R : ℕ)
    (hwidth : ∀ i j, small i j=false → 2≤B i j) :
    PositiveSlice (softMarginal small B r c L a) m R ∧
      RemovalSlice (softMarginal small B r c L a) m R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => small a.1 a.2))).symm
  let N := fun k => B (e k).val.1 (e k).val.2
  rw [softMarginal_eq_eliminate small B r c L a e]
  exact NestedReindex.physical_soft_marginal_slices (widths N) m R
    (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e N)
    cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope a ha
    (widths_lower N (fun k => hwidth _ _ (e k).property))

theorem softMarginal_tendsto (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) :
    Filter.Tendsto (fun a : ℝ => softMarginal small B r c L a z) Filter.atTop
      (nhds (hardMarginal small B r c L z)) := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => small a.1 a.2))).symm
  simp_rw [softMarginal_eq_eliminate small B r c L _ e,
    hardMarginal_eq_eliminate small B r c L e]
  apply BalancedFamily.eliminate_tendsto
  intro q
  exact softWeight_tendsto cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope _

theorem hardMarginal_removal (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (m : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (R : ℕ)
    (hwidth : ∀ i j, small i j=false → 2≤B i j) :
    RemovalSlice (hardMarginal small B r c L) m R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => small a.1 a.2))).symm
  let N := fun k => B (e k).val.1 (e k).val.2
  rw [hardMarginal_eq_eliminate small B r c L e]
  exact NestedReindex.physical_hard_marginal_removal (widths N) m R
    (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e N)
    cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope
    (widths_lower N (fun k => hwidth _ _ (e k).property))

theorem hardMarginal_reflected (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (m : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (R : ℕ)
    (hwidth : ∀ i j, small i j=false → 2≤B i j) :
    RemovalSlice (fun z => hardMarginal small B r c L (IntegerReflection.reflect m z)) m R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => small a.1 a.2))).symm
  let N := fun k => B (e k).val.1 (e k).val.2
  rw [hardMarginal_eq_eliminate small B r c L e]
  exact NestedReindex.physical_hard_marginal_reflected (widths N) m R
    (physicalCoordinateEquiv (fun a : I×J => small a.1 a.2) e N)
    cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L)) viewSlope
    (smallOffset small B r c) viewSlope
    (widths_lower N (fun k => hwidth _ _ (e k).property))

/-- The exact finite marginal agrees with the original supported padded
completion count, on its actual capacity box. -/
theorem hardMarginal_eq_completionCount (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (hz : ∀ u, z u≤B u.1.val.1 u.1.val.2)
    (hB : ∀ i j, small i j=false →
      (∑ k, (r k-smallRow small (smallView small z false) k+rowLargeCount small k*L))≤B i j) :
    hardMarginal small B r c L z=
      if OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c
      then (Fintype.card (LargeCompletion small
        (fun i => r i-smallRow small (smallView small z false) i+rowLargeCount small i*L)
        (fun j => c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L)):ℝ)
      else 0 := by
  unfold hardMarginal fullHardFamily
  rw [physicalHardSum_eq_supported]
  apply hard_count_eq
  · intro i j hs
    simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,false)
  · intro i j hs
    simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,true)
  · exact hB

@[reducible] noncomputable def paperSmall (r : I → ℕ) (c : J → ℕ) : I → J → Bool :=
  firstPaperSmall r c (dimensionAllowance (I := I) (J := J)^20)

noncomputable def firstMarginal (r : I → ℕ) (c : J → ℕ)
    (z : SmallView (fun a : I×J => paperSmall r c a.1 a.2) → ℕ) : ℝ :=
  firstPaperWeight r c (smallView (paperSmall r c) z false) (smallView (paperSmall r c) z true)

/-- This specializes the finite-count identification to the manuscript's
exact d, d^12 padding, d^20 small capacity and C=N+dL+U+2. -/
theorem firstMarginal_eq_hard (r : I → ℕ) (c : J → ℕ)
    (z : SmallView (fun a : I×J => paperSmall r c a.1 a.2) → ℕ)
    (hz : ∀ u, z u≤dimensionAllowance (I := I) (J := J)^20) :
    firstMarginal r c z=hardMarginal (paperSmall r c)
      (paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
        (dimensionAllowance (I := I) (J := J)^12) (dimensionAllowance (I := I) (J := J)^20))
      r c (dimensionAllowance (I := I) (J := J)^12) z := by
  have hx : ∀ i j, paperSmall r c i j=true →
      smallView (paperSmall r c) z false i j≤dimensionAllowance (I := I) (J := J)^20 := by
    intro i j hs
    simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,false)
  have hy : ∀ i j, paperSmall r c i j=true →
      smallView (paperSmall r c) z true i j≤dimensionAllowance (I := I) (J := J)^20 := by
    intro i j hs
    simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,true)
  unfold firstMarginal
  rw [← firstPaperHardSum_eq_weight r c _ _ hx hy]
  unfold firstPaperHardSum hardMarginal fullHardFamily
  exact (physicalHardSum_eq_supported (paperSmall r c)
    (paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
      (dimensionAllowance (I := I) (J := J)^12) (dimensionAllowance (I := I) (J := J)^20))
    z r c (dimensionAllowance (I := I) (J := J)^12)).symm

/-- The original supported completion weight inherits its hard-limit raw
signature. It is allowed to vanish; no hard degree positivity is claimed. -/
theorem firstMarginal_removal (r : I → ℕ) (c : J → ℕ) (R : ℕ) :
    RemovalSlice (firstMarginal r c)
      (fun _ => dimensionAllowance (I := I) (J := J)^20) R := by
  let d := dimensionAllowance (I := I) (J := J)
  let small := paperSmall r c
  let B := paperCapacity small r d (d^12) (d^20)
  have hw : ∀ i j, small i j=false → 2≤B i j := by
    intro i j hs
    simp only [B,paperCapacity,hs,Bool.false_eq_true,ite_false]
    omega
  have hs := hardMarginal_removal small B r c (d^12) (fun _ => d^20) R hw
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (fun _ => d^20) z hz (firstMarginal_eq_hard r c)]
  exact hs z hz ht

theorem firstMarginal_reflected (r : I → ℕ) (c : J → ℕ) (R : ℕ) :
    RemovalSlice (fun z => firstMarginal r c
      (IntegerReflection.reflect (fun _ => dimensionAllowance (I := I) (J := J)^20) z))
      (fun _ => dimensionAllowance (I := I) (J := J)^20) R := by
  let d := dimensionAllowance (I := I) (J := J)
  let small := paperSmall r c
  let B := paperCapacity small r d (d^12) (d^20)
  have hw : ∀ i j, small i j=false → 2≤B i j := by
    intro i j hs
    simp only [B,paperCapacity,hs,Bool.false_eq_true,ite_false]
    omega
  have hs := hardMarginal_reflected small B r c (d^12) (fun _ => d^20) R hw
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (fun _ => d^20) z hz (by
    intro x _
    apply firstMarginal_eq_hard r c
    intro u
    exact Nat.sub_le _ _)]
  exact hs z hz ht

end ContingencyTables.FirstPaperPhysicalMarginal

end OAI
