import OAI.Analysis.LipschitzHilbert.Estimates.ShiftedBlocks
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockLineGrid
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedIntegral
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! The source line windows grow along the angular path. Reading those
windows in reverse gives increasing levels in one finite line grid. Only
the factors are reordered: the stopping budget retains its forward mass
path, including the possibility of a zero terminal mass. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

def reverseLevel (σ : Fin K) (count k : ℕ) : ℕ :=
  endpoint σ count - endpoint σ (count-k)

def reverseIndex (count j : ℕ) : ℕ := count-1-j

@[simp] theorem reverseLevel_zero (σ : Fin K) (count : ℕ) :
    reverseLevel σ count 0 = 0 := by
  simp [reverseLevel]

@[simp] theorem reverseLevel_last (σ : Fin K) (count : ℕ) :
    reverseLevel σ count count = endpoint σ count := by
  simp [reverseLevel]

theorem reverseLevel_le (σ : Fin K) (count k : ℕ) :
    reverseLevel σ count k ≤ endpoint σ count := Nat.sub_le _ _

theorem reverseLevel_monotone (hK : 0 < K) (σ : Fin K) (count : ℕ) :
    Monotone (reverseLevel σ count) := by
  intro a b hab
  exact Nat.sub_le_sub_left ((endpoint_strictMono hK σ).monotone
    (Nat.sub_le_sub_left hab count)) _

theorem reverseLevel_step_lt (hK : 0 < K) (σ : Fin K) {count k : ℕ}
    (hk : k < count) : reverseLevel σ count k < reverseLevel σ count (k+1) := by
  have he := endpoint_strictMono hK σ (show count-(k+1) < count-k by omega)
  have hb := (endpoint_strictMono hK σ).monotone (Nat.sub_le count k)
  unfold reverseLevel
  omega

theorem reverseIndex_lt {count j : ℕ} (hj : j < count) :
    reverseIndex count j < count := by
  unfold reverseIndex
  omega

theorem reverseIndex_involutive {count j : ℕ} (hj : j < count) :
    reverseIndex count (reverseIndex count j) = j := by
  unfold reverseIndex
  omega

theorem reverseLevel_block_start (σ : Fin K) {count j : ℕ} (hj : j < count) :
    reverseLevel σ count (reverseIndex count j) =
      endpoint σ count-endpoint σ (j+1) := by
  unfold reverseLevel reverseIndex
  congr 2
  omega

theorem reverseLevel_block_end (σ : Fin K) {count j : ℕ} (hj : j < count) :
    reverseLevel σ count (reverseIndex count j+1) =
      endpoint σ count-endpoint σ j := by
  unfold reverseLevel reverseIndex
  congr 2
  omega

theorem reverseLevel_block_length (hK : 0 < K) (σ : Fin K) {count j : ℕ}
    (hj : j < count) :
    reverseLevel σ count (reverseIndex count j+1)-
        reverseLevel σ count (reverseIndex count j) =
      endpoint σ (j+1)-endpoint σ j := by
  rw [reverseLevel_block_start σ hj,reverseLevel_block_end σ hj]
  have h1 := (endpoint_strictMono hK σ).monotone (show j+1 ≤ count by omega)
  have h2 := (endpoint_strictMono hK σ).monotone (Nat.le_succ j)
  omega

theorem sum_reverseIndex {M : Type*} [AddCommMonoid M] (f : ℕ → M) (count : ℕ) :
    (∑ j ∈ Finset.range count, f (reverseIndex count j)) =
      ∑ j ∈ Finset.range count, f j :=
  Finset.sum_range_reflect f count

theorem prod_reverseIndex {M : Type*} [CommMonoid M] (f : ℕ → M) (count : ℕ) :
    (∏ j ∈ Finset.range count, f (reverseIndex count j)) =
      ∏ j ∈ Finset.range count, f j :=
  Finset.prod_range_reflect f count

end LipschitzHilbert.ShiftedBlocks

namespace LipschitzHilbert

/-- A single root line grid contains every source block window, in reverse
angular order. Its depth includes the shorter initial source block exactly. -/
def sourceReverseLineGrid {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (count : ℕ) : FiniteLineGrid :=
  sourceLineGrid L origin (sourceLineScale g L w (ShiftedBlocks.endpoint σ count))
    (ShiftedBlocks.endpoint σ count)
    (sourceLineScale_pos g L hw (ShiftedBlocks.endpoint σ count))

theorem sourceReverseLineGrid_levels {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) (count : ℕ) :
    (∀ k ≤ count, ShiftedBlocks.reverseLevel σ count k ≤
      (sourceReverseLineGrid g L origin hw σ count).depth) ∧
    (∀ k < count, ShiftedBlocks.reverseLevel σ count k ≤
      ShiftedBlocks.reverseLevel σ count (k+1)) := by
  exact ⟨fun k _ => ShiftedBlocks.reverseLevel_le σ count k,
    fun k _ => ShiftedBlocks.reverseLevel_monotone hK σ count (Nat.le_succ k)⟩

theorem source_reverse_line_mesh {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) (count k : ℕ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count k) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (count-k)) := by
  have hle := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.sub_le count k)
  have hm := source_block_line_mesh g L origin hw
    (ShiftedBlocks.endpoint σ (count-k)) (ShiftedBlocks.endpoint σ count) hle hbranch
  simpa only [sourceReverseLineGrid,ShiftedBlocks.reverseLevel,sourceLineGrid_mesh] using hm

/-- The coarse side of original block j is its child window. -/
theorem source_reverse_block_coarse {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) := by
  rw [source_reverse_line_mesh g L origin hw σ hK count _ hbranch]
  congr 2
  unfold ShiftedBlocks.reverseIndex
  omega

/-- Refining that child window across the block gives its parent mesh. -/
theorem source_reverse_block_fine {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ j) := by
  rw [source_reverse_line_mesh g L origin hw σ hK count _ hbranch]
  congr 2
  unfold ShiftedBlocks.reverseIndex
  omega

theorem source_reverse_local_mesh {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    let grid := sourceReverseLineGrid g L origin hw σ count
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    (grid.lineWindow coarse i (fine-coarse)).width =
        sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) ∧
      (grid.lineWindow coarse i (fine-coarse)).meshWidth (fine-coarse) =
        sourceLineScale g L w (ShiftedBlocks.endpoint σ j) := by
  dsimp only
  constructor
  · exact source_reverse_block_coarse g L origin hw σ hK hj hbranch
  · rw [FiniteLineGrid.lineWindow_meshWidth,
      Nat.add_sub_of_le (ShiftedBlocks.reverseLevel_monotone hK σ count (Nat.le_succ _))]
    exact source_reverse_block_fine g L origin hw σ hK hj hbranch

/-- Local prediction factors can be integrated in reverse angular order.
The hypothesis on their errors remains the original forward sum. Thus a
forward stopped-mass estimate can be used without reversing its masses. -/
theorem source_reverse_local_path_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (count : ℕ) (hlevel : ∀ j ≤ count, level j ≤ g.depth)
    (hmono : ∀ j < count, level j ≤ level (j+1))
    (good : Set ℝ) (beta error : ℕ → ℝ → ℝ) (F : ℕ → ℕ → ℝ → ℝ)
    (hF : ∀ j < count, ∀ i < g.branching^level j, ∀ x,
      0 ≤ F (ShiftedBlocks.reverseIndex count j) i x)
    (hint : ∀ j < count, ∀ i < g.branching^level j,
      Integrable (F (ShiftedBlocks.reverseIndex count j) i) (intervalProbability
        (g.lineWindow (level j) i (level (j+1)-level j)).origin
        ((g.lineWindow (level j) i (level (j+1)-level j)).origin+
          (g.lineWindow (level j) i (level (j+1)-level j)).width)))
    (haverage : ∀ j < count, ∀ i < g.branching^level j,
      (∫ x, F (ShiftedBlocks.reverseIndex count j) i x ∂intervalProbability
        (g.lineWindow (level j) i (level (j+1)-level j)).origin
        ((g.lineWindow (level j) i (level (j+1)-level j)).origin+
          (g.lineWindow (level j) i (level (j+1)-level j)).width)) ≤ 1)
    (hconstant : ∀ j < count, ∀ i < g.branching^level j, ∀ x z,
      (g.lineWindow (level j) i (level (j+1)-level j)).index (level (j+1)-level j) x =
        (g.lineWindow (level j) i (level (j+1)-level j)).index (level (j+1)-level j) z →
        F (ShiftedBlocks.reverseIndex count j) i x =
          F (ShiftedBlocks.reverseIndex count j) i z)
    (hcompare : ∀ j < count, ∀ i < g.branching^level j,
      ∀ x ∈ g.cell (level j) i ∩ good,
        beta (ShiftedBlocks.reverseIndex count j) x ≤
          Real.exp (error (ShiftedBlocks.reverseIndex count j) x)*
            F (ShiftedBlocks.reverseIndex count j) i x)
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x)
    (hbudget : ∀ x ∈ g.root ∩ good, (∑ j ∈ Finset.range count, error j x) ≤ E)
    (hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*∏ j ∈ Finset.range count, beta j x)) volume) :
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, beta j x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, beta j x) x) ≤
      Real.exp E*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  have hp (x : ℝ) := ShiftedBlocks.prod_reverseIndex (fun j => beta j x) count
  have hs (x : ℝ) := ShiftedBlocks.sum_reverseIndex (fun j => error j x) count
  have hf' : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*∏ j ∈ Finset.range count,
        beta (ShiftedBlocks.reverseIndex count j) x)) volume := by
    simpa only [hp] using hf
  have hi := source_local_path_integral g T K D y E hK hD hwidth level count hlevel hmono
    good (fun j => beta (ShiftedBlocks.reverseIndex count j))
    (fun j => error (ShiftedBlocks.reverseIndex count j))
    (fun j => F (ShiftedBlocks.reverseIndex count j)) hF hint haverage hconstant hcompare
    (fun x hx j hj => hbeta x hx _ (ShiftedBlocks.reverseIndex_lt hj))
    (fun x hx => by simpa only [hs] using hbudget x hx) hf'
  simpa only [hp] using hi

end LipschitzHilbert

end

end OAI
