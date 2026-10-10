import OAI.Combinatorics.ContingencyTables.Dense.DenseNormalizer

namespace OAI

/-! # Wholly feasible bins covering the inner polytope -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

def closedBinSet (a : Grid (I := Fin q) K) : Set (Fin q → ℝ) :=
  Set.Icc (realCorner a) (fun j => realCorner a j + 1)

theorem mem_closedBinSet (a : Grid (I := Fin q) K) (x : Fin q → ℝ) :
    x ∈ closedBinSet a ↔ ClosedBin (corner a) x := by
  constructor
  · intro hx j
    exact ⟨hx.1 j, hx.2 j⟩
  · intro hx
    exact ⟨fun j => (hx j).1, fun j => (hx j).2⟩

theorem closedBinSet_volume (a : Grid (I := Fin q) K) : volume (closedBinSet a) = 1 := by
  rw [closedBinSet, Real.volume_Icc_pi]
  simp only [add_sub_cancel_left, ENNReal.ofReal_one, Finset.prod_const_one]

def goodBin (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : Prop :=
  ∀ x, ClosedBin (corner a) x → denseGridFeasible R P d e x

def goodBins (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : Finset (Grid (I := Fin q) K) :=
  Finset.univ.filter (goodBin R P d e)

def denseGridInner (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : Set (Fin q → ℝ) :=
  {x | (fun p => x (e p)) ∈ DenseAffine.normalizedRegion R P d (2 * (d : ℝ) / (d : ℝ) ^ 8)}

theorem inner_bin_good (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) K) (x : Fin q → ℝ)
    (hx : x ∈ denseGridInner R P d e) (hbin : ClosedBin (corner a) x) :
    goodBin R P d e a := by
  intro y hy
  have hdist (p : I × J) : |y (e p) - x (e p)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hy (e p)).1, (hy (e p)).2, (hbin (e p)).1, (hbin (e p)).2]
  have hzero : (fun p => y (e p)) ∈ DenseAffine.normalizedRegion R P d 0 := by
    intro g
    have hb := DenseAffine.normalizedEntry_change R P d hd hR hP hRmax hPmax hfree
      (fun p => y (e p)) (fun p => x (e p)) 1 (by norm_num) hdist g
    have hs := hx g
    have heq : 2 * (d : ℝ) / (d : ℝ) ^ 8 = 2 * ((d : ℝ) / (d : ℝ) ^ 8) := by ring
    rw [heq] at hs
    have hl := (abs_le.mp hb).1
    have hnonneg : (0 : ℝ) ≤ (d : ℝ) / (d : ℝ) ^ 8 := by positivity
    linarith
  rw [DenseAffine.normalizedRegion_zero R P d hd hR hP] at hzero
  exact hzero

theorem goodBin_weight_one (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) K) (ha : goodBin R P d e a) : denseBinWeight R P d e a = 1 := by
  have hx : ClosedBin (corner a) (realCorner a) := fun _ => ⟨le_rfl, by dsimp [realCorner]; linarith⟩
  exact denseBinWeight_eq_one R P d hd hR hP hRmax hPmax hfree e a (realCorner a) hx (ha _ hx)

theorem dense_inner_covered_by_good_bins (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    denseGridInner R P d e ⊆
      ⋃ a ∈ goodBins R P d e (K := 4 * d ^ 8), closedBinSet a := by
  intro x hx
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hxzero : (fun p => x (e p)) ∈ DenseAffine.normalizedRegion R P d 0 :=
    fun g => (show (0 : ℝ) ≤ 2 * (d : ℝ) / (d : ℝ) ^ 8 by positivity).trans (hx g)
  rw [DenseAffine.normalizedRegion_zero R P d hd hR hP] at hxzero
  have hcube := DenseAffine.feasible_in_cube R P d hd hR hP htotal _ hxzero
  have hcoords (j : Fin q) : 0 ≤ x j ∧ x j < (4 * d ^ 8 : ℕ) := by
    have hj := hcube (e.symm j)
    simp only [Equiv.apply_symm_apply] at hj
    constructor
    · exact hj.1
    · push_cast
      have hb : (0 : ℝ) < (d : ℝ) ^ 8 := pow_pos hd₀ _
      linarith [hj.2]
  have hfloor (j : Fin q) : ⌊x j⌋ ∈ Set.Icc (0 : ℤ) ((4 * d ^ 8 : ℕ) - 1) := by
    refine ⟨Int.floor_nonneg.mpr (hcoords j).1, ?_⟩
    have hlt : ⌊x j⌋ < (4 * d ^ 8 : ℕ) := Int.floor_lt.mpr (by exact_mod_cast (hcoords j).2)
    omega
  let a : Grid (I := Fin q) (4 * d ^ 8) := fun j => ⟨⌊x j⌋, hfloor j⟩
  have hclosed : ClosedBin (corner a) x := fun j => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  have hgood := inner_bin_good R P d hd hR hP hRmax hPmax hfree e a x hx hclosed
  refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨?_, (mem_closedBinSet a x).mpr hclosed⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩

theorem goodBins_volume_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    (1 / 2 : ℝ≥0∞) * volume {x | denseGridFeasible R P d e x} ≤
      (goodBins R P d e (K := 4 * d ^ 8)).card := by
  have hinner : (1 / 2 : ℝ≥0∞) * volume {x | denseGridFeasible R P d e x} ≤
      volume (denseGridInner R P d e) := by
    rw [denseGridInner, volume_dense_reindex, denseGridFeasible_volume]
    exact DenseAffine.dense_inner_volume R P d hd hR hP hdimR hdimP hfree htotal
  calc
    _ ≤ volume (denseGridInner R P d e) := hinner
    _ ≤ volume (⋃ a ∈ goodBins R P d e (K := 4 * d ^ 8), closedBinSet a) :=
      measure_mono (dense_inner_covered_by_good_bins R P d hd hR hP hRmax hPmax hfree htotal e)
    _ ≤ ∑ a ∈ goodBins R P d e (K := 4 * d ^ 8), volume (closedBinSet a) :=
      measure_biUnion_finset_le _ _
    _ = _ := by simp only [closedBinSet_volume, Finset.sum_const, nsmul_eq_mul, mul_one]

end

end ContingencyTables.GridBoundary

end OAI
