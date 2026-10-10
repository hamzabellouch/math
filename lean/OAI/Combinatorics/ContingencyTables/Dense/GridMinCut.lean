import OAI.Combinatorics.ContingencyTables.Dense.GridConductance
import OAI.Combinatorics.ContingencyTables.Dense.GridPartition
import OAI.Combinatorics.ContingencyTables.Dense.DenseGrid
import OAI.Combinatorics.ContingencyTables.Dense.DenseCutParameters

namespace OAI

/-!
# Every nontrivial cut of the actual dense grid

Choosing the smaller continuous side and then comparing its own discrete
mass gives a lower bound using the smaller discrete side. No assumption
identifying those two choices is made.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

variable {q K : ℕ}

def cutComplementEquiv (Q : (Fin q → ℤ) → Prop) :
    CutEdge K Q ≃ CutEdge K (fun a => ¬ Q a) where
  toFun e := ⟨e.val, e.property.1, not_congr e.property.2⟩
  invFun e := ⟨e.val, e.property.1, by simpa only [not_not] using not_congr e.property.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

theorem cut_complement_sum (Q : (Fin q → ℤ) → Prop) (w : Grid (I := Fin q) K → ℝ) :
    (∑ e : CutEdge K Q, min (w e.val.1) (w e.val.2.1)) =
      ∑ e : CutEdge K (fun a => ¬ Q a), min (w e.val.1) (w e.val.2.1) := by
  exact Fintype.sum_equiv (cutComplementEquiv Q) _ _ (fun _ => rfl)

theorem weighted_min_cut (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (Q : (Fin q → ℤ) → Prop) (t : ℝ) (ht : 0 < t) (ht₁ : t < 1)
    (hr : t * K ≤ 1 / 4) (hsize : (q - 1 : ℕ) * (2 * (t * K)) ≤ (1 / 2 : ℝ))
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 < w a) (hρ : ContinuousOn ρ (ambientBox q K))
    (hpos : ∀ x ∈ ambientBox q K, 0 < ρ x)
    (hlc : PublishedInputs.LogConcaveOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x)
    (htube : ∀ (edge : CutEdge K Q) x,
      x ∈ edgeTube edge (t * K) ∩ {x | Cube K x} →
        ρ x ≤ 4 * min (w edge.val.1) (w edge.val.2.1))
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun a => ¬ Q a))) :
    (((2 : ℝ) ^ t - 1) / 16) *
        min (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun b => ¬ Q b), w a.val) ≤
      ∑ edge : CutEdge K Q, min (w edge.val.1) (w edge.val.2.1) := by
  have hi : IntegrableOn ρ (ambientBox q K) := hρ.integrableOn_Icc
  have hsum := selected_complement_integral Q ρ hi
  have hc : 0 ≤ ((2 : ℝ) ^ t - 1) / 16 := by
    have hg := two_rpow_gain t ht.le
    exact div_nonneg ((show (0 : ℝ) ≤ t / 2 by positivity).trans hg) (by norm_num)
  by_cases hcut : 2 * (∫ x in selectedBins K Q, ρ x) ≤ ∫ x in {x | Cube K x}, ρ x
  · calc
      _ ≤ (((2 : ℝ) ^ t - 1) / 16) * (∑ a : Selected K Q, w a.val) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hc
      _ ≤ _ := weighted_cut_of_interpolation hPL Q t ht ht₁ hr hsize ρ w
        (fun a => (hw a).le) hρ hpos hlc hbin htube
        (selected_mass_positive Q ρ w hw hi hbin hne) hcut
  · have hcut' : 2 * (∫ x in selectedBins K (fun a => ¬ Q a), ρ x) ≤
        ∫ x in {x | Cube K x}, ρ x := by linarith
    have htube' (edge : CutEdge K (fun a => ¬ Q a)) (x : Fin q → ℝ)
        (hx : x ∈ edgeTube edge (t * K) ∩ {x | Cube K x}) :
        ρ x ≤ 4 * min (w edge.val.1) (w edge.val.2.1) :=
      htube ((cutComplementEquiv Q).symm edge) x hx
    calc
      _ ≤ (((2 : ℝ) ^ t - 1) / 16) * (∑ a : Selected K (fun b => ¬ Q b), w a.val) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hc
      _ ≤ ∑ edge : CutEdge K (fun a => ¬ Q a), min (w edge.val.1) (w edge.val.2.1) :=
        weighted_cut_of_interpolation hPL (fun a => ¬ Q a) t ht ht₁ hr hsize ρ w
          (fun a => (hw a).le) hρ hpos hlc hbin htube'
          (selected_mass_positive (fun a => ¬ Q a) ρ w hw hi hbin hne') hcut'
      _ = _ := (cut_complement_sum Q w).symm

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The actual dense sampler's dyadic weights satisfy every nontrivial
cut bound, with the manuscript interpolation parameter. -/
theorem denseGrid_min_cut (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q) (hK : 1 ≤ K)
    (Q : (Fin q → ℤ) → Prop)
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun a => ¬ Q a))) :
    (1 / (128 * (d : ℝ) * K)) * min
        (∑ a : Selected K Q, DenseWeights.binWeight ((d : ℝ) ^ 4)
          (denseGridPenalty R P d e) (realCorner a.val))
        (∑ a : Selected K (fun b => ¬ Q b), DenseWeights.binWeight ((d : ℝ) ^ 4)
          (denseGridPenalty R P d e) (realCorner a.val)) ≤
      ∑ edge : CutEdge K Q, min
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.1))
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.2.1)) := by
  let p := denseGridPenalty R P d e
  let w := fun a : Grid (I := Fin q) K => DenseWeights.binWeight ((d : ℝ) ^ 4) p (realCorner a)
  let ρ := DenseWeights.density ((d : ℝ) ^ 4) p
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  obtain ⟨ht, ht₁, hr, hsize⟩ := denseInterpolation_bounds d K q hd hK hq
  have hbound := weighted_min_cut hPL Q (denseInterpolation d K) ht ht₁ hr hsize ρ w
    (fun a => DenseWeights.binWeight_pos _ _ _)
    ((DenseWeights.density_continuous _ _ (denseGridPenalty_continuous R P d e)).continuousOn)
    (fun x _ => DenseWeights.density_pos _ _ _) (fun x _ y _ t ht ht₁ =>
      DenseWeights.density_logConcave _ (by positivity) _ Set.univ
        (denseGridPenalty_convex R P d e) x (Set.mem_univ _) y (Set.mem_univ _) t ht ht₁)
    (fun a x hx => (denseGrid_bin_comparison R P d hd hR hP hRmax hPmax hfree e a x
      (fun j => ⟨(hx j).1.le, (hx j).2.le⟩)).1)
    (fun edge x hx => denseGrid_tube_comparison R P d hd hR hP hRmax hPmax hfree e edge
      (denseInterpolation d K * K) (mul_nonneg ht.le (Nat.cast_nonneg _)) (by linarith) x hx.1)
    hne hne'
  have hs : 0 ≤ min (∑ a : Selected K Q, w a.val)
      (∑ a : Selected K (fun b => ¬ Q b), w a.val) := by
    apply le_min <;> exact Finset.sum_nonneg (fun a _ => (DenseWeights.binWeight_pos _ _ _).le)
  have hgain := two_rpow_gain (denseInterpolation d K) ht.le
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hK₀ : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  calc
    _ = (denseInterpolation d K / 32) * min
        (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun b => ¬ Q b), w a.val) := by
      unfold denseInterpolation
      congr 1
      field_simp [hd₀, hK₀]
      norm_num
    _ ≤ (((2 : ℝ) ^ denseInterpolation d K - 1) / 16) * min
        (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun b => ¬ Q b), w a.val) :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    _ ≤ _ := hbound

end

end ContingencyTables.GridBoundary

end OAI
