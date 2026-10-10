import OAI.Combinatorics.ContingencyTables.Dense.DenseRegionVolume
import OAI.Combinatorics.ContingencyTables.Dense.DensityLayers
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Volume-preserving free-coordinate indexing for the dense sampler -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseGridFeasible (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (x : Fin q → ℝ) : Prop :=
  DenseAffine.Feasible R P d (fun p => x (e p))

omit [DecidableEq I] [DecidableEq J] in
theorem volume_dense_reindex (e : I × J ≃ Fin q) (S : Set (I × J → ℝ)) :
    volume {x : Fin q → ℝ | (fun p => x (e p)) ∈ S} = volume S := by
  have hm : (MeasurableEquiv.piCongrLeft (fun _ : I × J => ℝ) e.symm :
      (Fin q → ℝ) → (I × J → ℝ)) = (fun x p => x (e p)) := by
    ext x p
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I × J => ℝ) e.symm x (e p)
    simpa only [Equiv.symm_apply_apply] using h
  have h := (volume_measurePreserving_piCongrLeft (fun _ : I × J => ℝ) e.symm).measure_preimage_equiv S
  rw [hm] at h
  exact h

omit [DecidableEq I] [DecidableEq J] in
theorem denseGridFeasible_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) :
    volume {x | denseGridFeasible R P d e x} =
      volume {x : I × J → ℝ | DenseAffine.Feasible R P d x} := by
  exact volume_dense_reindex e {x | DenseAffine.Feasible R P d x}

theorem denseGrid_layer_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (j : ℕ) :
    volume (DenseWeights.layerSet ((d : ℝ) ^ 4) (denseGridPenalty R P d e) j) ≤
      ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 *
        ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))) *
      volume {x | denseGridFeasible R P d e x} := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hset : DenseWeights.layerSet ((d : ℝ) ^ 4) (denseGridPenalty R P d e) j =
      {x | denseGridPenalty R P d e x ≤ ((j : ℝ) + 1) / (d : ℝ) ^ 4} := by
    ext x
    change (d : ℝ) ^ 4 * denseGridPenalty R P d e x ≤ (j : ℝ) + 1 ↔
      denseGridPenalty R P d e x ≤ ((j : ℝ) + 1) / (d : ℝ) ^ 4
    rw [le_div_iff₀ (pow_pos hd₀ 4), mul_comm]
  rw [hset, denseGridFeasible_volume]
  have hv := volume_dense_reindex e {x | DenseAffine.densePenalty R P d x ≤
    ((j : ℝ) + 1) / (d : ℝ) ^ 4}
  change volume {x | denseGridPenalty R P d e x ≤ ((j : ℝ) + 1) / (d : ℝ) ^ 4} = _ at hv
  rw [hv]
  exact DenseAffine.dense_sublevel_volume R P d hd hR hP hdimR hdimP hfree htotal _ (by positivity)

end

end ContingencyTables.GridBoundary

end OAI
