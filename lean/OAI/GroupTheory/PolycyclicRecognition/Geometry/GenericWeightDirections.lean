import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

namespace OAI

/-! # Generic directions for a finite weight arrangement -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

def genericWeightDirections (α : I → W →L[ℝ] ℝ) : Set W :=
  {w | ∀ i, α i w ≠ 0}

/-- Every nonzero weight cuts out a closed hyperplane with empty interior;
the finitely many hyperplanes can be avoided in every open set. -/
theorem dense_genericWeightDirections (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) : Dense (genericWeightDirections α) := by
  have hd (i : I) : Dense {w : W | α i w ≠ 0} := by
    have hproper : (α i).ker ≠ ⊤ := by
      intro h
      apply hα i
      ext w
      have hw : w ∈ (α i).ker := h ▸ Submodule.mem_top
      exact hw
    have hi : interior ((α i).ker : Set W) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro h
      exact hproper ((α i).ker.eq_top_of_nonempty_interior' h)
    exact interior_eq_empty_iff_dense_compl.mp hi
  have ho (i : I) : IsOpen {w : W | α i w ≠ 0} :=
    (isClosed_eq (α i).continuous continuous_const).isOpen_compl
  have h := dense_iInter_of_isOpen ho hd
  simpa only [genericWeightDirections, Set.iInter_ofPred] using h

/-- A prescribed side of any one weight contains generic directions. -/
theorem exists_generic_weight_positive (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (i : I) :
    ∃ w ∈ genericWeightDirections α, 0 < α i w := by
  have hex : ∃ w, α i w ≠ 0 := by
    by_contra! h
    exact hα i (by ext w; exact h w)
  obtain ⟨v, hv⟩ := hex
  have hne : ({w : W | 0 < α i w} : Set W).Nonempty := by
    rcases lt_or_gt_of_ne hv with hn | hp
    · refine ⟨-v, ?_⟩
      change 0 < α i (-v)
      simpa only [map_neg] using neg_pos.mpr hn
    · exact ⟨v, hp⟩
  exact (dense_genericWeightDirections α hα).exists_mem_open
    (isOpen_lt continuous_const (α i).continuous) hne

theorem exists_generic_weight_negative (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (i : I) :
    ∃ w ∈ genericWeightDirections α, α i w < 0 := by
  obtain ⟨v, hv, hi⟩ := exists_generic_weight_positive α hα i
  exact ⟨-v, fun j => by simpa only [map_neg, neg_ne_zero] using hv j,
    by simpa only [map_neg] using neg_neg_of_pos hi⟩

end PolycyclicRecognition

end

end OAI
