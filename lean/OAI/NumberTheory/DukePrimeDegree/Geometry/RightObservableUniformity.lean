import OAI.NumberTheory.DukePrimeDegree.Dynamics.CompactFamilyGeneric
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockShell

namespace OAI

/-!
# Uniform observables near a compact family of right translations

The tolerance is selected before the eventual shearing limit. Matrix
entry control then bounds a compact observable at every base point,
including points outside compact subsets of the lattice space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

def rightCompactObservable {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ) (g : G n) : X n →ᵇ ℝ :=
  f.toBoundedContinuousFunction.compContinuous ⟨fun x => rightAction x g, continuous_rightAction g⟩

section OppositeAction

local instance rightLatticeOppositeAction (n : ℕ) : MulAction (G n)ᵐᵒᵖ (X n) where
  smul g x := rightAction x g.unop
  one_smul x := rightAction_one x
  mul_smul g h x := by
    change rightAction x (h.unop * g.unop) =
      rightAction (rightAction x h.unop) g.unop
    exact (rightAction_mul x h.unop g.unop).symm

local instance rightLatticeOppositeAction_continuous (n : ℕ) :
    ContinuousSMul (G n)ᵐᵒᵖ (X n) where
  continuous_smul := (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk (MulOpposite.continuous_unop.comp continuous_fst))

lemma continuous_rightCompactObservable {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ) :
    Continuous (rightCompactObservable f) := by
  exact (continuous_compactObservableTranslate (H := (G n)ᵐᵒᵖ) f).comp MulOpposite.continuous_op

end OppositeAction

/-- A single matrix tolerance works around the whole compact set and
for every lattice base point. -/
theorem exists_uniform_right_observable_tolerance {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ)
    (K : Set (G n)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g h : G n, h ∈ K → slMatrixDifference g h < δ →
      ∀ x : X n, |f (rightAction x g) - f (rightAction x h)| < ε := by
  let : MetricSpace (G n) := MetricSpace.induced
    (fun g : G n => g.val) Subtype.val_injective inferInstance
  have hu := hK.uniformContinuousAt_of_continuousAt (rightCompactObservable f)
    (fun _ _ => (continuous_rightCompactObservable f).continuousAt)
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ, hδ, ?_⟩
  intro g h hh hgh x
  have hdist : dist h g < δ := by
    change dist h.val g.val < δ
    rw [dist_eq_norm]
    apply (Matrix.norm_lt_iff hδ).mpr
    intro i j
    change |h.val i j - g.val i j| < δ
    rw [abs_sub_comm]
    exact (entry_sub_le_slMatrixDifference g h i j).trans_lt hgh
  have ht : dist (rightCompactObservable f h) (rightCompactObservable f g) < ε :=
    hclose hdist hh
  have hp := (BoundedContinuousFunction.dist_coe_le_dist
    (f := rightCompactObservable f h) (g := rightCompactObservable f g) x).trans_lt ht
  simpa only [rightCompactObservable, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    Real.dist_eq, abs_sub_comm] using hp

/-- Finitely many separating tests share one tolerance, with no choice
of a limiting shear involved. -/
theorem exists_finite_uniform_right_observable_tolerance {n : ℕ}
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ g h : G n, h ∈ K →
      slMatrixDifference g h < δ →
        ∀ x : X n, |f (rightAction x g) - f (rightAction x h)| < ε := by
  classical
  choose δ hδ hsmall using fun f : F =>
    exists_uniform_right_observable_tolerance f.val K hK ε hε
  by_cases hF : F.Nonempty
  · obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image F
      (fun f => if h : f ∈ F then δ ⟨f, h⟩ else 1) hF
    refine ⟨δ ⟨f, hf⟩, hδ ⟨f, hf⟩, ?_⟩
    intro q hq g h hh hgh x
    apply hsmall ⟨q, hq⟩ g h hh _ x
    apply hgh.trans_le
    simpa only [dite_eq_left hf, dite_eq_left hq] using hmin q hq
  · refine ⟨1, zero_lt_one, ?_⟩
    intro f hf
    exact (hF ⟨f, hf⟩).elim

end DukePrimeDegree

end

end OAI
