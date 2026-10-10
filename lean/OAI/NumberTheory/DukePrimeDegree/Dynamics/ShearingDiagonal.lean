import OAI.NumberTheory.DukePrimeDegree.Geometry.DiagonalTwoTargets
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingAnnulus

namespace OAI

/-!
# The two-coordinate shearing diagonal

In the row-lattice convention the weights are `-1` at the root's row,
`+1` at its column, and zero elsewhere. Backward right translation
contracts root time by `exp (-2*t)`. The corresponding relative return
matrix has a fixed diagonal difference, quadratic coefficient growing
by `exp (2*t)`, and other shearing coefficients growing by `exp t`.
These are the rates in EKL (2006), Lemma 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def rootPairWeights {n : ℕ} (i j : Fin n) (k : Fin n) : ℝ :=
  (if k = j then 1 else 0) - (if k = i then 1 else 0)

lemma rootPairWeights_sum {n : ℕ} (i j : Fin n) : ∑ k, rootPairWeights i j k = 0 := by
  simp [rootPairWeights, Finset.sum_sub_distrib]

lemma rootPairWeights_row {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootPairWeights i j i = -1 := by simp [rootPairWeights, hij]

lemma rootPairWeights_col {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootPairWeights i j j = 1 := by simp [rootPairWeights, hij.symm]

lemma rootPairWeights_other {n : ℕ} {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    rootPairWeights i j k = 0 := by simp [rootPairWeights, hki, hkj]

def rootPairFlow {n : ℕ} (i j : Fin n) (t : ℝ) : G n :=
  diagonalOneParameter (rootPairWeights i j) (rootPairWeights_sum i j) t

def rootPairConjugate {n : ℕ} (i j : Fin n) (t : ℝ) (g : G n) : G n :=
  rootPairFlow i j t * g * rootPairFlow i j (-t)

lemma rootPairConjugate_diagonal {n : ℕ} (i j r : Fin n) (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val r r = g.val r r := by
  simp [rootPairConjugate, rootPairFlow, conjugation_entry]

lemma rootPairConjugate_quadratic {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val j i = Real.exp (2 * t) * g.val j i := by
  simp only [rootPairConjugate, rootPairFlow, conjugation_entry,
    rootPairWeights_row hij, rootPairWeights_col hij]
  norm_num

lemma rootPairConjugate_row {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val j k = Real.exp t * g.val j k := by
  simp [rootPairConjugate, rootPairFlow, conjugation_entry,
    rootPairWeights_col hij, rootPairWeights_other hki hkj]

lemma rootPairConjugate_col {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val k i = Real.exp t * g.val k i := by
  simp [rootPairConjugate, rootPairFlow, conjugation_entry,
    rootPairWeights_row hij, rootPairWeights_other hki hkj]

theorem rootPairFlow_contracts_root {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (t u : ℝ) :
    rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij u))
      (rootPairFlow i j (-t)) =
    rightAction (rightAction x (rootPairFlow i j (-t)))
      (Matrix.SpecialLinearGroup.transvection hij (Real.exp (-2 * t) * u)) := by
  have h := root_pair_diagonal_translate hij (rootPairWeights i j)
    (rootPairWeights_sum i j) x u (-t)
  simpa only [rootPairFlow, rootPairWeights_row hij, rootPairWeights_col hij,
    show ((1 : ℝ) - -1) * -t = -2 * t by ring] using h

theorem rootPairFlow_preserving
    (d : ℕ) (i j : Fin (d + 1)) (t : ℝ) (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    MeasurePreserving (fun x => rightAction x (rootPairFlow i j t)) μ μ := by
  refine ⟨(continuous_rightAction _).measurable, ?_⟩
  rw [rootPairFlow, diagonalOneParameter_eq_diagonalFlow]
  exact hA _

theorem exists_rootPairFlow_return_good_set
    (d : ℕ) (i j : Fin (d + 1)) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (E : Set (X (d + 1))) (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set (X (d + 1)), MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | rightAction x (rootPairFlow i j (-t)) ∈ E}) ≤ c * T := by
  let Φ : ℝ → X (d + 1) → X (d + 1) := fun t x => rightAction x (rootPairFlow i j (-t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) := by
    have hD : Continuous (fun p : X (d + 1) × ℝ => rootPairFlow i j (-p.2)) :=
      (continuous_diagonalOneParameter (rootPairWeights i j) (rootPairWeights_sum i j)).comp
        continuous_snd.neg
    exact (continuous_rightAction_uncurry (d + 1)).comp (continuous_fst.prodMk hD)
  have hzero (x : X (d + 1)) : Φ 0 x = x := by
    simp [Φ, rootPairFlow, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ, rootPairFlow]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  exact exists_flow_return_good_set μ hcont.measurable hzero hadd
    (fun t => rootPairFlow_preserving d i j (-t) μ hA) hE c hc

end DukePrimeDegree

end

end OAI
