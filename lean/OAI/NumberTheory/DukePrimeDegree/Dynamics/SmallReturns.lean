import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallCentralizer

namespace OAI

/-!
# Small quotient returns centralize both roots

For a fixed neutral return parameter, compact sets of possible small
return matrices give measurable sets of returning points. Conjugation in
the contracting direction preserves the single-root centralizer ball;
uniqueness of quotient lifts then identifies returning matrices exactly.
Poincaré recurrence proves the fixed-parameter form of EKL Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def compactReturnSet {n : ℕ} (K : Set (G n)) (b : G n) : Set (X n) :=
  {x | ∃ g ∈ K, rightAction x g = rightAction x b}

lemma isClosed_compactReturnSet {n : ℕ} (K : Set (G n)) (hK : IsCompact K) (b : G n) :
    IsClosed (compactReturnSet K b) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (X n × K) := {p | rightAction p.1 p.2.val = rightAction p.1 b}
  have hS : IsClosed S := isClosed_eq
    ((continuous_rightAction_uncurry n).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    ((continuous_rightAction b).comp continuous_fst)
  have hproj := isClosedMap_fst_of_compactSpace S hS
  convert hproj using 1
  ext x
  simp only [compactReturnSet, mem_ofPred_eq, mem_image, S, Prod.exists, Subtype.exists]
  aesop

/-- A fixed neutral return parameter has, almost everywhere, no small
single-root-centralizing lift outside the opposite-root centralizer. -/
theorem ae_small_rootCentralizer_return_in_pair
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (b : G (d + 1))
    (hcomm : ∀ t : ℝ,
      b * diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t =
        diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t * b)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (U : Set (X (d + 1))) (hU : MeasurableSet U)
    (hinj : ∀ x ∈ U, Set.InjOn (fun g => rightAction x g) (matrixBall (d + 1) R))
    (K : Set (G (d + 1))) (hK : IsCompact K)
    (hKsmall : ∀ g ∈ K, g ∈ matrixClosedBall (d + 1) r ∧
      g * Matrix.SpecialLinearGroup.transvection hij 1 =
        Matrix.SpecialLinearGroup.transvection hij 1 * g) :
    ∀ᵐ x ∂μ, x ∈ U → ∀ g ∈ K, rightAction x g = rightAction x b →
      g ∈ rootPairCentralizer hij := by
  let D := diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j)
  let T : X (d + 1) → X (d + 1) := fun x => rightAction x (D (-1))
  let E := U ∩ compactReturnSet K b
  have hE : MeasurableSet E := hU.inter (isClosed_compactReturnSet K hK b).measurableSet
  let g : X (d + 1) → G (d + 1) := fun x =>
    if hx : x ∈ E then Classical.choose hx.2 else 1
  have hg (x : X (d + 1)) (hx : x ∈ E) :
      g x ∈ K ∧ rightAction x (g x) = rightAction x b := by
    dsimp only [g]
    rw [dite_eq_left hx]
    exact Classical.choose_spec hx.2
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [T, D]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hiter (k : ℕ) (x : X (d + 1)) : T^[k] x = rightAction x (D (-(k : ℝ))) := by
    induction k with
    | zero => simp [D, diagonalOneParameter_zero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp only [T, D]
      rw [rightAction_mul, ← diagonalOneParameter_add]
      congr 2
      push_cast
      ring
  have hbound (x : X (d + 1)) (hx : x ∈ E) (k : ℕ) (hk : T^[k] x ∈ E) :
      ∀ a c, |(D (k : ℝ) * g x * D (-(k : ℝ))).val a c| ≤ r + 1 := by
    let y := T^[k] x
    have hy : y = rightAction x (D (-(k : ℝ))) := hiter k x
    have hgy := hg y hk
    have hbackball : D (-(k : ℝ)) * g y * D (k : ℝ) ∈ matrixClosedBall (d + 1) r :=
      rootCentralizer_conjugate_mem_closedBall hij hr (g y)
        (hKsmall _ hgy.1).1 (hKsmall _ hgy.1).2 (k : ℝ) (Nat.cast_nonneg k)
    have hbackret : rightAction x (D (-(k : ℝ)) * g y * D (k : ℝ)) = rightAction x b := by
      calc
        _ = rightAction (rightAction y (g y)) (D (k : ℝ)) := by
          rw [hy]
          simp only [rightAction_mul, mul_assoc]
        _ = rightAction (rightAction y b) (D (k : ℝ)) := congrArg _ hgy.2
        _ = rightAction x b := by
          rw [hy, rightAction_mul, rightAction_mul, hcomm]
          dsimp only [D]
          rw [← mul_assoc, diagonalOneParameter_neg]
          simp
    have heq : D (-(k : ℝ)) * g y * D (k : ℝ) = g x :=
      hinj x hx.1 (matrixClosedBall_subset_matrixBall hr hrR hbackball)
        (matrixClosedBall_subset_matrixBall hr hrR (hKsmall _ (hg x hx).1).1)
        (hbackret.trans (hg x hx).2.symm)
    have hconj : D (k : ℝ) * g x * D (-(k : ℝ)) = g y := by
      rw [← heq]
      dsimp only [D]
      rw [diagonalOneParameter_neg]
      group
    intro a c
    rw [hconj]
    exact entry_bound_of_mem_matrixClosedBall hr (hKsmall _ hgy.1).1 a c
  have hpair := ae_rootPairCentralizer_of_recurrent_conjugates μ T hT E hE hij
    (rootContractionWeights i j) (rootContractionWeights_sum i j)
    (rootContractionWeights_gap hij) (fun a hai haj => rootContractionWeights_middle hij hai haj)
    g (fun x hx => (hKsmall _ (hg x hx).1).2) (r + 1) hbound
  filter_upwards [hpair] with x hx
  intro hxU z hz hret
  have hxE : x ∈ E := ⟨hxU, z, hz, hret⟩
  have heq : z = g x := hinj x hxU
    (matrixClosedBall_subset_matrixBall hr hrR (hKsmall _ hz).1)
    (matrixClosedBall_subset_matrixBall hr hrR (hKsmall _ (hg x hxE).1).1)
    (hret.trans (hg x hxE).2.symm)
  exact heq ▸ hx hxE

end DukePrimeDegree

end

end OAI
