import OAI.Algebra.DepthFive.FiniteOperator
import OAI.Algebra.DepthFive.ImmFockMatrix
import OAI.Algebra.DepthFive.FockBidegreeBasis
import OAI.Algebra.DepthFive.TraceExpansion
import OAI.Algebra.DepthFive.PathInjectivity

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The number of derivative layers in a layerwise partition. -/
def immLayerVCount {n : ℕ} (side : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun t => side t = true)).card

/-- The number of multiplication layers in a layerwise partition. -/
def immLayerUCount {n : ℕ} (side : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun t => side t = false)).card

/-- Source exponent vectors for the finite IMM operator. -/
abbrev ImmSourceIndex (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :=
  BidegreeIndex (fun x : Fin n × Fin n × Fin n => side x.1) a b

/-- Target exponent vectors for the finite IMM operator. -/
abbrev ImmTargetIndex (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :=
  BidegreeIndex (fun x : Fin n × Fin n × Fin n => side x.1)
    (a - immLayerVCount side) (b + immLayerUCount side)

/-- The actual finite IMM map written in factorial-normalized source and target bases. -/
def immNormalizedMatrix (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :
    Matrix (ImmTargetIndex n side a b) (ImmSourceIndex n side a b) ℂ :=
  LinearMap.toMatrix
    (bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n) (fun x => side x.1) a b)
    (bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n) (fun x => side x.1)
      (a - immLayerVCount side) (b + immLayerUCount side))
    (finiteMixedOperator (K := ℂ) (σ := Fin n × Fin n × Fin n) (fun x => side x.1) a b
      (immLayerVCount side) (immLayerUCount side) (imm ℂ n))

/-- Each finite normalized matrix entry is exactly the weighted sum of its IMM path shifts. -/
theorem immNormalizedMatrix_apply (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (a b : ℕ) (e : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b) :
    immNormalizedMatrix n side a b e d =
      ∑ p : Fin (immPaths n hn).length,
        if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
        then (immPathAmplitude n hn (fun x => side x.1) d.1 p : ℂ) else 0 := by
  classical
  unfold immNormalizedMatrix
  rw [LinearMap.toMatrix_apply, bidegreeComplexFockBasis_repr]
  change (Real.sqrt (multiFactorial e.1 : ℝ) : ℂ) *
    (mixedOperator (fun x => side x.1)
        (bidegreeComponent (fun x => side x.1) (immLayerVCount side) (immLayerUCount side)
          (imm ℂ n))
        ((bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n)
          (fun x => side x.1) a b d) : MvPolynomial (Fin n × Fin n × Fin n) ℂ)).coeff e.1 = _
  rw [bidegreeComplexFockBasis_apply]
  simp only [immLayerVCount, immLayerUCount, bidegreeComponent_imm]
  rw [← complexFockBasis_repr]
  exact complexFockBasis_repr_mixedOperator_imm n hn (fun x => side x.1) d.1 e.1

/-- The finite normalized matrix computes exactly the manuscript's rank measure. -/
theorem immNormalizedMatrix_rank (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :
    (immNormalizedMatrix n side a b).rank =
      bidegreeRank (fun x => side x.1) a b
        (immLayerVCount side) (immLayerUCount side) (imm ℂ n) := by
  rw [immNormalizedMatrix, ← RankMeasure.mapRank_eq_matrixRank, finiteMixedOperator_rank]

/-- The genuine target occupation, with an irrelevant fallback for zero-amplitude paths. -/
def immTargetShift (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    [Nonempty (ImmTargetIndex n side a b)]
    (d : ImmSourceIndex n side a b) (p : Fin (immPaths n hn).length) :
    ImmTargetIndex n side a b := by
  classical
  exact if h : Finsupp.weight (bidegreeWeight (fun x => side x.1))
      (immPathOccupation n hn (fun x => side x.1) d.1 p) =
        (a - immLayerVCount side, b + immLayerUCount side)
    then ⟨_, h⟩ else Classical.choice inferInstance

/-- Nonzero paths never use the arbitrary fallback index. -/
theorem immTargetShift_val_of_amplitude_ne_zero (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) [Nonempty (ImmTargetIndex n side a b)]
    (d : ImmSourceIndex n side a b) (p : Fin (immPaths n hn).length)
    (hp : immPathAmplitude n hn (fun x => side x.1) d.1 p ≠ 0) :
    (immTargetShift n hn side a b d p).1 =
      immPathOccupation n hn (fun x => side x.1) d.1 p := by
  have h := immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p hp
  unfold immTargetShift
  split_ifs with hdegree
  · rfl
  · exact False.elim (hdegree h)

/-- The actual normalized IMM matrix is the finite weighted path-shift matrix. -/
theorem immNormalizedMatrix_eq_pathShiftMatrix (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) [Nonempty (ImmTargetIndex n side a b)] :
    immNormalizedMatrix n side a b =
      pathShiftMatrix (immTargetShift n hn side a b)
        (fun d p => (immPathAmplitude n hn (fun x => side x.1) d.1 p : ℂ)) := by
  classical
  ext e d
  rw [immNormalizedMatrix_apply n hn side a b e d]
  unfold pathShiftMatrix
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ha : immPathAmplitude n hn (fun x => side x.1) d.1 p = 0
  · simp [ha]
  · have hs := immTargetShift_val_of_amplitude_ne_zero n hn side a b d p ha
    have he : immPathOccupation n hn (fun x => side x.1) d.1 p = e.1 ↔
        immTargetShift n hn side a b d p = e := by
      rw [Subtype.ext_iff, hs]
    simp only [he]

/-- Distinct nonzero path contributions cannot reach the same occupation vector. -/
theorem immPathOccupation_injective_of_nonzero (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (d : (Fin n × Fin n × Fin n) →₀ ℕ)
    (p q : Fin (immPaths n hn).length)
    (hp : immPathAmplitude n hn (fun x => side x.1) d p ≠ 0)
    (hq : immPathAmplitude n hn (fun x => side x.1) d q ≠ 0)
    (heq : immPathOccupation n hn (fun x => side x.1) d p =
      immPathOccupation n hn (fun x => side x.1) d q) : p = q := by
  have hsp := signedOccupation_path_of_amplitude_ne_zero (fun x : Fin n × Fin n × Fin n => side x.1)
    ((immPaths n hn).get p) (immPaths_nodup n hn _ (List.get_mem _ p)) d hp
  have hsq := signedOccupation_path_of_amplitude_ne_zero (fun x : Fin n × Fin n × Fin n => side x.1)
    ((immPaths n hn).get q) (immPaths_nodup n hn _ (List.get_mem _ q)) d hq
  have hs := congrArg signedOccupation heq
  change signedOccupation (pathOccupation _ _ _) =
    signedOccupation (pathOccupation _ _ _) at hs
  rw [hsp, hsq] at hs
  have hshift := add_left_cancel hs
  apply immPaths_get_injective n hn
  apply edgeListShift_injective_of_labels side (List.finRange n) (List.nodup_finRange n)
    _ _ (immPaths_labels n hn _ (List.get_mem _ p))
    (immPaths_labels n hn _ (List.get_mem _ q))
  simpa only [edgeListShift_eq_sum, occupationShift] using hshift

/-- Any collision of distinct finite shifts has a zero-amplitude contribution. -/
theorem immTargetShift_collision_zero (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) [Nonempty (ImmTargetIndex n side a b)]
    (d : ImmSourceIndex n side a b) (p q : Fin (immPaths n hn).length)
    (hpq : p ≠ q) (hs : immTargetShift n hn side a b d p =
      immTargetShift n hn side a b d q) :
    immPathAmplitude n hn (fun x => side x.1) d.1 p = 0 ∨
      immPathAmplitude n hn (fun x => side x.1) d.1 q = 0 := by
  by_cases hp : immPathAmplitude n hn (fun x => side x.1) d.1 p = 0
  · exact Or.inl hp
  by_cases hq : immPathAmplitude n hn (fun x => side x.1) d.1 q = 0
  · exact Or.inr hq
  apply False.elim
  apply hpq
  apply immPathOccupation_injective_of_nonzero n hn side d.1 p q hp hq
  have hv := congrArg Subtype.val hs
  simpa only [immTargetShift_val_of_amplitude_ne_zero n hn side a b d p hp,
    immTargetShift_val_of_amplitude_ne_zero n hn side a b d q hq] using hv

/-- All entries of the normalized IMM operator are real, so adjoint equals transpose. -/
theorem immNormalizedMatrix_conjTranspose (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) :
    (immNormalizedMatrix n side a b).conjTranspose =
      (immNormalizedMatrix n side a b).transpose := by
  classical
  ext d e
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply,
    immNormalizedMatrix_apply n hn side a b]
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- The first Gram trace of the actual IMM operator is its total path occupation mass. -/
theorem immNormalizedMatrix_first_trace (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) [Nonempty (ImmTargetIndex n side a b)] :
    Matrix.trace ((immNormalizedMatrix n side a b).conjTranspose *
      immNormalizedMatrix n side a b) =
      ∑ d : ImmSourceIndex n side a b, ∑ p : Fin (immPaths n hn).length,
        ((immPathAmplitude n hn (fun x => side x.1) d.1 p) ^ 2 : ℝ) := by
  classical
  rw [immNormalizedMatrix_conjTranspose n hn side a b,
    immNormalizedMatrix_eq_pathShiftMatrix n hn side a b,
    pathShiftMatrix_first_trace]
  · simp
  · intro d p q hpq hs
    rcases immTargetShift_collision_zero n hn side a b d p q hpq hs with hp | hq
    · simp [hp]
    · simp [hq]

end Problem335

end

end OAI
