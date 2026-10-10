import OAI.Algebra.DepthFive.ImmFiniteMatrix
import OAI.Algebra.DepthFive.FourPathTrace

namespace OAI

/-! The second trace identity for the actual IMM operator in normalized
monomial coordinates.  Invalid path actions have zero amplitude, so their
chosen finite target index does not enter the trace. -/

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The signed exponent displacement of an actual IMM path. -/
def immPathSignedShift (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (p : Fin (immPaths n hn).length) : (Fin n × Fin n × Fin n) →₀ ℤ :=
  occupationShift isV ((immPaths n hn).get p)

/-- Every nonzero actual path action has its prescribed signed displacement. -/
theorem signedOccupation_immPathOccupation (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length)
    (hamp : immPathAmplitude n hn isV d p ≠ 0) :
    signedOccupation (immPathOccupation n hn isV d p) =
      signedOccupation d + immPathSignedShift n hn isV p := by
  exact signedOccupation_path_of_amplitude_ne_zero isV ((immPaths n hn).get p)
    (immPaths_nodup n hn _ (List.get_mem _ p)) d hamp

/-- A finite submatrix of the genuine normalized IMM operator. -/
def immCoefficientMatrix {I J : Type*} (n : ℕ)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (source : I → (Fin n × Fin n × Fin n) →₀ ℕ)
    (target : J → (Fin n × Fin n × Fin n) →₀ ℕ) : Matrix J I ℂ :=
  fun j i => complexFockBasis.repr
    (mixedOperator isV (imm ℂ n) (complexFockMonomial (source i))) (target j)

/-- The finite normalized coefficient matrix is the actual weighted path matrix
whenever all nonzero path actions are represented in its target coordinates. -/
theorem immCoefficientMatrix_eq_pathShiftMatrix {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (n : ℕ) (hn : 0 < n) (isV : (Fin n × Fin n × Fin n) → Bool)
    (source : I → (Fin n × Fin n × Fin n) →₀ ℕ)
    (target : J → (Fin n × Fin n × Fin n) →₀ ℕ)
    (htarget : Function.Injective target)
    (shift : I → Fin (immPaths n hn).length → J)
    (hshift : ∀ i p, immPathAmplitude n hn isV (source i) p ≠ 0 →
      target (shift i p) = immPathOccupation n hn isV (source i) p) :
    immCoefficientMatrix n isV source target =
      pathShiftMatrix shift (fun i p => (immPathAmplitude n hn isV (source i) p : ℂ)) := by
  classical
  ext j i
  change complexFockBasis.repr
    (mixedOperator isV (imm ℂ n) (complexFockMonomial (source i))) (target j) = _
  rw [complexFockBasis_repr_mixedOperator_imm n hn isV]
  unfold pathShiftMatrix
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hz : immPathAmplitude n hn isV (source i) p = 0
  · simp [hz]
  · simp only [← hshift i p hz, htarget.eq_iff]

/-- Source-eliminated second trace for the genuine finite IMM coefficient
matrix.  The only coordinate hypothesis says that nonzero path actions stay
in the chosen target basis; no trace or moment formula is assumed. -/
theorem immCoefficientMatrix_second_trace {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (n : ℕ) (hn : 0 < n) (isV : (Fin n × Fin n × Fin n) → Bool)
    (source : I → (Fin n × Fin n × Fin n) →₀ ℕ)
    (hsource : Function.Injective source)
    (target : J → (Fin n × Fin n × Fin n) →₀ ℕ)
    (htarget : Function.Injective target)
    (shift : I → Fin (immPaths n hn).length → J)
    (hshift : ∀ i p, immPathAmplitude n hn isV (source i) p ≠ 0 →
      target (shift i p) = immPathOccupation n hn isV (source i) p) :
    let A := immCoefficientMatrix n isV source target
    let occupation := fun i => signedOccupation (source i)
    let eps := immPathSignedShift n hn isV
    let weight := fun i p => immPathAmplitude n hn isV (source i) p
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ i, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          weight i p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
            (occupation i + eps p - eps q) * weight i r *
          Function.extend occupation (fun k => weight k s) (fun _ => 0)
            (occupation i + eps p - eps q) else 0 := by
  classical
  dsimp only
  rw [immCoefficientMatrix_eq_pathShiftMatrix n hn isV source target htarget shift hshift]
  apply complex_path_second_trace_eliminate_source
    (fun i => signedOccupation (source i)) (signedOccupation_injective.comp hsource)
    (fun j => signedOccupation (target j)) (signedOccupation_injective.comp htarget)
  intro i p hp
  rw [hshift i p hp]
  exact signedOccupation_immPathOccupation n hn isV (source i) p hp

/-- A finite target index for each path.  The fallback is used only for a
zero-amplitude path, and is therefore invisible in the operator matrix. -/
def immFinitePathShift (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    (e0 : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b)
    (p : Fin (immPaths n hn).length) : ImmTargetIndex n side a b := by
  classical
  exact if h : immPathAmplitude n hn (fun x => side x.1) d.1 p ≠ 0 then
    ⟨immPathOccupation n hn (fun x => side x.1) d.1 p,
      immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p h⟩
    else e0

theorem immFinitePathShift_val_of_amplitude_ne_zero
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    (e0 : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b)
    (p : Fin (immPaths n hn).length)
    (hp : immPathAmplitude n hn (fun x => side x.1) d.1 p ≠ 0) :
    (immFinitePathShift n hn side a b e0 d p).1 =
      immPathOccupation n hn (fun x => side x.1) d.1 p := by
  simp only [immFinitePathShift, dite_eq_left hp]

/-- The finite normalized operator matrix is the indicated submatrix of its
ambient normalized monomial coefficients. -/
theorem immNormalizedMatrix_eq_immCoefficientMatrix
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    immNormalizedMatrix n side a b =
      immCoefficientMatrix n (fun x => side x.1)
        (fun d : ImmSourceIndex n side a b => d.1)
        (fun e : ImmTargetIndex n side a b => e.1) := by
  classical
  ext e d
  rw [immNormalizedMatrix_apply n hn side a b]
  exact (complexFockBasis_repr_mixedOperator_imm n hn (fun x => side x.1) d.1 e.1).symm

/-- The actual finite IMM matrix has a weighted finite-path representation. -/
theorem immNormalizedMatrix_eq_pathShiftMatrix_of_fallback
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    (e0 : ImmTargetIndex n side a b) :
    immNormalizedMatrix n side a b =
      pathShiftMatrix (immFinitePathShift n hn side a b e0)
        (fun d p => (immPathAmplitude n hn (fun x => side x.1) d.1 p : ℂ)) := by
  classical
  rw [immNormalizedMatrix_eq_immCoefficientMatrix n hn side a b]
  exact immCoefficientMatrix_eq_pathShiftMatrix n hn (fun x => side x.1)
    _ _ Subtype.val_injective _
    (immFinitePathShift_val_of_amplitude_ne_zero n hn side a b e0)

/-- Exact source-eliminated second trace of the genuine finite IMM operator.
This includes an empty target space: then every path amplitude vanishes.
There are no trace, closure, or nonempty-index assumptions in the statement. -/
theorem immNormalizedMatrix_second_trace
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    let A := immNormalizedMatrix n side a b
    let occupation := fun d : ImmSourceIndex n side a b => signedOccupation d.1
    let eps := immPathSignedShift n hn (fun x => side x.1)
    let weight := fun (d : ImmSourceIndex n side a b) p =>
      immPathAmplitude n hn (fun x => side x.1) d.1 p
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ d, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          weight d p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
            (occupation d + eps p - eps q) * weight d r *
          Function.extend occupation (fun k => weight k s) (fun _ => 0)
            (occupation d + eps p - eps q) else 0 := by
  classical
  rcases isEmpty_or_nonempty (ImmTargetIndex n side a b) with h | h
  · let := h
    have hA : immNormalizedMatrix n side a b = 0 := Subsingleton.elim _ _
    have hz (d : ImmSourceIndex n side a b) (p : Fin (immPaths n hn).length) :
        immPathAmplitude n hn (fun x => side x.1) d.1 p = 0 := by
      by_contra hp
      exact isEmptyElim (⟨immPathOccupation n hn (fun x => side x.1) d.1 p,
        immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p hp⟩ :
          ImmTargetIndex n side a b)
    simp [hA, hz]
  · obtain ⟨e0⟩ := h
    dsimp only
    rw [immNormalizedMatrix_eq_immCoefficientMatrix n hn side a b]
    exact immCoefficientMatrix_second_trace n hn (fun x => side x.1)
      _ Subtype.val_injective _ Subtype.val_injective
      (immFinitePathShift n hn side a b e0)
      (immFinitePathShift_val_of_amplitude_ne_zero n hn side a b e0)

end Problem335

end

end OAI
