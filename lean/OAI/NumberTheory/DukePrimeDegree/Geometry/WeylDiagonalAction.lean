import OAI.NumberTheory.DukePrimeDegree.Entropy.WeylEntropy

namespace OAI

/-! # Diagonal invariance and ergodicity under coordinate permutations -/

noncomputable section
open MeasureTheory Set Filter
namespace DukePrimeDegree
open PrimeDegreePackets

/-- The original last coordinate is restored before the coordinates are permuted. -/
def reindexLogCoordinates (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) : LogCoordinates d :=
  fun i => restoredLogCoordinates u (e.symm i.castSucc)

lemma reindex_diagonalFlow (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) :
    reindexSpecialLinear ℝ e (diagonalFlow u) = diagonalFlow (reindexLogCoordinates d e u) := by
  have hs := restoredLogCoordinates_sum u
  have he : diagonalOneParameter (restoredLogCoordinates u) hs 1=diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext i
    simp only [restoredLogCoordinates,Fin.snoc_castSucc,mul_one]
  rw [←he,reindex_diagonalOneParameter,diagonalOneParameter_eq_diagonalFlow]
  congr 1
  funext i
  simp only [reindexLogCoordinates,mul_one]

lemma reindex_diagonalFlow_conjugacy (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) (x : X (d+1)) :
    quotientReindex e (rightAction x (diagonalFlow u)) =
      rightAction (quotientReindex e x) (diagonalFlow (reindexLogCoordinates d e u)) := by
  rw [quotientReindex_rightAction,reindex_diagonalFlow]

lemma reindex_diagonalFlow_reverse (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) (x : X (d+1)) :
    quotientReindex e (rightAction x (diagonalFlow (reindexLogCoordinates d e.symm u))) =
      rightAction (quotientReindex e x) (diagonalFlow u) := by
  apply (quotientReindexHomeomorph e.symm).injective
  change quotientReindex e.symm (quotientReindex e
    (rightAction x (diagonalFlow (reindexLogCoordinates d e.symm u)))) =
      quotientReindex e.symm (rightAction (quotientReindex e x) (diagonalFlow u))
  rw [quotientReindex_symm_apply,reindex_diagonalFlow_conjugacy,
    quotientReindex_symm_apply]

/-- The full diagonal action remains invariant after reindexing. -/
theorem diagonal_invariant_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (u : LogCoordinates d) :
    (μ.map (quotientReindex e)).map (fun x => rightAction x (diagonalFlow u)) =
      μ.map (quotientReindex e) := by
  rw [Measure.map_map (continuous_rightAction _).measurable
    (continuous_quotientReindex e).measurable]
  have he : (fun x => rightAction x (diagonalFlow u)) ∘ quotientReindex e =
      quotientReindex e ∘ (fun x => rightAction x
        (diagonalFlow (reindexLogCoordinates d e.symm u))) := by
    funext x
    exact (reindex_diagonalFlow_reverse d e u x).symm
  rw [he,←Measure.map_map (continuous_quotientReindex e).measurable
    (continuous_rightAction _).measurable,hA]

/-- Ergodicity uses the full diagonal group, whose parameters are permuted
along with the coordinates. -/
theorem diagonal_ergodic_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1)))
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
      (μ.map (quotientReindex e)) := by
  let E := (quotientReindexHomeomorph e).toMeasurableEquiv
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro u S hS
    exact (show MeasurePreserving (fun x => rightAction x (diagonalFlow u.toAdd))
      (μ.map (quotientReindex e)) (μ.map (quotientReindex e)) from
      ⟨(continuous_rightAction _).measurable,diagonal_invariant_reindex d e μ hA _⟩).measure_preimage
        hS.nullMeasurableSet
  · intro S hS hfix
    change EventuallyEmptyOrUniv S (ae (μ.map E))
    rw [←E.map_ae μ,←eventuallyEmptyOrUniv_preimage]
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
      (G := Multiplicative (LogCoordinates d)) (hS.preimage E.measurable)
    intro u
    have h := ae_of_ae_map E.measurable.aemeasurable
      (hfix (Multiplicative.ofAdd (reindexLogCoordinates d e u.toAdd))).mem_iff
    filter_upwards [h] with x hx
    apply propext
    change rightAction x (diagonalFlow u.toAdd) ∈ E ⁻¹' S ↔ x ∈ E ⁻¹' S
    change rightAction (quotientReindex e x)
      (diagonalFlow (reindexLogCoordinates d e u.toAdd)) ∈ S ↔ quotientReindex e x ∈ S at hx
    change quotientReindex e (rightAction x (diagonalFlow u.toAdd)) ∈ S ↔
      quotientReindex e x ∈ S
    rw [reindex_diagonalFlow_conjugacy]
    exact hx

end DukePrimeDegree

end

end OAI
