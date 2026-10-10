import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.NextGroupConjugation

namespace OAI

/-! # Factorization of the intrinsic remaining-root product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

theorem rootProduct_map_factor (q : InitialRootStep n)
    {D : Finset (Fin n)} (c : EliminationChain q.processed D)
    (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : ↥q.remaining → Measure ℝ) [∀ p, SigmaFinite (ν p)] :
    (Measure.pi ν).map (c.remainingGroupCoordinates q.initial hfinal).symm =
      (((Measure.pi fun p : q.NextRoot => ν ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩).map
        q.nextGroupCoordinates.symm).prod (ν ⟨q.root,q.mem_remaining⟩)).map q.remainingFactor := by
  let S := q.splitRootCoordinates
  let E := c.remainingGroupCoordinates q.initial hfinal
  let K : (q.NextRoot → ℝ) × ℝ → positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ :=
    Prod.map q.nextGroupCoordinates.symm id
  have hK : Measurable K := q.nextGroupCoordinates.symm.measurable.prodMap measurable_id
  have H : ((Measure.pi fun p : q.NextRoot => ν ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩).map
        q.nextGroupCoordinates.symm).prod (ν ⟨q.root,q.mem_remaining⟩) =
      ((Measure.pi ν).map S).map K := by
    rw [(q.splitRootCoordinates_preserves ν).map_eq]
    change _ = ((Measure.pi fun p : q.NextRoot => ν ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩).prod
      (ν ⟨q.root,q.mem_remaining⟩)).map (Prod.map q.nextGroupCoordinates.symm id)
    rw [←Measure.map_prod_map _ _ q.nextGroupCoordinates.symm.measurable measurable_id,
      Measure.map_id]
  rw [H,Measure.map_map q.remainingFactor.measurable hK,
    Measure.map_map (q.remainingFactor.measurable.comp hK) S.measurable]
  apply congrArg (fun f => (Measure.pi ν).map f)
  funext v
  apply E.injective
  rw [E.apply_symm_apply]
  apply S.injective
  change S v = S (E (q.remainingFactor (K (S v))))
  have hw := q.remainingFactor_coordinates c hfinal (K (S v))
  simpa only [K,Prod.map_fst,Prod.map_snd,id_eq,Homeomorph.apply_symm_apply] using hw.symm

theorem ae_remainingIntrinsicProduct_factor (d : ℕ) (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, c.remainingIntrinsicProduct q.initial hfinal μ x =
      ((q.nextIntrinsicProduct d μ x).prod (intrinsicRootLeaf q.distinct μ x)).map
        q.remainingFactor := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H (p : ↥q.remaining) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (q.remaining_positive p.val p.prop)) μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  filter_upwards [ae_all_iff.mpr H] with x hx
  let : ∀ p : ↥q.remaining,
      IsLocallyFiniteMeasure (intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val p.prop)) μ x) :=
    fun p => (hx p).1
  exact q.rootProduct_map_factor c hfinal
    (fun p => intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val p.prop)) μ x)

end InitialRootStep
end DukePrimeDegree

end

end OAI
