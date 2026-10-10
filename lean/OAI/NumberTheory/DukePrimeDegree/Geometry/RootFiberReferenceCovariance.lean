import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFiberReference
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase

namespace OAI

/-! # A common reference with the required next-product covariance -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

theorem exists_covariant_nextProduct_reference (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (b : S → X (d+1)) (hb : Measurable b)
    (ρ : Measure (S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)))
    [IsFiniteMeasure ρ]
    (hρ : ρ.map (q.rootFiberPoint d b) ≪ μ)
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd)
    (Good : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) → Prop)
    (hGood : ∀ᵐ z ∂ρ, Good z) :
    ∀ᵐ s ∂ρ.fst, ∃ w : positiveRootGeneratedGroup (q.remaining.erase q.root), ∃ t₀ : ℝ,
      Good (s,(w,t₀)) ∧ ∀ᵐ t ∂(ρ.condKernel s).snd,
        Good (s,(w,t)) ∧
        q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t))) =
          q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t₀))) ∧
        (q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t₀)))).map
          (q.nextConjugation d (t-t₀)) =
            q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t₀))) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  rcases intrinsicRootLeaf_ergodic_alternative d q.distinct μ with hna | hat
  · have hc : ∀ᵐ z ∂ρ, ∀ r : ℝ,
        (q.nextIntrinsicProduct d μ (q.rootFiberPoint d b z)).map (q.nextConjugation d r) =
          q.nextIntrinsicProduct d μ (q.rootFiberPoint d b z) :=
      ae_of_ae_map (q.measurable_rootFiberPoint d b hb).aemeasurable
        (hρ.ae_le (ae_nextIntrinsicProduct_conjugation d q μ hna))
    have H := q.exists_common_nextProduct_reference d μ hA b hb ρ hρ hprod
      (fun z => Good z ∧ ∀ r : ℝ,
        (q.nextIntrinsicProduct d μ (q.rootFiberPoint d b z)).map (q.nextConjugation d r) =
          q.nextIntrinsicProduct d μ (q.rootFiberPoint d b z)) (hGood.and hc)
    filter_upwards [H] with s hs
    obtain ⟨w,t₀,hw,ht⟩ := hs
    exact ⟨w,t₀,hw.1,ht.mono fun t ht => ⟨ht.1.1,ht.2,hw.2 (t-t₀)⟩⟩
  · obtain ⟨N,hN,hN0,htrans⟩ := exists_nullset_atomic_root_transversal d q.distinct μ hA hat
    have hn : ∀ᵐ x ∂μ, x ∉ N := by
      simpa only [ae_iff,not_not,ofPred_mem_eq] using hN0
    have hc : ∀ᵐ z ∂ρ, q.rootFiberPoint d b z ∉ N :=
      ae_of_ae_map (q.measurable_rootFiberPoint d b hb).aemeasurable (hρ.ae_le hn)
    have H := q.exists_common_nextProduct_reference d μ hA b hb ρ hρ hprod
      (fun z => Good z ∧ q.rootFiberPoint d b z ∉ N) (hGood.and hc)
    filter_upwards [H] with s hs
    obtain ⟨w,t₀,hw,ht⟩ := hs
    refine ⟨w,t₀,hw.1,ht.mono fun t ht => ⟨ht.1.1,ht.2,?_⟩⟩
    have hz : t-t₀ = 0 := htrans (q.rootFiberPoint d b (s,(w,t₀))) hw.2 (t-t₀) (by
      rw [q.rootFiberPoint_translate]
      exact ht.1.2)
    rw [hz]
    have he : q.nextConjugation d 0 = id := funext (q.nextConjugation_zero d)
    rw [he,Measure.map_id]

end InitialRootStep
end DukePrimeDegree

end

end OAI
