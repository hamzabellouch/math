import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootProductBoxes
import OAI.NumberTheory.DukePrimeDegree.Geometry.NextProductHolonomy
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductReorder

namespace OAI

/-! # A common sampled reference on each independent root fiber -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

def rootFiberPoint (d : ℕ) (q : InitialRootStep (d+1)) (b : S → X (d+1))
    (z : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) : X (d+1) :=
  rightAction (b z.1) (q.remainingBeforeRoot d z.2)

lemma measurable_rootFiberPoint (d : ℕ) (q : InitialRootStep (d+1))
    (b : S → X (d+1)) (hb : Measurable b) : Measurable (q.rootFiberPoint d b) :=
  (continuous_rightAction_uncurry (d+1)).measurable.comp
    ((hb.comp measurable_fst).prodMk ((q.measurable_remainingBeforeRoot d).comp measurable_snd))

omit [MeasurableSpace S] in
lemma rootFiberPoint_translate (d : ℕ) (q : InitialRootStep (d+1))
    (b : S → X (d+1)) (s : S)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (t u : ℝ) :
    rightAction (q.rootFiberPoint d b (s,(w,t)))
      (Matrix.SpecialLinearGroup.transvection q.distinct (u-t)) =
        q.rootFiberPoint d b (s,(w,u)) := by
  unfold rootFiberPoint remainingBeforeRoot
  rw [rightAction_mul,mul_assoc,←Matrix.SpecialLinearGroup.transvection_add,
    show t+(u-t)=u by ring]

theorem exists_common_nextProduct_reference (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
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
          q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t₀))) := by
  obtain ⟨N,hN,hN0,hconst⟩ := exists_nullset_nextProduct_constancy d q μ hA
  have hNae : ∀ᵐ x ∂μ, x ∉ N := by
    simpa only [ae_iff,not_not,ofPred_mem_eq] using hN0
  have havoid : ∀ᵐ z ∂ρ, q.rootFiberPoint d b z ∉ N :=
    ae_of_ae_map (q.measurable_rootFiberPoint d b hb).aemeasurable (hρ.ae_le hNae)
  have H : ∀ᵐ s ∂ρ.fst, ∀ᵐ z ∂ρ.condKernel s,
      Good (s,z) ∧ q.rootFiberPoint d b (s,z) ∉ N := by
    have HG : ∀ᵐ z ∂ρ.fst ⊗ₘ ρ.condKernel,
        Good z ∧ q.rootFiberPoint d b z ∉ N := by
      simpa only [Measure.disintegrate] using hGood.and havoid
    exact Measure.ae_ae_of_ae_compProd HG
  filter_upwards [H,hprod] with s hs hp
  rw [hp] at hs
  obtain ⟨w,hw⟩ := (Measure.ae_ae_of_ae_prod hs).exists
  obtain ⟨t₀,ht₀⟩ := hw.exists
  refine ⟨w,t₀,ht₀.1,hw.mono fun t ht => ⟨ht.1,?_⟩⟩
  have he := q.rootFiberPoint_translate d b s w t₀ t
  have h := hconst (q.rootFiberPoint d b (s,(w,t₀))) ht₀.2 (t-t₀)
    (by rw [he]; exact ht.2)
  simpa only [he] using h

end InitialRootStep
end DukePrimeDegree

end

end OAI
