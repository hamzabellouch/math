import OAI.Analysis.CircleDomains.Selection.ResidualProductAvoidance

namespace OAI

/-! Pull the actual prior-law residual constraint back to independent
samples of the earlier and later code laws. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_later_residual_contact_in_prior_support
    (d e : PathCodeData X Y) (hB : IsClosed e.dust)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (i : ℕ) (hprior : e.priorLaws i = (codePathLaw d P : Measure C(PathTime, X)))
    (hm : (support (priorHitMass (e.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (priorHitMass (e.priorLaws i)) =>
      priorHitMass (e.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (priorHitMass (e.priorLaws i)) =>
      meanVisitCount (codePathLaw e Q) x.val) < ∞)
    (hcover : ∀ x ∈ support (priorHitMass (e.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ e.priorDeletions i n)
    (hsub : ∀ n, (e.priorDeletions i n : Set X) ⊆ support (priorHitMass (e.priorLaws i))) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ t ∈ residualTimes e.dust p.2.val, p.2.val.1 t ∈ range p.1.val.1 →
        p.2.val.1 t ∈ support (priorHitMass (e.priorLaws i)) := by
  let : SFinite (e.priorLaws i) := by rw [hprior]; infer_instance
  have hb := ae_no_residual_incidence_of_null_envelopes e hB pathHitSet isClosed_pathHitSet
    Q (e.priorLaws i) (e.priorDeletions i) (support (priorHitMass (e.priorLaws i))) hsub
    (ae_code_prior_envelope_null e Q i hm hweight hvisits hcover)
  have hb' : ∀ᵐ q ∂((Q : Measure (BasePathCode e)).prod
      (codePathLaw d P : Measure C(PathTime, X))),
      ∀ t ∈ residualTimes e.dust q.1.val, (q.2, q.1.val.1 t) ∈ pathHitSet →
        q.1.val.1 t ∈ support (priorHitMass (e.priorLaws i)) := by
    simpa only [hprior] using hb
  have hpath : MeasurePreserving (codePath d) (P : Measure (BasePathCode d))
      (codePathLaw d P : Measure C(PathTime, X)) :=
    ⟨measurable_codePath d, rfl⟩
  have hprod := Measure.measurePreserving_swap.comp
    (hpath.prod (MeasurePreserving.id (Q : Measure (BasePathCode e))))
  exact hprod.quasiMeasurePreserving.ae hb'

end CircleDomainRigidity

end

end OAI
