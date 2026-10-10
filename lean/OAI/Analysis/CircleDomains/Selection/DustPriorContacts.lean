import OAI.Analysis.CircleDomains.Selection.PriorResidualContacts

namespace OAI

/-! Prior constraints only charge residual times in the dust. Consequently
their finite-toll argument only needs visit bounds at dust marks; a possible
atom at the image of infinity does not impose an extra path constraint. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

def dustPriorHitMass {X : Type*} [MetricSpace X]
    [MeasurableSpace C(PathTime, X)] (B : Set X) (μ : Measure C(PathTime, X)) : X → ℝ≥0∞ :=
  fun x => if x ∈ B then priorHitMass μ x else 0

theorem support_dustPriorHitMass {X : Type*} [MetricSpace X]
    [MeasurableSpace C(PathTime, X)] (B : Set X) (μ : Measure C(PathTime, X)) :
    support (dustPriorHitMass B μ) = B ∩ support (priorHitMass μ) := by
  ext x
  by_cases hx : x ∈ B <;> simp [dustPriorHitMass, hx]

theorem residualToll_dust_restriction {X : Type*} [MetricSpace X]
    (B I : Set X) (J : Set PathTime) (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B J (deletedWeight I (fun x => if x ∈ B then m x else 0)) Γ =
      residualToll B J (deletedWeight I m) Γ := by
  apply tsum_congr
  intro t
  by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ J
  · have hb : Γ.1 t ∈ B := ht.1.1
    simp only [ht, ite_true, deletedWeight, hb]
  · simp only [ht, ite_false]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_code_dust_prior_envelope_null (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (hm : (support (dustPriorHitMass d.dust (d.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (dustPriorHitMass d.dust (d.priorLaws i)) =>
      dustPriorHitMass d.dust (d.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (dustPriorHitMass d.dust (d.priorLaws i)) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (dustPriorHitMass d.dust (d.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ d.priorDeletions i n) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), (d.priorLaws i)
      (⋂ n, {η | (Γ.val, η) ∈ residualIncidence d.dust univ pathHitSet
        (d.priorDeletions i n)}) = 0 := by
  filter_upwards [ae_code_boundaryToll_finite d P _ hm hweight hvisits] with Γ hΓ
  apply residual_incidence_envelope_null d.dust univ pathHitSet _ _ hm _ hcover Γ.val hΓ
  intro n
  change _ ≤ residualToll d.dust univ
    (deletedWeight (d.priorDeletions i n)
      (fun x => if x ∈ d.dust then priorHitMass (d.priorLaws i) x else 0)) Γ.val
  rw [residualToll_dust_restriction]
  exact baseCode_prior_bound d Γ i n

theorem ae_later_residual_contact_in_prior_support_of_dust_bounds
    (d e : PathCodeData X Y) (hB : IsClosed e.dust)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (i : ℕ) (hprior : e.priorLaws i = (codePathLaw d P : Measure C(PathTime, X)))
    (hm : (support (dustPriorHitMass e.dust (e.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      dustPriorHitMass e.dust (e.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      meanVisitCount (codePathLaw e Q) x.val) < ∞)
    (hcover : ∀ x ∈ support (dustPriorHitMass e.dust (e.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ e.priorDeletions i n)
    (hsub : ∀ n, (e.priorDeletions i n : Set X) ⊆ support (priorHitMass (e.priorLaws i))) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ t ∈ residualTimes e.dust p.2.val, p.2.val.1 t ∈ range p.1.val.1 →
        p.2.val.1 t ∈ support (priorHitMass (e.priorLaws i)) := by
  let : SFinite (e.priorLaws i) := by rw [hprior]; infer_instance
  have hb := ae_no_residual_incidence_of_null_envelopes e hB pathHitSet isClosed_pathHitSet
    Q (e.priorLaws i) (e.priorDeletions i) (support (priorHitMass (e.priorLaws i))) hsub
    (ae_code_dust_prior_envelope_null e Q i hm hweight hvisits hcover)
  have hb' : ∀ᵐ q ∂((Q : Measure (BasePathCode e)).prod
      (codePathLaw d P : Measure C(PathTime, X))),
      ∀ t ∈ residualTimes e.dust q.1.val, (q.2, q.1.val.1 t) ∈ pathHitSet →
        q.1.val.1 t ∈ support (priorHitMass (e.priorLaws i)) := by
    simpa only [hprior] using hb
  have hpath : MeasurePreserving (codePath d) (P : Measure (BasePathCode d))
      (codePathLaw d P : Measure C(PathTime, X)) := ⟨measurable_codePath d, rfl⟩
  exact (Measure.measurePreserving_swap.comp
    (hpath.prod (MeasurePreserving.id (Q : Measure (BasePathCode e))))).quasiMeasurePreserving.ae hb'

end CircleDomainRigidity

end

end OAI
