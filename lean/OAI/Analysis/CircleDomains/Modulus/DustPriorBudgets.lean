import OAI.Analysis.CircleDomains.Probability.CountableLawRestriction
import OAI.Analysis.CircleDomains.Probability.PriorLawPresentation
import OAI.Analysis.CircleDomains.Probability.CodeLawCandidateConsequences
import OAI.Analysis.CircleDomains.Sobolev.FiniteHitSquareEnergy

namespace OAI

/-! The candidate's prescribed-mark budget supplies exactly the dust
visit norms used by the prior-contact argument. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] [BorelSpace X] [SecondCountableTopology X] in
theorem priorHitMass_codePathLaw (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    priorHitMass (codePathLaw d P : Measure C(PathTime, X)) x = codeHitProbability d P x :=
  pathHitProbability_codePathLaw d P x

omit [MeasurableSpace Y] [BorelSpace Y] [BorelSpace X] [SecondCountableTopology X] in
theorem dust_prior_weight_norm_finite (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (B : Set X)
    (hhit : (∑' x : B, codeHitProbability d P x.val ^ 2) < ∞) :
    countingSquareNorm (fun x : support (dustPriorHitMass B (codePathLaw d P : Measure _)) =>
      dustPriorHitMass B (codePathLaw d P : Measure _) x.val) < ∞ := by
  let M := support (dustPriorHitMass B (codePathLaw d P : Measure C(PathTime, X)))
  have hMB (x : M) : x.val ∈ B := by
    have hx : x.val ∈ support (dustPriorHitMass B (codePathLaw d P : Measure _)) := x.property
    rw [support_dustPriorHitMass] at hx
    exact hx.1
  let f : M → B := fun x => ⟨x.val, hMB x⟩
  have hf : Injective f := fun _ _ h => Subtype.ext (congrArg (fun x : B => x.val) h)
  have he : (fun x : M => dustPriorHitMass B (codePathLaw d P : Measure _) x.val) =
      (fun x : B => codeHitProbability d P x.val) ∘ f := by
    funext x
    have hx : x.val ∈ B := hMB x
    simp only [dustPriorHitMass, hx, ite_true, priorHitMass_codePathLaw, comp_apply, f]
  rw [he]
  apply (countingSquareNorm_comp_injective _ f hf).trans_lt
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hhit.ne

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem candidate_visit_norm_on_marks (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (M T : Set X) (hTM : T ⊆ M)
    {C : ℝ≥0∞}
    (hb : CountableSquareLawBounds (codeVisitWeight d (fun x : M => x.val)) (C ^ 2) P) :
    countingSquareNorm (fun x : T => meanVisitCount (codePathLaw d P) x.val) ≤ C := by
  have hsub : range (fun x : T => x.val) ⊆ range (fun x : M => x.val) := by
    rintro x ⟨t, rfl⟩
    exact ⟨⟨t.val, hTM t.property⟩, rfl⟩
  exact (countingSquareNorm_restrict_range (meanVisitCount (codePathLaw d P))
    (fun x : T => x.val) (fun x : M => x.val) Subtype.val_injective hsub).trans
      (countableSquareLawBounds_visit_norm d P (fun x : M => x.val) hb)

theorem PriorLawPresentation.prior_visit_norm_finite
    {B S : Set X} {μ : ℕ → Measure C(PathTime, X)} (R : PriorLawPresentation B S μ)
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (σ : Measure Y) (τ : Measure LevelTuple) (M N E C : ℝ≥0∞) (hC : C < ∞)
    (hb : CodeLawCandidate d (fun x : R.marks => x.val) σ τ M N E (C ^ 2) P) (i : ℕ) :
    countingSquareNorm (fun x : support (dustPriorHitMass B (μ i)) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞ :=
  (candidate_visit_norm_on_marks d P R.marks _ (R.prior_marks i) hb.2.1).trans_lt hC

end CircleDomainRigidity

end

end OAI
