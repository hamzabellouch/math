import OAI.Analysis.CircleDomains.Selection.DustPriorContacts
import OAI.Analysis.CircleDomains.Selection.ResidualTagContacts
import OAI.Analysis.CircleDomains.Selection.RankedTagPairAvoidance

namespace OAI

/-! Diffuse dust intersections using only the visit bounds on dust marks.
No visit bound is required at the distinguished image of infinity. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

private theorem tag_interval_of_not_residual {X : Type*} [TopologicalSpace X]
    (B : Set X) (Γ : TaggedPath X) (t : PathTime) (ht : Γ.1 t ∈ B)
    (hres : t ∉ residualTimes B Γ) :
    ∃ k, tagLeft (Γ.2 k) < t ∧ t < tagRight (Γ.2 k) := by
  by_contra h
  apply hres
  refine ⟨ht, ?_⟩
  intro k
  by_cases hl : t ≤ tagLeft (Γ.2 k)
  · exact Or.inl hl
  · right
    by_contra hr
    exact h ⟨k, lt_of_not_ge hl, lt_of_not_ge hr⟩

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_ranked_diffuse_dust_intersections_of_dust_bounds
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (d e : PathCodeData X Y) (hB : IsClosed d.dust) (hde : e.dust = d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (hle : e.levels = d.levels)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (i : ℕ) (hprior : e.priorLaws i = (codePathLaw d P : Measure C(PathTime, X)))
    (hm : (support (dustPriorHitMass e.dust (e.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      dustPriorHitMass e.dust (e.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      meanVisitCount (codePathLaw e Q) x.val) < ∞)
    (hcover : ∀ x ∈ support (dustPriorHitMass e.dust (e.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ e.priorDeletions i n)
    (hsub : ∀ n, (e.priorDeletions i n : Set X) ⊆ support (priorHitMass (e.priorLaws i)))
    (S : Set X) (hFS : ∀ n, (d.flagDeletions n : Set X) ⊆ S)
    (hmlevel : ∀ j, (support (d.levelWeights j)).Countable)
    (hwlevel : ∀ j, countingSquareNorm (fun x : support (d.levelWeights j) =>
      d.levelWeights j x.val) < ∞)
    (hvlevel : ∀ j, countingSquareNorm (fun x : support (d.levelWeights j) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hflagcover : ∀ j x, x ∈ support (d.levelWeights j) →
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hcompat : RankedLevelNullCompatibility rank d.levels (d.dust \ S))
    (hunique : ∀ x ∈ d.dust \ S, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτP : meanCodeTuple d P ≪ tupleReference ω)
    (hτQ : meanCodeTuple e Q ≪ tupleReference ω) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range p.1.val.1 ∩ range p.2.val.1 ∩ d.dust ⊆
        S ∪ support (priorHitMass (e.priorLaws i)) := by
  have hpriorAE := ae_later_residual_contact_in_prior_support_of_dust_bounds d e (hde ▸ hB)
    P Q i hprior hm hweight hvisits hcover hsub
  have hresAE := ae_residual_tag_contact_in_flags d e hB hH hle P Q ω hτQ
    hmlevel hwlevel hvlevel hflagcover S hFS
  have htagAE := ae_ranked_no_tag_pair_contact rank hrank d e hle hH (d.dust \ S)
    hcompat hunique P Q ω hτP hτQ
  filter_upwards [hpriorAE, hresAE, htagAE] with p hp hr ht
  rintro x ⟨⟨⟨t, htx⟩, ⟨u, hux⟩⟩, hxB⟩
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  have hnewB : p.2.val.1 u ∈ e.dust := by rw [hux, hde]; exact hxB
  by_cases hnew : u ∈ residualTimes e.dust p.2.val
  · right
    rw [← hux]
    exact hp u hnew ⟨t, htx.trans hux.symm⟩
  obtain ⟨l, hul, hur⟩ := tag_interval_of_not_residual e.dust p.2.val u hnewB hnew
  have holdB : p.1.val.1 t ∈ d.dust := htx ▸ hxB
  by_cases hold : t ∈ residualTimes d.dust p.1.val
  · exact (hxS (htx ▸ hr t hold l u hul hur (hux.trans htx.symm))).elim
  obtain ⟨k, htl, htr⟩ := tag_interval_of_not_residual d.dust p.1.val t holdB hold
  exact (ht k l t u htl htr hul hur ⟨holdB, htx ▸ hxS⟩ (hux.trans htx.symm)).elim


end CircleDomainRigidity

end

end OAI
