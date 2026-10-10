import OAI.Analysis.CircleDomains.Probability.HitFusionTree
import OAI.Analysis.CircleDomains.Selection.FiniteSupBound
import OAI.Analysis.CircleDomains.Sobolev.ConfigurationHitIntegral

namespace OAI

/-! Uniform upper bounds on a closed child control every continuation of a
fusion branch. The weighted sum of these bounds is the original split bound. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity
namespace HitFusionSplit

variable {X Z : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MetricSpace Z] [SecondCountableTopology Z]
  {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}
  {A : ClosedHitCandidate law C} {n : ℕ} {r ε η : ℝ}
  (S : HitFusionSplit law C A n r ε η)

def hitCap (a : ℕ) (p : HitConfiguration X n r) : ℝ :=
  sSup ((fun z => weightedConfigurationHits law z p) '' (S.child (S.index a)).carrier)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem hitCap_bddAbove (a : ℕ) (p : HitConfiguration X n r) :
    BddAbove ((fun z => weightedConfigurationHits law z p) ''
      (S.child (S.index a)).carrier) :=
  ⟨n, by rintro _ ⟨z, _, rfl⟩; exact weightedConfigurationHits_le_card law z p⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem le_hitCap (a : ℕ) (p : HitConfiguration X n r) {z : Z}
    (hz : z ∈ (S.child (S.index a)).carrier) :
    weightedConfigurationHits law z p ≤ S.hitCap a p :=
  le_csSup (S.hitCap_bddAbove a p) ⟨z, hz, rfl⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem hitCap_nonneg (a : ℕ) (p : HitConfiguration X n r) : 0 ≤ S.hitCap a p := by
  obtain ⟨z, hz⟩ := (S.child (S.index a)).nonempty
  exact (weightedConfigurationHits_nonneg law z p).trans (S.le_hitCap a p hz)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem hitCap_le_card (a : ℕ) (p : HitConfiguration X n r) : S.hitCap a p ≤ n := by
  apply csSup_le ((S.child (S.index a)).nonempty.image _)
  rintro _ ⟨z, _, rfl⟩
  exact weightedConfigurationHits_le_card law z p

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem weighted_hitCap_le (p : HitConfiguration X n r) :
    ∑ i : Fin S.count, S.weight i * S.hitCap i.val p ≤ C + ε := by
  have h := finite_weighted_sup_le (fun i => (S.child i).carrier)
    (fun _ z => weightedConfigurationHits law z p) S.weight
    (fun i => (S.child i).nonempty) S.weight_nonneg S.weight_sum
    (fun z hz => (S.bound z hz p).le)
  simpa only [hitCap, index_val] using h

end HitFusionSplit
end CircleDomainRigidity

end

end OAI
