import OAI.Analysis.CircleDomains.Modulus.ConcatenatedIncidenceBounds
import OAI.Analysis.CircleDomains.Probability.ConcatenatedResidualNull
import OAI.Analysis.CircleDomains.Topology.BasePathCodes

namespace OAI

/-! A continuous concatenation of countably many allowed paths is allowed
when its remaining parameter times are countable and its physical length is
finite. All tags and incidence estimates are constructed explicitly. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_concatenated [Encodable ι]
    (d : PathCodeData X Y) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfinite : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X) (hΓ : ∀ i, AllowedTaggedPath d ν N (Γ i))
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    AllowedTaggedPath d ν N (concatenatedTaggedPath γ a b Γ) := by
  refine ⟨hfinite, tagRules_concatenated d.levels N γ a b hab Γ hmatch
    (fun i => (hΓ i).2.1), ?_, ?_, ?_⟩
  · apply residualConstraintFamily_concatenated d.dust (fun _ => pathHitSet)
      d.priorDeletions d.priorLaws (fun i => priorHitMass (d.priorLaws i))
      γ a b hab hdis hcount Γ hmatch _ (fun i => (hΓ i).2.2.1)
    intro i x
    exact le_rfl
  · exact residualConstraintFamily_concatenated d.dust d.levels (fun _ => d.flagDeletions)
      (fun _ => volume) d.levelWeights γ a b hab hdis hcount Γ hmatch hpoint
        (fun i => (hΓ i).2.2.2.1)
  · exact residualImage_concatenated_null d.dust ν γ a b hab hdis hcount Γ hmatch
      (fun i => (hΓ i).2.2.2.2)

theorem exists_allowed_countable_concatenation [Countable ι]
    (d : PathCodeData X Y) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfinite : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X) (hΓ : ∀ i, AllowedTaggedPath d ν N (Γ i))
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ θ : ℕ → TagSlot, AllowedTaggedPath d ν N (γ, θ) := by
  let : Encodable ι := Encodable.ofCountable ι
  exact ⟨_, allowedTaggedPath_concatenated d ν N γ hfinite a b hab hdis hcount Γ hΓ hmatch hpoint⟩

end CircleDomainRigidity

end

end OAI
