import OAI.Analysis.CircleDomains.Topology.BasePathCodes

namespace OAI

/-! Forgetting auxiliary dust and tuple exclusions maps an allowed endpoint
code into the base-code family without changing its path or tags. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem tagTupleExcluded_mono
    {S T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (h : ∀ n l, S n l ⊆ T n l) : tagTupleExcluded S ⊆ tagTupleExcluded T := by
  apply iUnion_mono
  intro n
  apply iUnion_mono
  intro l
  exact image_mono (Set.prod_mono (h n l) Subset.rfl)

theorem tagRules_relax {X : Type*} [MetricSpace X]
    {H : ℕ → Set (UnitAddCircle × X)}
    {S T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (h : ∀ n l, S n l ⊆ T n l) {Γ : TaggedPath X} (hΓ : TagRules H T Γ) :
    TagRules H S Γ := by
  intro k
  exact ⟨(hΓ k).1, (hΓ k).2.1, fun hk => (hΓ k).2.2 (tagTupleExcluded_mono h hk)⟩

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_forget (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {Γ : TaggedPath X} (hΓ : AllowedTaggedPath d ν T Γ) :
    AllowedTaggedPath d 0 (fun _ _ => ∅) Γ := by
  refine ⟨hΓ.1, tagRules_relax (fun _ _ => empty_subset _) hΓ.2.1,
    hΓ.2.2.1, hΓ.2.2.2.1, ?_⟩
  simp

theorem endpointCode_forget (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {Γ : TaggedPath X} (hΓ : EndpointCode d ν T Γ) :
    EndpointCode d 0 (fun _ _ => ∅) Γ :=
  ⟨allowedTaggedPath_forget d ν T hΓ.1, hΓ.2⟩

def forgetCode (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : {Γ : TaggedPath X // EndpointCode d ν T Γ}) : BasePathCode d :=
  ⟨Γ.val, endpointCode_forget d ν T Γ.property⟩

theorem measurable_forgetCode (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)) :
    Measurable (forgetCode d ν T) := measurable_subtype_coe.subtype_mk

end CircleDomainRigidity

end

end OAI
