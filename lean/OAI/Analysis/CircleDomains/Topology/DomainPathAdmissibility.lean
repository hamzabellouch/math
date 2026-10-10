import OAI.Analysis.CircleDomains.Selection.TagDelay

namespace OAI

/-! Every path of finite physical length which stays off the dust is
allowed with inactive tags, for every residual measure and tuple exclusion. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem residualTimes_empty_of_avoids {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) : residualTimes B Γ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact h t ht.1

theorem residualImage_empty_of_avoids {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) : residualImage B Γ = ∅ := by
  rw [residualImage, residualTimes_empty_of_avoids h, image_empty]

theorem residualIncidence_empty_of_avoids {Z : Type*} [TopologicalSpace Z]
    {B : Set X} {Γ : TaggedPath X} (h : ∀ t, Γ.1 t ∉ B)
    (I : Set PathTime) (R : Set (Z × X)) (P : Set X) :
    {z | (Γ, z) ∈ residualIncidence B I R P} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨t, ht, _⟩
  rw [residualTimes_empty_of_avoids h] at ht
  exact ht

theorem residualConstraintFamily_of_avoids {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞) :
    ResidualConstraintFamily B R P ν m Γ := by
  intro i n a b
  unfold ResidualIncidenceBound
  rw [residualIncidence_empty_of_avoids h, measure_empty]
  exact bot_le

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_of_avoids (d : PathCodeData X Y)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (havoid : ∀ t, γ t ∉ d.dust) : AllowedTaggedPath d ν N (γ, fun _ => inactiveTag) := by
  refine ⟨hfin, ?_, ?_, ?_, ?_⟩
  · intro k
    exact inactiveTag_rules d.levels N γ
  · exact residualConstraintFamily_of_avoids havoid _ _ _ _
  · exact residualConstraintFamily_of_avoids havoid _ _ _ _
  · rw [residualImage_empty_of_avoids havoid, measure_empty]

theorem domainPath_allowed (d : PathCodeData X Y)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (hγ : ∀ t, γ t ∈ d.quotientDomain) : AllowedTaggedPath d ν N (γ, fun _ => inactiveTag) :=
  allowedTaggedPath_of_avoids d ν N γ hfin
    (fun t ht => Set.disjoint_left.mp hdisj (hγ t) ht)

end CircleDomainRigidity

end

end OAI
