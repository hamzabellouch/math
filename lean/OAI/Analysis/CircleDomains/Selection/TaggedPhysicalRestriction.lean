import OAI.Analysis.CircleDomains.Modulus.RestrictedFragmentCosts
import OAI.Analysis.CircleDomains.Topology.AllowedPathRestriction

namespace OAI

/-! Actual affine restrictions of tagged finite-physical paths, retaining
all the tag and physical-cost information used by the collar fragments. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def restrictTaggedPhysicalPath (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : TaggedPhysicalPath d) {a b : PathTime} (hab : a < b) : TaggedPhysicalPath d :=
  (affineFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 hab,
    fun k => affineRestrictedTag a b Γ.1.val (Γ.2 k))

omit [MeasurableSpace X] in
@[simp] theorem restrictTaggedPhysicalPath_zero (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (Γ : TaggedPhysicalPath d)
    {a b : PathTime} (hab : a < b) :
    (restrictTaggedPhysicalPath d hU Γ hab).1.val ⊥ = Γ.1.val a := by
  change Γ.1.val (affinePathTime a b ⊥) = _
  rw [affinePathTime_zero]

omit [MeasurableSpace X] in
@[simp] theorem restrictTaggedPhysicalPath_one (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (Γ : TaggedPhysicalPath d)
    {a b : PathTime} (hab : a < b) :
    (restrictTaggedPhysicalPath d hU Γ hab).1.val ⊤ = Γ.1.val b := by
  change Γ.1.val (affinePathTime a b ⊤) = _
  rw [affinePathTime_one]

omit [MeasurableSpace X] in
theorem restrictTaggedPhysicalPath_range (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (Γ : TaggedPhysicalPath d)
    {a b : PathTime} (hab : a < b) :
    range (restrictTaggedPhysicalPath d hU Γ hab).1.val = Γ.1.val '' Icc a b := by
  change range (Γ.1.val ∘ affinePathTime a b) = _
  rw [range_comp, range_affinePathTime hab]

variable [MeasurableSingletonClass X]

theorem restrictTaggedPhysicalPath_allowed (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {a b : PathTime} (hab : a < b) :
    AllowedTaggedPath d ν N ((restrictTaggedPhysicalPath d hU Γ hab).1.val,
      (restrictTaggedPhysicalPath d hU Γ hab).2) :=
  allowedTaggedPath_affine d hU ν N (Γ.1.val, Γ.2) hΓ hpoint hab

end CircleDomainRigidity

end

end OAI
