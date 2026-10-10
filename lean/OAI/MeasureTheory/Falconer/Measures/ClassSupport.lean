import OAI.MeasureTheory.Falconer.Estimates.RegularClasses

namespace OAI

/-! # Original support and occupied anchors of the normalized classes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem ae_occupied_anchors (Q : DyadicCube d) (ρ : Measure (Space d)) :
    ∀ᵐ x ∂ρ, ∀ P : List (Fin d → Bool), x ∈ (Q.descendant P).carrier →
      0 < ρ (Q.descendant P).carrier := by
  apply ae_all_iff.mpr
  intro P
  by_cases hp : 0 < ρ (Q.descendant P).carrier
  · exact Filter.Eventually.of_forall (fun _ _ => hp)
  · have hz : ρ (Q.descendant P).carrier = 0 := le_antisymm (not_lt.mp hp) (by positivity)
    have he : ∀ᵐ x ∂ρ, x ∉ (Q.descendant P).carrier := ae_iff.mpr (by simpa using hz)
    filter_upwards [he] with x hx
    exact fun hp => (hx hp).elim

namespace Regularization

 theorem normalizedClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    normalizedClass Q μ L f T ≪ μ :=
  Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

 theorem sourceClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : sourceClass Q μ N B p ≪ μ :=
  normalizedClass_absolutelyContinuous Q μ _ _ _

 theorem normalizedClass_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    normalizedClass Q μ L f T Q.carrierᶜ = 0 := by
  rw [normalizedClass_apply]
  have he : Q.carrierᶜ ∩ leafUnion Q (classLeaves L f T) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

 theorem sourceClass_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (p : CellPath d) :
    sourceClass Q μ N B p Q.carrierᶜ = 0 :=
  normalizedClass_parent Q hQ μ _ _ _

end Regularization
end Falconer

end OAI
