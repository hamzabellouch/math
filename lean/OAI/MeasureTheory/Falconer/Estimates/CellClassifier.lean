import OAI.MeasureTheory.Falconer.Measures.AmbientProduct
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! # Countable Borel labels for the actual endpoint masks

Every descriptor anchored above a fixed depth is constant on that depth's
cells. The label also records points outside the original cube.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

instance cellLabelMeasurableSpace (d : ℕ) : MeasurableSpace (Option (List (Fin d → Bool))) := ⊤

instance cellLabelMeasurableSingletonClass (d : ℕ) :
    MeasurableSingletonClass (Option (List (Fin d → Bool))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

noncomputable def cellLabel (Q : DyadicCube d) (t : ℕ) (x : Space d) :
    Option (List (Fin d → Bool)) :=
  if hx : x ∈ Q.carrier then some (Classical.choose (Q.mem_descendant_at_depth t hx)) else none

theorem cellLabel_eq_some_iff (Q : DyadicCube d) (t : ℕ) (x : Space d)
    (p : List (Fin d → Bool)) :
    cellLabel Q t x = some p ↔ p ∈ cubePaths d t ∧ x ∈ (Q.descendant p).carrier := by
  by_cases hx : x ∈ Q.carrier
  · let q := Classical.choose (Q.mem_descendant_at_depth t hx)
    have hq := Classical.choose_spec (Q.mem_descendant_at_depth t hx)
    change q ∈ cubePaths d t ∧ x ∈ (Q.descendant q).carrier at hq
    simp only [cellLabel,dite_eq_left hx,Option.some.injEq]
    constructor
    · intro he
      change q = p at he
      simpa only [he] using hq
    · rintro ⟨hp,hxp⟩
      change q = p
      by_contra hne
      exact Set.disjoint_left.mp (Q.descendants_disjoint
        (((mem_cubePaths d t q).mp hq.1).trans ((mem_cubePaths d t p).mp hp).symm) hne)
        hq.2 hxp
  · rw [cellLabel,dite_eq_right hx]
    constructor
    · intro he; cases he
    · rintro ⟨_,hp⟩
      exact (hx (Q.descendant_subset p hp)).elim

theorem cellLabel_eq_none_iff (Q : DyadicCube d) (t : ℕ) (x : Space d) :
    cellLabel Q t x = none ↔ x ∉ Q.carrier := by
  by_cases hx : x ∈ Q.carrier <;> simp [cellLabel,hx]

theorem cellLabel_measurable (Q : DyadicCube d) (t : ℕ) : Measurable (cellLabel Q t) := by
  apply measurable_to_countable'
  intro l
  cases l with
  | none =>
    have he : (cellLabel Q t) ⁻¹' {none} = Q.carrierᶜ := by
      ext x
      exact cellLabel_eq_none_iff Q t x
    rw [he]
    exact Q.measurable.compl
  | some p =>
    by_cases hp : p ∈ cubePaths d t
    · have he : (cellLabel Q t) ⁻¹' {some p} = (Q.descendant p).carrier := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,cellLabel_eq_some_iff,hp,true_and]
      rw [he]
      exact (Q.descendant p).measurable
    · have he : (cellLabel Q t) ⁻¹' {some p} = ∅ := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,cellLabel_eq_some_iff,hp,false_and,mem_empty_iff_false]
      rw [he]
      exact MeasurableSet.empty

noncomputable def descriptorClassProduct (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Option (List (Fin d → Bool)) → Space d → ℝ
  | some p => descriptorAmbientProduct Q ρ m N σ J i B S (Q.descendant p).center
  | none => fun _ => if B = ∅ then 1 else 0

theorem descriptorClassProduct_contDiff (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (l : Option (List (Fin d → Bool))) :
    ContDiff ℝ ∞ (descriptorClassProduct Q ρ m N σ J i B S l) := by
  cases l with
  | none => exact contDiff_const
  | some p => exact descriptorAmbientProduct_contDiff Q ρ m N σ J i B S _

theorem descriptorAmbientProduct_eq_class (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i t : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (hB : ∀ b ∈ B, PlanarFalconer.descriptorAnchor b ≤ t)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) :
    descriptorAmbientProduct Q ρ m N σ J i B S x =
      descriptorClassProduct Q ρ m N σ J i B S (cellLabel Q t x) := by
  by_cases hx : x ∈ Q.carrier
  · let p := Classical.choose (Q.mem_descendant_at_depth t hx)
    have hp := Classical.choose_spec (Q.mem_descendant_at_depth t hx)
    have hlen : p.length = t := (mem_cubePaths d t p).mp hp.1
    rw [cellLabel,dite_eq_left hx]
    change _ = descriptorClassProduct Q ρ m N σ J i B S (some p)
    exact descriptorAmbientProduct_reached_on_cell Q hQ ρ m N σ J i B S p
      (fun b hb => by rw [hlen]; exact hB b hb) hp.2
  · rw [show cellLabel Q t x = none from (cellLabel_eq_none_iff Q t x).mpr hx]
    funext z
    simp only [descriptorClassProduct,descriptorAmbientProduct]
    by_cases hB0 : B = ∅
    · simp only [hB0,Finset.prod_empty,ite_true]
    · rw [ite_eq_right hB0]
      obtain ⟨b,hb⟩ := Finset.nonempty_iff_ne_empty.mpr hB0
      apply Finset.prod_eq_zero hb
      exact congrFun (descriptorAmbientMask_off_parent Q ρ m N σ J i b (S b) hx) z

end Falconer

end OAI
