import Mathlib

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.BinaryLaw

def signedCylinder {I : Type*} (A B : Finset I) : Set (I → Bool) :=
  {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)}

theorem measurableSet_signedCylinder {I : Type*} (A B : Finset I) :
    MeasurableSet (signedCylinder A B) := by
  unfold signedCylinder
  convert (A.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton true)).inter
    (B.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton false)) using 1
  ext x
  simp

theorem measure_ext_of_signed_cylinders {I : Type*} {μ ν : Measure (I → Bool)} [IsFiniteMeasure μ]
    (h : ∀ A B : Finset I,
      μ {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)} =
      ν {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)}) : μ = ν := by
  classical
  let F : (s : Finset I) → Measure (s → Bool) :=
    fun s => μ.map s.restrict
  have hμ : IsProjectiveLimit μ F := fun s => rfl
  have hν : IsProjectiveLimit ν F := by
    intro s
    apply Measure.ext_of_singleton
    intro a
    let f : I → Bool := fun e => if he : e ∈ s then a ⟨e, he⟩ else false
    let A := s.filter (fun e => f e = true)
    let B := s.filter (fun e => f e = false)
    have hset : s.restrict ⁻¹' ({a} : Set (s → Bool)) =
        {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)} := by
      ext x
      change (s.restrict x = a) ↔ _
      constructor
      · intro hx
        constructor
        · intro e he
          obtain ⟨hes, he⟩ := Finset.mem_filter.mp he
          have hx' := congrFun hx (⟨e, hes⟩ : s)
          simpa [f, hes, ← hx'] using he
        · intro e he
          obtain ⟨hes, he⟩ := Finset.mem_filter.mp he
          have hx' := congrFun hx (⟨e, hes⟩ : s)
          simpa [f, hes, ← hx'] using he
      · intro hx
        funext e
        have hf : f e = a e := by simp [f, e.property]
        cases ha : a e
        · exact hx.2 e (Finset.mem_filter.mpr ⟨e.property, hf.trans ha⟩)
        · exact hx.1 e (Finset.mem_filter.mpr ⟨e.property, hf.trans ha⟩)
    change (ν.map s.restrict) {a} = (μ.map s.restrict) {a}
    rw [Measure.map_apply (Finset.measurable_restrict s) (measurableSet_singleton a),
      Measure.map_apply (Finset.measurable_restrict s) (measurableSet_singleton a), hset]
    exact (h A B).symm
  exact hμ.unique hν

theorem measure_ext_of_positive_cylinders {I : Type*} {μ ν : Measure (I → Bool)}
    [IsFiniteMeasure μ]
    (h : ∀ A : Finset I, μ {x | ∀ e ∈ A, x e = true} =
      ν {x | ∀ e ∈ A, x e = true}) : μ = ν := by
  classical
  apply measure_ext_of_signed_cylinders
  intro A B
  change μ (signedCylinder A B) = ν (signedCylinder A B)
  induction B using Finset.induction_on generalizing A with
  | empty => simpa [signedCylinder] using h A
  | @insert e B he ih =>
    have hu : signedCylinder A B =
        signedCylinder (insert e A) B ∪ signedCylinder A (insert e B) := by
      ext x
      simp only [signedCylinder, Set.mem_ofPred_eq, Set.mem_union, Finset.mem_insert,
        forall_eq_or_imp]
      cases x e <;> simp
    have hd : Disjoint (signedCylinder (insert e A) B)
        (signedCylinder A (insert e B)) := by
      rw [Set.disjoint_left]
      intro x hx hy
      have ht := hx.1 e (Finset.mem_insert_self e A)
      have hf := hy.2 e (Finset.mem_insert_self e B)
      exact Bool.noConfusion (ht.symm.trans hf)
    have hsplit (ρ : Measure (I → Bool)) :
        ρ (signedCylinder A B) = ρ (signedCylinder (insert e A) B) +
          ρ (signedCylinder A (insert e B)) := by
      rw [hu, measure_union hd (measurableSet_signedCylinder A (insert e B))]
    have heq := ih A
    rw [hsplit μ, hsplit ν, ← ih (insert e A)] at heq
    exact (ENNReal.add_right_inj (measure_ne_top μ _)).mp heq

end Problem336.BinaryLaw

end

end OAI
