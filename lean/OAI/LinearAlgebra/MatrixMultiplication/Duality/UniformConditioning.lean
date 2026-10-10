import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.IndependentConditioning
import OAI.LinearAlgebra.MatrixMultiplication.Duality.EntropyHelpers

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniformConditioning

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws CompletionProductLaws DualEntropyHelpers
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {A : Type*} {X Y Z : Type uCoord} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]

theorem eventMass_congr_support (p : FiniteLaw A) (P Q : A → Prop)
    (h : ∀ a, p.mass a ≠ 0 → (P a ↔ Q a)) : eventMass p P = eventMass p Q := by
  rw [eventMass, eventMass, sum_subtype_indicator, sum_subtype_indicator]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p.mass a = 0
  · simp [ha]
  · rw [h a ha]

theorem condition_map_mass_congr_support (p : FiniteLaw A) (P Q : A → Prop)
    (h : ∀ a, p.mass a ≠ 0 → (P a ↔ Q a))
    (hP : 0 < eventMass p P) (hQ : 0 < eventMass p Q) (f : A → X) (x : X) :
    ((condition p P hP).map (fun a => f a.val)).mass x =
      ((condition p Q hQ).map (fun a => f a.val)).mass x := by
  rw [condition_map_mass, condition_map_mass, eventMass_congr_support p P Q h]
  congr 1
  rw [sum_subtype_indicator P (fun a => if f a = x then p.mass a else 0),
    sum_subtype_indicator Q (fun a => if f a = x then p.mass a else 0)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p.mass a = 0
  · simp [ha]
  · rw [h a ha]

theorem uniform_coordinate_pred_congr (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : ∀ x, P x ↔ Q x) (hp : UniformCoordinate p f P) :
    UniformCoordinate p f Q := by
  have he : P = Q := funext (fun x => propext (h x))
  simpa only [he] using hp

theorem uniform_coordinate_condition_positive (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : UniformCoordinate p f P)
    (hevent : 0 < eventMass p (fun a => Q (f a))) :
    UniformCoordinate (condition p (fun a => Q (f a)) hevent)
      (fun a => f a.val) (fun x => P x ∧ Q x) := by
  have hratio := hevent
  rw [uniform_coordinate_eventMass p f P Q h] at hratio
  have hPQ : 0 < Fintype.card {x // P x ∧ Q x} := by
    by_contra hn
    have hz : Fintype.card {x // P x ∧ Q x} = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hratio
  have hP : 0 < Fintype.card {x // P x} := by
    by_contra hn
    have hz : Fintype.card {x // P x} = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hratio
  exact (uniform_coordinate_condition p f P Q h hP hPQ).choose_spec

theorem uniform_coordinate_condition_supported (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (E : A → Prop) (h : UniformCoordinate p f P)
    (heq : ∀ a, p.mass a ≠ 0 → (E a ↔ Q (f a)))
    (hevent : 0 < eventMass p E) :
    UniformCoordinate (condition p E hevent) (fun a => f a.val)
      (fun x => P x ∧ Q x) := by
  have hQ : 0 < eventMass p (fun a => Q (f a)) := by
    rwa [← eventMass_congr_support p E (fun a => Q (f a)) heq]
  have hu := uniform_coordinate_condition_positive p f P Q h hQ
  intro x
  rw [condition_map_mass_congr_support p E (fun a => Q (f a)) heq hevent hQ]
  exact hu x

theorem conditionalCompletionLaw_X_mass
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (x : Fin m → X) :
    ((conditionalCompletionLaw S center output pc po m hm α hα hα').map
      (fun a => a.val.val.1)).mass x =
    ((condition (iidColorLaw S center output pc po m α hα hα'.le)
      (completionEvent S center output m)
      (completionEvent_mass_pos S center output pc po m hm α hα hα')).map
      (fun w i => (w.val i).val.1)).mass x := by
  unfold conditionalCompletionLaw transport
  rw [map_comp_mass]
  rfl

theorem iidColorLaw_allowed
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (w : Fin m → Leaf S)
    (hw : (iidColorLaw S center output pc po m α hα hα').mass w ≠ 0) :
    ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output := by
  intro i
  by_contra h
  have hc : leafColor S (w i) ≠ center := fun hc => h (Or.inl hc)
  have ho : leafColor S (w i) ≠ output := fun ho => h (Or.inr ho)
  have hz := colorMix_mass_zero S center output pc po α hα hα' (w i) hc ho
  rw [iidColorLaw, independentProduct_mass] at hw
  exact ((Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)) hz

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem completionEvent_outputB (S : FlaggedTensor X Y Z) (center : Color)
    (m : ℕ) (w : Fin m → Leaf S)
    (ha : ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = .B) :
    completionEvent S center .B m w ↔
      (complete S center m).flagB (fun i => (w i).val.1) := by
  have heq : (fun i => leafColor S (w i) = .B) =
      (fun i => S.flagB (w i).val.1) := by
    funext i
    exact propext (leafColor_eq_iff S (w i) .B)
  simp only [completionEvent, ha, forall_true_iff, and_true, heq]
  rfl

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem completionEvent_centerB (S : FlaggedTensor X Y Z) (output : Color)
    (ho : output ≠ .B) (m : ℕ) (w : Fin m → Leaf S)
    (ha : ∀ i, leafColor S (w i) = .B ∨ leafColor S (w i) = output) :
    completionEvent S .B output m w ↔
      ¬ (complete S .B m).flagB (fun i => (w i).val.1) := by
  change (raisedFlag .B output (fun i => leafColor S (w i) = output) ∧ _) ↔
    ¬ raisedFlag .B .B (fun i => S.flagB (w i).val.1)
  simp only [raisedFlag, ite_eq_right ho.symm, ite_true, ha, forall_true_iff, and_true]
  constructor
  · rintro ⟨i, hi⟩ hall
    have hb := (leafColor_eq_iff S (w i) .B).mpr (hall i)
    exact ho (hi.symm.trans hb)
  · intro hn
    obtain ⟨i, hi⟩ := not_forall.mp hn
    refine ⟨i, (ha i).resolve_left ?_⟩
    exact fun hb => hi ((leafColor_eq_iff S (w i) .B).mp hb)

end MatrixMultiplication.DualUniformConditioning

end

end OAI
