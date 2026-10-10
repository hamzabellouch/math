import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformConditioning
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformProducts

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniformUpdates

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws CompletionProductLaws DualUniformConditioning DualUniformProducts
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

theorem conditionalCompletionLaw_uniform_independent
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (P : X → Prop)
    (hu : UniformCoordinate (colorMix S center output pc po α hα hα'.le)
      (fun a => a.val.1) P)
    (hi : ∀ x c,
      ((colorMix S center output pc po α hα hα'.le).map
        (fun a => (a.val.1, leafColor S a))).mass (x,c) =
      ((colorMix S center output pc po α hα hα'.le).map (fun a => a.val.1)).mass x *
      ((colorMix S center output pc po α hα hα'.le).map (leafColor S)).mass c) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1) (fun x => ∀ i, P (x i)) := by
  let p := iidColorLaw S center output pc po m α hα hα'.le
  let f : (Fin m → Leaf S) → (Fin m → X) := fun w i => (w i).val.1
  let g : (Fin m → Leaf S) → (Fin m → Color) := fun w i => leafColor S (w i)
  let Q : (Fin m → Color) → Prop := fun w =>
    raisedFlag center output (fun i => w i = output) ∧
      ∀ i, w i = center ∨ w i = output
  have hprod : UniformCoordinate p f (fun x => ∀ i, P (x i)) :=
    independentProduct_uniformCoordinate
      (fun _ : Fin m => colorMix S center output pc po α hα hα'.le)
      (fun _ a => a.val.1) (fun _ => P) (fun _ => hu)
  have hind : ∀ x c, (p.map (fun a => (f a, g a))).mass (x,c) =
      (p.map f).mass x * (p.map g).mass c :=
    independentProduct_independent
      (fun _ : Fin m => colorMix S center output pc po α hα hα'.le)
      (fun _ a => a.val.1) (fun _ => leafColor S) (fun _ => hi)
  have hcond := uniform_coordinate_independent_condition p f g
    (fun x => ∀ i, P (x i)) Q hprod hind
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  intro x
  rw [conditionalCompletionLaw_X_mass]
  exact hcond x

theorem conditionalCompletionLaw_uniform_incident
    (S : FlaggedTensor X Y Z) (center output : Color)
    (hc : center = .B ∨ output = .B)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (hu : UniformCoordinate (colorMix S center output pc po α hα hα'.le)
      (fun a => a.val.1) (fun _ => True)) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1)
      (fun x => if output = .B then (complete S center m).flagB x
        else ¬ (complete S center m).flagB x) := by
  let p := iidColorLaw S center output pc po m α hα hα'.le
  let f : (Fin m → Leaf S) → (Fin m → X) := fun w i => (w i).val.1
  let Q : (Fin m → X) → Prop := fun x => if output = .B then
    (complete S center m).flagB x else ¬ (complete S center m).flagB x
  have hprod : UniformCoordinate p f (fun _ => True) := by
    apply uniform_coordinate_pred_congr p f (fun x => ∀ _i : Fin m, True)
      (fun _ => True) (fun _ => by simp)
    exact independentProduct_uniformCoordinate
      (fun _ : Fin m => colorMix S center output pc po α hα hα'.le)
      (fun _ a => a.val.1) (fun _ _ => True) (fun _ => hu)
  have heq : ∀ w, p.mass w ≠ 0 →
      (completionEvent S center output m w ↔ Q (f w)) := by
    intro w hw
    have ha := iidColorLaw_allowed S center output pc po m α hα hα'.le w hw
    by_cases ho : output = .B
    · subst output
      simpa only [Q, f, ite_eq_left rfl, ite_true] using completionEvent_outputB S center m w ha
    · have hcenter : center = .B := hc.resolve_right ho
      subst center
      simpa only [Q, f, ite_eq_right ho] using completionEvent_centerB S output ho m w ha
  have hcond := uniform_coordinate_condition_supported p f (fun _ => True) Q
    (completionEvent S center output m) hprod heq
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  have hcond' := uniform_coordinate_pred_congr _ _ (fun x => True ∧ Q x) Q
    (fun _ => ⟨And.right, fun h => ⟨True.intro, h⟩⟩) hcond
  intro x
  rw [conditionalCompletionLaw_X_mass]
  exact hcond' x

end MatrixMultiplication.DualUniformUpdates

end

end OAI
