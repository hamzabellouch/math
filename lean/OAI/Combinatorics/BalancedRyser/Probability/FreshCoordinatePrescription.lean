import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace OAI

namespace Balanced.FreshCoordinate

noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable

variable {D A : Type*} [DecidableEq D]

def prescriptionEquiv (d : D) (E : (D → A) → Prop) (b : (D → A) → A)
    (hE : ∀ f a, E (Function.update f d a) ↔ E f)
    (hb : ∀ f a, b (Function.update f d a) = b f) :
    {f : D → A // E f} ≃ {f : D → A // E f ∧ f d = b f} × A where
  toFun f := (⟨Function.update f.1 d (b f.1),
    (hE f.1 (b f.1)).mpr f.2, by simp [hb]⟩, f.1 d)
  invFun p := ⟨Function.update p.1.1 d p.2, (hE p.1.1 p.2).mpr p.1.2.1⟩
  left_inv f := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [hb, Function.update_idem]
      rw [← p.1.2.2]
      simp
    · simp

variable [Fintype D] [Fintype A] [Nonempty A]

omit [Nonempty A] in

theorem card_prescription_mul (d : D) (E : (D → A) → Prop) (b : (D → A) → A)
    (hE : ∀ f a, E (Function.update f d a) ↔ E f)
    (hb : ∀ f a, b (Function.update f d a) = b f) :
    Fintype.card {f : D → A // E f ∧ f d = b f} * Fintype.card A =
      Fintype.card {f : D → A // E f} := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr (prescriptionEquiv d E b hE hb)).symm

theorem probability_prescription (d : D) (E : (D → A) → Prop)
    (b : (D → A) → A)
    (hE : ∀ f a, E (Function.update f d a) ↔ E f)
    (hb : ∀ f a, b (Function.update f d a) = b f) :
    ((PMF.uniformOfFintype (D → A)).toOuterMeasure
      {f | E f ∧ f d = b f}).toReal =
    ((PMF.uniformOfFintype (D → A)).toOuterMeasure {f | E f}).toReal /
      Fintype.card A := by
  simp only [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  have hc := card_prescription_mul d E b hE hb
  have hcR : (Fintype.card {f : D → A // E f} : ℝ) =
      Fintype.card {f : D → A // E f ∧ f d = b f} * Fintype.card A := by
    exact_mod_cast hc.symm
  change (Fintype.card {f : D → A // E f ∧ f d = b f} : ℝ) /
      Fintype.card (D → A) =
    (Fintype.card {f : D → A // E f} : ℝ) / Fintype.card (D → A) /
      Fintype.card A
  rw [hcR]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem probability_prescription_on_subtype (d : D)
    (G E : (D → A) → Prop) [Nonempty {f : D → A // G f}]
    (b : (D → A) → A)
    (hG : ∀ f a, G (Function.update f d a) ↔ G f)
    (hE : ∀ f a, E (Function.update f d a) ↔ E f)
    (hb : ∀ f a, b (Function.update f d a) = b f) :
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1 ∧ f.1 d = b f.1}).toReal =
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1}).toReal / Fintype.card A := by
  simp only [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  change (Fintype.card {f : {f : D → A // G f} // E f.1 ∧ f.1 d = b f.1} : ℝ) /
      Fintype.card {f : D → A // G f} =
    (Fintype.card {f : {f : D → A // G f} // E f.1} : ℝ) /
      Fintype.card {f : D → A // G f} / Fintype.card A
  have he : Fintype.card {f : {f : D → A // G f} // E f.1} =
      Fintype.card {f : D → A // G f ∧ E f} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter G E)
  have hp : Fintype.card {f : {f : D → A // G f} // E f.1 ∧ f.1 d = b f.1} =
      Fintype.card {f : D → A // (G f ∧ E f) ∧ f d = b f} := by
    apply Fintype.card_congr
    exact (Equiv.subtypeSubtypeEquivSubtypeInter G
      (fun f => E f ∧ f d = b f)).trans
        (Equiv.subtypeEquivRight fun _ => and_assoc.symm)
  rw [he, hp]
  have hc : Fintype.card {f : D → A // G f ∧ E f} =
      Fintype.card {f : D → A // (G f ∧ E f) ∧ f d = b f} * Fintype.card A := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (prescriptionEquiv d (fun f => G f ∧ E f) b
      (by intro f a; rw [hG, hE]) hb)
  have hcR : (Fintype.card {f : D → A // G f ∧ E f} : ℝ) =
      Fintype.card {f : D → A // (G f ∧ E f) ∧ f d = b f} * Fintype.card A := by
    exact_mod_cast hc
  rw [hcR]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end
end Balanced.FreshCoordinate

end OAI
