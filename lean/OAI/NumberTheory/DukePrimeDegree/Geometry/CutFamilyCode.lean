import OAI.NumberTheory.DukePrimeDegree.Entropy.LayeredObservations

namespace OAI

/-! # Finite integer codes for families of real cuts -/

noncomputable section
open MeasureTheory
namespace DukePrimeDegree

def finiteCutCode {Y : Type*} {N : ℕ} (f : Fin N → Y → ℝ) (c : Fin N → ℝ)
    (x : Y) : Fin (Fintype.card (Fin N → Bool)) :=
  Fintype.equivFin (Fin N → Bool) (fun i => decide (f i x < c i))

lemma finiteCutCode_measurable {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    {f : Fin N → Y → ℝ} (hf : ∀ i, Measurable (f i)) (c : Fin N → ℝ) :
    Measurable (finiteCutCode f c) := by
  apply (measurable_of_finite (Fintype.equivFin (Fin N → Bool))).comp
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_bool
  have he : (fun x => decide (f i x < c i)) ⁻¹' {true} = {x | f i x < c i} := by
    ext x
    simp
  rw [he]
  exact measurableSet_lt (hf i) measurable_const

lemma finiteCutCode_eq_of_iff {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (h : ∀ i, f i y < c i ↔ f i x < c i) : finiteCutCode f c y=finiteCutCode f c x := by
  apply congrArg (Fintype.equivFin (Fin N → Bool))
  funext i
  simp only [h i]

lemma finiteCutCode_eq_imp_iff {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (h : finiteCutCode f c y=finiteCutCode f c x) (i : Fin N) :
    f i y < c i ↔ f i x < c i := by
  have he := congrFun ((Fintype.equivFin (Fin N → Bool)).injective h) i
  constructor
  · intro hy
    have hx : decide (f i x < c i)=true := by
      rw [←he]
      exact decide_eq_true hy
    exact of_decide_eq_true hx
  · intro hx
    have hy : decide (f i y < c i)=true := by
      rw [he]
      exact decide_eq_true hx
    exact of_decide_eq_true hy

end DukePrimeDegree

end

end OAI
