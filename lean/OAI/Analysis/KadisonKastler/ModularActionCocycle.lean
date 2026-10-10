import OAI.Analysis.KadisonKastler.RegularCoreRepresentation

namespace OAI

/-! # Unitary cocycles between represented modular actions

These are the cocycles occurring in the change-of-state theorem. The
construction of a cocycle from two faithful states is a separate step.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ModularActionCocycle (M : VonNeumannAlgebra H)
    (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)) where
  value : Multiplicative ℝ → unitary (H →L[ℂ] H)
  mem : ∀ s, (value s : H →L[ℂ] H) ∈ M
  continuous : ∀ x, Continuous (fun t : ℝ => (value (Multiplicative.ofAdd t) : H →L[ℂ] H) x)
  continuous_star : ∀ x, Continuous
    (fun t : ℝ => (star (value (Multiplicative.ofAdd t)) : H →L[ℂ] H) x)
  value_mul : ∀ s t, (value (s * t) : H →L[ℂ] H) =
    (value s : H →L[ℂ] H) * unitaryConj (U s) (value t : H →L[ℂ] H)
  action : ∀ s a, a ∈ M → unitaryConj (V s) a =
    unitaryConj (value s) (unitaryConj (U s) a)

namespace ModularActionCocycle

variable {M : VonNeumannAlgebra H}
  {U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)}
  (c : ModularActionCocycle M U V)

private theorem star_unitaryConj (u : unitary (H →L[ℂ] H)) (a : H →L[ℂ] H) :
    star (unitaryConj u a) = unitaryConj u (star a) := by
  simp only [unitaryConj, star_mul, star_star, mul_assoc]

def symm : ModularActionCocycle M V U where
  value s := star (c.value s)
  mem s := star_mem (c.mem s)
  continuous := c.continuous_star
  continuous_star x := by simpa only [Unitary.coe_star, star_star] using c.continuous x
  value_mul s t := by
    have h := congrArg star (c.value_mul s t)
    rw [star_mul, star_unitaryConj] at h
    change star (c.value (s * t) : H →L[ℂ] H) =
      star (c.value s : H →L[ℂ] H) * unitaryConj (V s) (star (c.value t : H →L[ℂ] H))
    rw [c.action s _ (star_mem (c.mem t)), h]
    simp only [unitaryConj, ← mul_assoc,
      Unitary.star_mul_self_of_mem (c.value s).property, one_mul]
  action s a ha := by
    have h := congrArg (unitaryConj (star (c.value s))) (c.action s a ha)
    rw [unitaryConj_star_unitaryConj] at h
    exact h.symm

def regularField (t : ℝ) : unitary (H →L[ℂ] H) :=
  c.value (Multiplicative.ofAdd (-t))

theorem regularField_measurable (x : H) :
    AEStronglyMeasurable (fun t => (c.regularField t : H →L[ℂ] H) x) volume :=
  ((c.continuous x).comp continuous_neg).aestronglyMeasurable

theorem regularField_star_measurable (x : H) :
    AEStronglyMeasurable (fun t => (star (c.regularField t) : H →L[ℂ] H) x) volume :=
  ((c.continuous_star x).comp continuous_neg).aestronglyMeasurable

theorem regularField_embedding (t : ℝ) (a : H →L[ℂ] H) (ha : a ∈ M) :
    (c.regularField t : H →L[ℂ] H) *
        unitaryConj (star (U (Multiplicative.ofAdd t))) a =
      unitaryConj (star (V (Multiplicative.ofAdd t))) a *
        (c.regularField t : H →L[ℂ] H) := by
  rw [regularGroup_star_eq, regularGroup_star_eq]
  rw [c.action _ a ha]
  simp only [regularField, unitaryConj, mul_assoc,
    Unitary.star_mul_self_of_mem (c.value (Multiplicative.ofAdd (-t))).property, mul_one]

theorem regularField_translation (s t : ℝ) :
    (c.regularField t : H →L[ℂ] H) =
      unitaryConj (star (V (Multiplicative.ofAdd t)))
        (star (c.value (Multiplicative.ofAdd (-s)) : H →L[ℂ] H)) *
      (c.regularField (t + s) : H →L[ℂ] H) := by
  rw [regularGroup_star_eq, c.action _ _ (star_mem (c.mem _))]
  have he : Multiplicative.ofAdd (-(t + s)) =
      Multiplicative.ofAdd (-t) * Multiplicative.ofAdd (-s) := by
    change -(t + s) = -t + -s
    ring
  change _ = _ * (c.value (Multiplicative.ofAdd (-(t + s))) : H →L[ℂ] H)
  rw [he, c.value_mul]
  have hcancel (u : unitary (H →L[ℂ] H)) (a : H →L[ℂ] H) :
      star (u : H →L[ℂ] H) * ((u : H →L[ℂ] H) * a) = a := by
    rw [← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]
  simp only [regularField, unitaryConj, mul_assoc, hcancel,
    Unitary.mul_star_self_of_mem (U (Multiplicative.ofAdd (-t))).property, mul_one]

end ModularActionCocycle

end

end KadisonKastler

end OAI
