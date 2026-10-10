import Mathlib

namespace OAI

namespace Balanced.VacantBins

open scoped BigOperators

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

noncomputable def missed (f : I → A) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => ∀ i, f i ≠ a)

noncomputable def missedCount (f : I → A) : ℕ := (missed f).card

omit [DecidableEq I] in
@[simp] theorem mem_missed (f : I → A) (a : A) :
    a ∈ missed f ↔ ∀ i, f i ≠ a := by
  classical
  simp [missed]

def avoidingEquiv (a : A) :
    {f : I → A // ∀ i, f i ≠ a} ≃ (I → {b : A // b ≠ a}) where
  toFun f i := ⟨f.val i, f.property i⟩
  invFun f := ⟨fun i => (f i).val, fun i => (f i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_avoiding (a : A) :
    Fintype.card {f : I → A // ∀ i, f i ≠ a} =
      (Fintype.card A - 1) ^ Fintype.card I := by
  classical
  rw [Fintype.card_congr (avoidingEquiv (I := I) a), Fintype.card_fun]
  congr 1
  simp

theorem sum_missedCount :
    (∑ f : I → A, missedCount f) =
      Fintype.card A * (Fintype.card A - 1) ^ Fintype.card I := by
  classical
  have hcount (f : I → A) :
      missedCount f = ∑ a : A, if (∀ i, f i ≠ a) then 1 else 0 := by
    simp [missedCount, missed]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  have havoid (a : A) :
      (∑ f : I → A, if (∀ i, f i ≠ a) then 1 else 0) =
        (Fintype.card A - 1) ^ Fintype.card I := by
    simpa [Fintype.card_subtype] using card_avoiding (I := I) a
  simp_rw [havoid]
  simp

noncomputable def uniformMean (Y : (I → A) → ℝ) : ℝ :=
  (∑ f : I → A, Y f) / Fintype.card (I → A)

omit [DecidableEq A] in
theorem uniformMean_equiv {B : Type*} [Fintype B] [DecidableEq B]
    (e : (I → A) ≃ (I → B)) (Y : (I → B) → ℝ) :
    uniformMean (fun f : I → A => Y (e f)) = uniformMean Y := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_missedCount [Nonempty A] :
    uniformMean (fun f : I → A => (missedCount f : ℝ)) =
      (Fintype.card A : ℝ) *
        (1 - 1 / (Fintype.card A : ℝ)) ^ Fintype.card I := by
  classical
  have hq : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr inferInstance
  have hq0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card A ≠ 0)
  have hsum : (∑ f : I → A, (missedCount f : ℝ)) =
      (Fintype.card A : ℝ) *
        ((Fintype.card A : ℝ) - 1) ^ Fintype.card I := by
    have h := sum_missedCount (I := I) (A := A)
    exact_mod_cast h
  unfold uniformMean
  rw [hsum, Fintype.card_fun, Nat.cast_pow]
  rw [show (1 : ℝ) - 1 / (Fintype.card A : ℝ) =
      ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ) by
    field_simp]
  rw [div_pow]
  ring

theorem integral_uniform_eq_uniformMean [Nonempty A]
    [MeasurableSpace (I → A)] [MeasurableSingletonClass (I → A)]
    (Y : (I → A) → ℝ) :
    (∫ f, Y f ∂(PMF.uniformOfFintype (I → A)).toMeasure) = uniformMean Y := by
  classical
  rw [MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite)]
  have hmass (f : I → A) :
      (PMF.uniformOfFintype (I → A)).toMeasure.real {f} =
        (Fintype.card (I → A) : ℝ)⁻¹ := by
    simp [MeasureTheory.measureReal_def]
  simp_rw [hmass, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp [uniformMean, div_eq_mul_inv, mul_comm]

theorem integral_missedCount [Nonempty A]
    [MeasurableSpace (I → A)] [MeasurableSingletonClass (I → A)] :
    (∫ f : I → A, (missedCount f : ℝ)
      ∂(PMF.uniformOfFintype (I → A)).toMeasure) =
      (Fintype.card A : ℝ) *
        (1 - 1 / (Fintype.card A : ℝ)) ^ Fintype.card I := by
  rw [integral_uniform_eq_uniformMean, uniformMean_missedCount]

theorem missedCount_le_add_one_of_eq_off (f g : I → A) (j : I)
    (hfg : ∀ i, i ≠ j → f i = g i) :
    missedCount f ≤ missedCount g + 1 := by
  classical
  have hsub : missed f ⊆ insert (g j) (missed g) := by
    intro a ha
    by_cases hag : a = g j
    · simp [hag]
    · apply Finset.mem_insert_of_mem
      rw [mem_missed] at ha ⊢
      intro i
      by_cases hij : i = j
      · simpa [hij, eq_comm] using hag
      · simpa [hfg i hij] using ha i
  calc
    missedCount f ≤ (insert (g j) (missed g)).card := Finset.card_le_card hsub
    _ ≤ missedCount g + 1 := Finset.card_insert_le _ _

theorem abs_missedCount_sub_le_one (f g : I → A) (j : I)
    (hfg : ∀ i, i ≠ j → f i = g i) :
    |(missedCount f : ℝ) - (missedCount g : ℝ)| ≤ 1 := by
  have h₁ := missedCount_le_add_one_of_eq_off f g j hfg
  have h₂ := missedCount_le_add_one_of_eq_off g f j
    (fun i hi => (hfg i hi).symm)
  have h₁R : (missedCount f : ℝ) ≤ (missedCount g : ℝ) + 1 := by
    exact_mod_cast h₁
  have h₂R : (missedCount g : ℝ) ≤ (missedCount f : ℝ) + 1 := by
    exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

end Balanced.VacantBins

end OAI
