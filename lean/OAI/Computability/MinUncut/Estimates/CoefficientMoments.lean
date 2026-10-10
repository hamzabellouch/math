import Mathlib
import OAI.Computability.MinUncut.PCP.SelectionSequence
import OAI.Computability.MinUncut.Games.HintSimulation

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {I : Type*} [Fintype I]

def coefficientVectors (q : ℕ) : HintCoefficients I q →ₗ[F₂] (I → Fin q → F₂) where
  toFun c i k := (c k).2.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] in
lemma coefficientVectors_surjective (q : ℕ) : Function.Surjective (coefficientVectors (I := I) q) := by
  intro v
  exact ⟨fun k => (0,(fun i => v i k,fun _ => 0)),rfl⟩

def Active {q : ℕ} (hidden : I → Bool) (v : I → Fin q → F₂) (i : I) : Prop :=
  hidden i=true ∧ v i=0

def hintRate (q : ℕ) : ℝ := 1-(1/(2:ℝ)^q)*(1-repetitionRate)

lemma active_power_product {q : ℕ} (hidden : I → Bool) (v : I → Fin q → F₂) (r : ℝ) :
    r ^ Fintype.card {i // Active hidden v i} =
      ∏ i, if hidden i=true ∧ v i=0 then r else 1 := by
  classical
  rw [Fintype.card_subtype (Active hidden v),← Finset.prod_const,Finset.prod_filter]
  simp only [Active]
  congr 1
  funext i
  split_ifs with h
  · exact ite_eq_left h
  · exact ite_eq_right h

lemma zero_vector_expect (q : ℕ) (r : ℝ) :
    (𝔼 v : Fin q → F₂, if v=0 then r else 1) = 1-(1/(2:ℝ)^q)*(1-r) := by
  classical
  have hpoint (v : Fin q → F₂) : (if v=0 then r else (1:ℝ)) =
      1+(r-1)*(if v=0 then 1 else 0) := by split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const]
  have hz : (𝔼 v : Fin q → F₂, if v=0 then (1:ℝ) else 0) = 1/(2:ℝ)^q := by
    simp [F₂]
  rw [hz]
  ring

lemma active_power_expect (q : ℕ) (hidden : I → Bool) :
    (𝔼 v : I → Fin q → F₂, repetitionRate ^ Fintype.card {i // Active hidden v i}) =
      hintRate q ^ Fintype.card {i // hidden i=true} := by
  classical
  simp_rw [active_power_product]
  rw [OuterSmoothness.expect_prod (fun i (v : Fin q → F₂) =>
    if hidden i=true ∧ v=0 then repetitionRate else 1)]
  have h j : (𝔼 v : Fin q → F₂,
      if hidden j=true ∧ v=0 then repetitionRate else 1) =
      if hidden j=true then hintRate q else 1 := by
    by_cases hj : hidden j=true
    · simp only [hj,true_and,↓reduceIte]
      exact zero_vector_expect q repetitionRate
    · simp [hj]
  simp_rw [h]
  rw [Fintype.card_subtype (fun i => hidden i=true),← Finset.prod_const,Finset.prod_filter]

lemma coefficient_active_expect (q : ℕ) (hidden : I → Bool) :
    (𝔼 c : HintCoefficients I q,
      repetitionRate ^ Fintype.card {i // Active hidden (coefficientVectors q c) i}) =
      hintRate q ^ Fintype.card {i // hidden i=true} := by
  exact (IndependentSquares.expect_surjective_linear (coefficientVectors q)
    (coefficientVectors_surjective q) (fun v =>
      repetitionRate ^ Fintype.card {i // Active hidden v i})).trans
    (active_power_expect q hidden)

lemma hintRate_nonnegative (q : ℕ) : 0 ≤ hintRate q := by
  have hp : (1 : ℝ) ≤ 2^q := one_le_pow₀ (by norm_num)
  have hd : 0 ≤ 1/(2:ℝ)^q := by positivity
  have hd' : 1/(2:ℝ)^q ≤ 1 := (div_le_one (by positivity)).2 hp
  have hr := repetitionRate_pos.le
  have hr' := repetitionRate_lt_one.le
  unfold hintRate
  nlinarith

lemma hintRate_lt_one (q : ℕ) : hintRate q<1 := by
  unfold hintRate
  have h : 0<(1/(2:ℝ)^q)*(1-repetitionRate) :=
    mul_pos (by positivity) (sub_pos.mpr repetitionRate_lt_one)
  linarith

end MinUncut.Outer

end
end

end OAI
