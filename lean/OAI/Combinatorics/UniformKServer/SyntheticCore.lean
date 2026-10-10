import Mathlib

namespace OAI

                                    
section

/-! Common-core preparation in the adaptive allocation update, companion
 eqs. synthetic-core-input and synthetic-core-errors. All input probabilities
 here are the NEW posteriors, including when used with the old flags. -/
namespace UniformKServer.SyntheticCore
noncomputable section
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def input (p : κ → ℝ) (f : κ → Bool) : ℝ := ∑ j, if f j then p j else 0

def changes (f g : κ → Bool) : ℝ := ∑ j, if f j=g j then 0 else 1

theorem input_nonneg {p : κ → ℝ} (hp : ∀ j, 0 ≤ p j) (f : κ → Bool) : 0 ≤ input p f := by
  apply sum_nonneg
  intro j _
  split_ifs
  · exact hp j
  · rfl

theorem changes_nonneg (f g : κ → Bool) : 0 ≤ changes f g := by
  apply sum_nonneg
  intro j _
  split_ifs <;> norm_num

theorem no_flags (p : κ → ℝ) {f : κ → Bool} (hf : ∀ j, f j=false) : input p f=0 := by
  simp only [input,hf,Bool.false_eq_true,ite_false,sum_const_zero]

theorem input_difference (p : κ → ℝ) (f g : κ → Bool) (hp : ∀ j, p j ∈ Set.Icc (0:ℝ) 1) :
    |input p f-input p g| ≤ changes f g := by
  unfold input changes
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rcases hp j with ⟨h₀,h₁⟩
  cases hf : f j <;> cases hg : g j <;> simp [abs_of_nonneg h₀,abs_neg,h₁]

def core (old new : ι → Bool) (p : ι → κ → ℝ) (f : ι → κ → Bool) (i : ι) : ℝ :=
  if old i && new i then input (p i) (f i) else 0

/-- Inactivity entails an empty core, not merely a zero observed value. -/
def Supported (active : ι → Bool) (flag : ι → κ → Bool) : Prop :=
  ∀ i, active i=false → ∀ j, flag i j=false

omit [Fintype ι] in
theorem core_le_new (old new : ι → Bool) (p : ι → κ → ℝ) (g : ι → κ → Bool)
    (hp : ∀ i j, 0 ≤ p i j) (i : ι) :
    0 ≤ core old new p g i ∧ core old new p g i ≤ input (p i) (g i) := by
  unfold core
  split_ifs
  · exact ⟨input_nonneg (hp i) _,le_rfl⟩
  · exact ⟨le_rfl,input_nonneg (hp i) _⟩

omit [Fintype ι] in
theorem old_core_difference (old new : ι → Bool) (p : ι → κ → ℝ)
    (f g : ι → κ → Bool) (hp : ∀ i j, p i j ∈ Set.Icc (0:ℝ) 1)
    (hf : Supported old f) (hg : Supported new g) (i : ι) :
    |input (p i) (f i)-core old new p g i| ≤ changes (f i) (g i) := by
  have hn := changes_nonneg (f i) (g i)
  have hb := input_difference (p i) (f i) (g i) (hp i)
  cases ho : old i <;> cases hn' : new i
  · simp only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false,sub_zero]
    rw [no_flags _ (hf i ho),abs_zero]
    exact hn
  · simp only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false,sub_zero]
    rw [no_flags _ (hf i ho),abs_zero]
    exact hn
  · simpa only [core,ho,hn',Bool.true_and,Bool.false_eq_true,ite_false,
      no_flags _ (hg i hn')] using hb
  · simpa only [core,ho,hn',Bool.true_and,ite_true] using hb

omit [Fintype ι] in
theorem new_core_difference (old new : ι → Bool) (p : ι → κ → ℝ)
    (f g : ι → κ → Bool) (hp : ∀ i j, p i j ∈ Set.Icc (0:ℝ) 1)
    (hf : Supported old f) (hg : Supported new g) (i : ι) :
    |input (p i) (g i)-core old new p g i| ≤ changes (f i) (g i) := by
  have hn := changes_nonneg (f i) (g i)
  have hb := input_difference (p i) (f i) (g i) (hp i)
  cases ho : old i <;> cases hn' : new i
  · simp only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false,sub_zero]
    rw [no_flags _ (hg i hn'),abs_zero]
    exact hn
  · rw [no_flags _ (hf i ho),zero_sub,abs_neg] at hb
    simpa only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false,sub_zero] using hb
  · simp only [core,ho,hn',Bool.true_and,Bool.false_eq_true,ite_false,sub_zero]
    rw [no_flags _ (hg i hn'),abs_zero]
    exact hn
  · simp only [core,ho,hn',Bool.true_and,ite_true,sub_self,abs_zero]
    exact hn

/-- All three source errors, on the fixed child set with zero extension. -/
theorem errors (old new : ι → Bool) (p : ι → κ → ℝ)
    (f g : ι → κ → Bool) (hp : ∀ i j, p i j ∈ Set.Icc (0:ℝ) 1)
    (hf : Supported old f) (hg : Supported new g) :
    (∑ i, |input (p i) (f i)-core old new p g i|) ≤ ∑ i, changes (f i) (g i) ∧
    (∑ i, |input (p i) (g i)-core old new p g i|) ≤ ∑ i, changes (f i) (g i) ∧
    0 ≤ (∑ i, input (p i) (g i))-(∑ i, core old new p g i) ∧
    (∑ i, input (p i) (g i))-(∑ i, core old new p g i) ≤ ∑ i, changes (f i) (g i) := by
  have hn (i : ι) : 0 ≤ input (p i) (g i)-core old new p g i :=
    sub_nonneg.mpr (core_le_new old new p g (fun i j => (hp i j).1) i).2
  have h₁ := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => old_core_difference old new p f g hp hf hg i)
  have h₂ := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => new_core_difference old new p f g hp hf hg i)
  refine ⟨h₁,h₂,?_,?_⟩
  · rw [←sum_sub_distrib]
    exact sum_nonneg fun i _ => hn i
  · simpa only [abs_of_nonneg (hn _),sum_sub_distrib] using h₂

end
end UniformKServer.SyntheticCore

end

end OAI
