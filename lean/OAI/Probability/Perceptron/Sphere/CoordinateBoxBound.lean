import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma box_coordinate_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {F : (I → ℝ) → ℝ} {L : I → ℝ} {a b : ℝ}
    (hderiv : ∀ u : I → ℝ, (∀ i, u i ∈ Icc a b) → ∀ j,
      ∃ D : ℝ, HasDerivAt (fun r => F (u+Pi.single j r)) D 0 ∧ |D| ≤ L j)
    {u : I → ℝ} (hu : ∀ i, u i ∈ Icc a b) (j : I)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |F (Function.update u j y)-F (Function.update u j x)| ≤ L j*|y-x| := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      ∃ D : ℝ, HasDerivAt (fun r => F (Function.update u j r)) D s ∧ |D| ≤ L j := by
    have huw : ∀ i, Function.update u j s i ∈ Icc a b := by
      intro i
      by_cases hi : i=j
      · subst i; simpa using hs
      · simpa [Function.update_of_ne hi] using hu i
    obtain ⟨D,hD,hDb⟩ := hderiv (Function.update u j s) huw j
    refine ⟨D,?_,hDb⟩
    have hsub : HasDerivAt (fun r : ℝ => r-s) 1 s := (hasDerivAt_id s).sub_const s
    have hc := hD.comp_of_eq s hsub (sub_self s).symm
    simp only [mul_one] at hc
    apply hc.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro r
    change F (Function.update u j r) = F (Function.update u j s + Pi.single j (r-s))
    congr 1
    funext i
    by_cases hi : i=j
    · subst i
      simp
    · simp [Function.update_of_ne hi,Pi.single_eq_of_ne hi]
  let D := fun s => if hs : s ∈ Icc a b then (hd s hs).choose else 0
  have hD (s) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun r => F (Function.update u j r)) (D s) (Icc a b) s := by
    dsimp [D]
    rw [dite_eq_left hs]
    exact (hd s hs).choose_spec.1.hasDerivWithinAt
  have hDb (s) (hs : s ∈ Icc a b) : ‖D s‖ ≤ L j := by
    dsimp [D]
    rw [dite_eq_left hs]
    exact (hd s hs).choose_spec.2
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hDb (convex_Icc a b) hx hy

lemma box_sum_coordinate_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {F : (I → ℝ) → ℝ} {L : I → ℝ} {a b : ℝ}
    (hderiv : ∀ u : I → ℝ, (∀ i, u i ∈ Icc a b) → ∀ j,
      ∃ D : ℝ, HasDerivAt (fun r => F (u+Pi.single j r)) D 0 ∧ |D| ≤ L j)
    {u v : I → ℝ} (hu : ∀ i, u i ∈ Icc a b) (hv : ∀ i, v i ∈ Icc a b) :
    |F v-F u| ≤ ∑ j, L j*|v j-u j| := by
  let w := fun s : Finset I => fun i => if i ∈ s then v i else u i
  have hw (s : Finset I) (i : I) : w s i ∈ Icc a b := by
    dsimp [w]
    split_ifs
    · exact hv i
    · exact hu i
  have hh (s : Finset I) : |F (w s)-F u| ≤ ∑ j ∈ s, L j*|v j-u j| := by
    induction s using Finset.induction_on with
    | empty => simp [w]
    | @insert j s hj ih =>
      have h0 : Function.update (w s) j (u j)=w s := by
        funext i
        by_cases hi : i=j
        · subst i; simp [w,hj]
        · simp [Function.update_of_ne hi]
      have h1 : Function.update (w s) j (v j)=w (insert j s) := by
        funext i
        by_cases hi : i=j
        · subst i; simp [w]
        · simp [w,hi]
      have hc := box_coordinate_comparison hderiv (hw s) j (hu j) (hv j)
      rw [h0,h1] at hc
      rw [Finset.sum_insert hj]
      exact (abs_sub_le (F (w (insert j s))) (F (w s)) (F u)).trans (add_le_add hc ih)
  simpa [w] using hh Finset.univ

end SphericalPerceptronFreeEnergy
end

end OAI
