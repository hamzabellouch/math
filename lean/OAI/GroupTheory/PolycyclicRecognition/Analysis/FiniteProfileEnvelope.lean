import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace OAI

/-! # Filling the finitely many exceptional profile scales -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal

/-- Eventual uniform control of a finite family can be extended to every
scale without changing the vanishing error sequence on its tail. The size
of the family is allowed to grow with the scale. -/
theorem exists_finite_profile_envelope {J : ℕ → Type*} [∀ n, Fintype (J n)]
    (base : ℕ → ℝ≥0) (err : ∀ n, J n → ℝ≥0) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, (base n : ℝ) ≤ η n)
    (he : ∀ᶠ n in atTop, ∀ j, (err n j : ℝ) ≤ η n) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      (∀ n, η n ≤ ε n) ∧ (∀ n, (base n : ℝ) ≤ ε n) ∧
      (∀ n j, (err n j : ℝ) ≤ ε n) := by
  classical
  let upper := fun n => max (base n) (Finset.univ.sup (err n))
  let ε := fun n => max (η n) (upper n : ℝ)
  have hbase (n) : (base n : ℝ) ≤ ε n :=
    (show (base n : ℝ) ≤ (upper n : ℝ) from
      NNReal.coe_le_coe.mpr (le_max_left _ _)).trans (le_max_right _ _)
  have herr (n) (j : J n) : (err n j : ℝ) ≤ ε n := by
    apply (show (err n j : ℝ) ≤ (upper n : ℝ) from ?_).trans (le_max_right _ _)
    exact NNReal.coe_le_coe.mpr ((Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _))
  have heq : ε =ᶠ[atTop] η := by
    filter_upwards [hb, he] with n hbn hen
    apply max_eq_left
    apply max_le hbn
    have hnonneg : 0 ≤ η n := (base n).coe_nonneg.trans hbn
    exact NNReal.coe_le_coe.mp (Finset.sup_le (fun j _ =>
      show err n j ≤ ⟨η n, hnonneg⟩ from hen j))
  exact ⟨ε, hη.congr' heq.symm, fun _ => le_max_left _ _, hbase, herr⟩

end PolycyclicRecognition

end

end OAI
