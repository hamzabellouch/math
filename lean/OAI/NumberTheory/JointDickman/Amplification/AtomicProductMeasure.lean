import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductMeasure

namespace OAI

/-! # Exact finite atomic expansions of product measures -/
namespace JointDickman
open Finset MeasureTheory
open scoped NNReal ENNReal

noncomputable def finitePointMeasure {Ω : Type*} [MeasurableSpace Ω] (t : Ω) : FiniteMeasure Ω :=
  ⟨Measure.dirac t, inferInstance⟩

open Classical in
theorem finitePointMeasure_apply {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (t : Ω) (s : Set Ω) : finitePointMeasure t s = if t ∈ s then 1 else 0 := by
  by_cases h : t ∈ s <;> simp [finitePointMeasure, Measure.dirac_apply, h]

theorem finiteMeasure_sum_apply {Ω β : Type*} [MeasurableSpace Ω]
    (P : Finset β) (μ : β → FiniteMeasure Ω) (s : Set Ω) :
    (∑ p ∈ P, μ p) s = ∑ p ∈ P, μ p s := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih => simp only [sum_insert hp, FiniteMeasure.coeFn_add, Pi.add_apply, ih]

noncomputable def finiteAtomicMeasure (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ P, w p • finitePointMeasure (f p)

noncomputable def atomicTupleMeasure (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (h : ℕ) :
    FiniteMeasure (Fin h → ℝ) :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
    (∏ i, w (v i)) • finitePointMeasure (fun i => f (v i))

open Classical in
theorem finiteAtomicMeasure_apply (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (s : Set ℝ) :
    finiteAtomicMeasure P w f s = ∑ p ∈ P, if f p ∈ s then w p else 0 := by
  rw [finiteAtomicMeasure, finiteMeasure_sum_apply]
  apply sum_congr rfl
  intro p hp
  rw [FiniteMeasure.smul_apply, smul_eq_mul, finitePointMeasure_apply]
  split_ifs <;> simp

open Classical in
theorem atomicTupleMeasure_apply (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ)
    (h : ℕ) (s : Set (Fin h → ℝ)) :
    atomicTupleMeasure P w f h s = ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
      if (fun i => f (v i)) ∈ s then ∏ i, w (v i) else 0 := by
  rw [atomicTupleMeasure, finiteMeasure_sum_apply]
  apply sum_congr rfl
  intro v hv
  rw [FiniteMeasure.smul_apply, smul_eq_mul, finitePointMeasure_apply]
  split_ifs <;> simp

theorem finiteAtomicMeasure_pi (P : Finset ℕ) (w : ℕ → ℝ≥0) (f : ℕ → ℝ) (h : ℕ) :
    FiniteMeasure.pi (fun _ : Fin h => finiteAtomicMeasure P w f) = atomicTupleMeasure P w f h := by
  classical
  apply FiniteMeasure.toMeasure_injective
  apply Measure.pi_eq
  intro s hs
  have he : atomicTupleMeasure P w f h (Set.pi Set.univ s) =
      ∏ i, finiteAtomicMeasure P w f (s i) := by
    rw [atomicTupleMeasure_apply]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    calc
      _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin h => P),
          ∏ i, if f (v i) ∈ s i then w (v i) else 0 := by
        apply sum_congr rfl
        intro v hv
        rw [Fintype.prod_ite_zero]
        split_ifs <;> rfl
      _ = ∏ i : Fin h, ∑ p ∈ P, if f p ∈ s i then w p else 0 :=
        by
          symm
          rw [prod_univ_sum]
      _ = _ := by simp only [finiteAtomicMeasure_apply]
  simp only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast he

end JointDickman

end OAI
