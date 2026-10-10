import OAI.Analysis.MarkovType.FiniteAnnihilator
import OAI.Analysis.MarkovType.FiniteGoldstine
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

structure TriangularArray (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (d ε : ℝ) (M : ℕ) where
  y : Fin M → Y
  f : Fin M → (Y →L[ℝ] ℝ)
  y_norm_le : ∀ j, ‖y j‖ ≤ 1
  f_norm_le : ∀ i, ‖f i‖ ≤ 1
  lower_zero : ∀ i j, j < i → f i (y j) = 0
  upper_close : ∀ i j, i ≤ j → |f i (y j) - d| ≤ ε

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem exists_triangular_array_with_value
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (M : ℕ) :
    ∃ A : TriangularArray Y d ε M, ∀ i, v (A.f i) = d := by
  classical
  induction M with
  | zero =>
      refine ⟨{
        y := Fin.elim0
        f := Fin.elim0
        y_norm_le := fun i => Fin.elim0 i
        f_norm_le := fun i => Fin.elim0 i
        lower_zero := fun i => Fin.elim0 i
        upper_close := fun i => Fin.elim0 i }, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      obtain ⟨A, hA⟩ := ih
      let E : Submodule ℝ Y := Submodule.span ℝ (Set.range A.y)
      let : FiniteDimensional ℝ E :=
        FiniteDimensional.span_of_finite ℝ (Set.finite_range A.y)
      obtain ⟨g, hg, hg_zero, hg_value⟩ :=
        exists_annihilating_functional E v hd hgap
      have hg_y (j : Fin k) : g (A.y j) = 0 :=
        hg_zero ⟨A.y j, Submodule.subset_span ⟨j, rfl⟩⟩
      let f' : Fin (k + 1) → (Y →L[ℝ] ℝ) := Fin.snoc A.f g
      have hf_value (i : Fin (k + 1)) : v (f' i) = d := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [f', Fin.snoc_last] using hg_value
        · simpa only [f', Fin.snoc_castSucc] using hA i
      have hf_norm (i : Fin (k + 1)) : ‖f' i‖ ≤ 1 := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [f', Fin.snoc_last] using hg
        · simpa only [f', Fin.snoc_castSucc] using A.f_norm_le i
      obtain ⟨z, hz_norm, hz_close⟩ := finite_goldstine v hv f' hε
      have hz_d (i : Fin (k + 1)) : |f' i z - d| ≤ ε := by
        rw [← hf_value i]
        exact (hz_close i).le
      let B : TriangularArray Y d ε (k + 1) := {
        y := Fin.snoc A.y z
        f := f'
        y_norm_le := by
          intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · simpa only [Fin.snoc_last] using hz_norm
          · simpa only [Fin.snoc_castSucc] using A.y_norm_le j
        f_norm_le := hf_norm
        lower_zero := by
          intro i j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro h
            exact (not_lt_of_ge (Fin.le_last i) h).elim
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · intro _
              simpa only [f', Fin.snoc_last, Fin.snoc_castSucc] using hg_y j
            · intro h
              simpa only [f', Fin.snoc_castSucc] using A.lower_zero i j h
        upper_close := by
          intro i j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro _
            simpa only [Fin.snoc_last] using hz_d i
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · intro h
              exact (not_le_of_gt (Fin.castSucc_lt_last j) h).elim
            · intro h
              simpa only [f', Fin.snoc_castSucc] using A.upper_close i j h }
      exact ⟨B, hf_value⟩

theorem exists_triangular_array_of_gap
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (M : ℕ) :
    Nonempty (TriangularArray Y d ε M) := by
  obtain ⟨A, _⟩ := exists_triangular_array_with_value v hv hd hε hgap M
  exact ⟨A⟩

theorem exists_uniform_triangular_arrays [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y)) :
    ∃ d : ℝ, 0 < d ∧ ∀ M : ℕ, 0 < M →
      Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M) := by
  obtain ⟨v, d, hv, hd, hgap⟩ := exists_bidual_gap hNR
  refine ⟨d, hd, ?_⟩
  intro M hM
  exact exists_triangular_array_of_gap v hv hd
    (inv_pos.mpr (Nat.cast_pos.mpr hM)) hgap M

end MarkovSuperreflexivity

end

end OAI
