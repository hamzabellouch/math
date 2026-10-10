import OAI.Analysis.HyperbolicCones.PencilTopology

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u v

namespace Paper256.FiniteMatrix

theorem sym_neg_norm_le {ι : Type u} [Fintype ι] [DecidableEq ι] (X : selfAdjoint (Matrix ι ι ℝ)) :
    -(‖(X : Matrix ι ι ℝ)‖) • (1 : Matrix ι ι ℝ) ≤ (X : Matrix ι ι ℝ) := by
  classical
  rcases isEmpty_or_nonempty (ι) with h | h
  · have := h
    exact (Subsingleton.elim _ _).le
  · have := h
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (algebraMap_le_iff_le_spectrum (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
    intro x hx
    have hh := spectrum.norm_le_norm_of_mem hx
    have hl := neg_abs_le x
    simpa only [Real.norm_eq_abs] using le_trans (neg_le_neg hh) hl

theorem sym_le_norm {ι : Type u} [Fintype ι] [DecidableEq ι] (X : selfAdjoint (Matrix ι ι ℝ)) :
    (X : Matrix ι ι ℝ) ≤ ‖(X : Matrix ι ι ℝ)‖ • (1 : Matrix ι ι ℝ) := by
  classical
  rcases isEmpty_or_nonempty (ι) with h | h
  · have := h
    exact (Subsingleton.elim _ _).le
  · have := h
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (le_algebraMap_iff_spectrum_le (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
    intro x hx
    exact (le_abs_self x).trans (spectrum.norm_le_norm_of_mem hx)

theorem posDef_of_scalar_lower_bound {ι : Type u} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (hX : c • (1 : Matrix ι ι ℝ) ≤ X) : X.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef hX
  simpa only [add_sub_cancel] using h

theorem posDef_scalar_lower_bound {ι : Type u} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ) (hX : X.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Matrix ι ι ℝ) ≤ X := by
  classical
  rcases isEmpty_or_nonempty (ι) with h | h
  · have := h
    exact ⟨1, zero_lt_one, (Subsingleton.elim _ _).le⟩
  · have := h
    have hh := (CFC.exists_pos_algebraMap_le_iff X hX.isHermitian).mpr
      (fun x hx => by
        rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hX.eigenvalues_pos i)
    simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem isOpen_posDef (ι : Type u) [Fintype ι] [DecidableEq ι] : IsOpen {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosDef} := by
  apply Metric.isOpen_iff.mpr
  intro H hH
  obtain ⟨c, hc, hbound⟩ := posDef_scalar_lower_bound (H : Matrix ι ι ℝ) hH
  refine ⟨c / 2, by positivity, ?_⟩
  intro X hX
  have hnorm : ‖((X - H : selfAdjoint (Matrix ι ι ℝ)) : Matrix ι ι ℝ)‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, AddSubgroup.coe_norm] using hX
  have hlower : -(c / 2) • (1 : Matrix ι ι ℝ) ≤ ((X - H : selfAdjoint (Matrix ι ι ℝ)) : Matrix ι ι ℝ) :=
    (smul_le_smul_of_nonneg_right (by linarith : -(c / 2) ≤ -‖((X - H : selfAdjoint (Matrix ι ι ℝ)) : Matrix ι ι ℝ)‖)
      Matrix.PosSemidef.one.nonneg).trans (sym_neg_norm_le (X - H))
  apply posDef_of_scalar_lower_bound (show 0 < c / 2 by positivity)
  have hh : c • (1 : Matrix ι ι ℝ) + -(c / 2) • (1 : Matrix ι ι ℝ) ≤
      (H : Matrix ι ι ℝ) + ((X : Matrix ι ι ℝ) - (H : Matrix ι ι ℝ)) := add_le_add hbound hlower
  convert hh using 1 <;> module

def quadraticEvaluation {ι : Type u} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) : selfAdjoint (Matrix ι ι ℝ) →ₗ[ℝ] ℝ where
  toFun X := v ⬝ᵥ ((X : Matrix ι ι ℝ) *ᵥ v)
  map_add' X Y := by simp [add_mulVec, dotProduct_add]
  map_smul' c X := by simp [smul_mulVec, dotProduct_smul]

theorem isClosed_posSemidef (ι : Type u) [Fintype ι] [DecidableEq ι] : IsClosed {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosSemidef} := by
  have : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
    FiniteDimensional.finiteDimensional_submodule
      (selfAdjoint.submodule ℝ (Matrix ι ι ℝ))
  have heq : {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosSemidef} =
      ⋂ v : ι → ℝ, {X | 0 ≤ quadraticEvaluation v X} := by
    ext X
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h.dotProduct_mulVec_nonneg v
    · intro h
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg X.property
      intro v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    (quadraticEvaluation v).continuous_of_finiteDimensional

theorem posSemidef_of_tendsto {α : Type u} {f : Filter α} [f.NeBot] {ι : Type v} [Fintype ι] [DecidableEq ι]
    {A : α → selfAdjoint (Matrix ι ι ℝ)} {H : selfAdjoint (Matrix ι ι ℝ)} (hA : Tendsto A f (𝓝 H))
    (h : ∀ᶠ x in f, (A x : Matrix ι ι ℝ).PosSemidef) : (H : Matrix ι ι ℝ).PosSemidef :=
  (isClosed_posSemidef ι).mem_of_tendsto hA h


end Paper256.FiniteMatrix

end

end OAI
