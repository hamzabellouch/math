import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Module.End

namespace Problem315.InvariantEnergyVariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [sectionFiniteDimensionalℝE : FiniteDimensional ℝ E]

theorem spectral_projection_mem (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (U : Submodule ℝ E) (hU : ∀ x ∈ U, T x ∈ U)
    (μ : ℝ) {x : E} (hx : x ∈ U) :
    (eigenspace T μ).starProjection x ∈ U := by
  let A := T.restrict hU
  have hA : A.IsSymmetric := hT.restrict_invariant hU
  let b := hA.eigenvectorBasis (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  let ev := hA.eigenvalues (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  have hbeigen (i : Fin (Module.finrank ℝ U)) :
      T (b i : E) = ev i • (b i : E) := by
    exact congrArg Subtype.val (hA.apply_eigenvectorBasis rfl i)
  have hbproj (i : Fin (Module.finrank ℝ U)) :
      (eigenspace T μ).starProjection (b i : E) ∈ U := by
    by_cases hi : ev i = μ
    · have hmem : (b i : E) ∈ eigenspace T μ := by
        rw [mem_eigenspace_iff, hbeigen, hi]
      rw [Submodule.starProjection_eq_self_iff.mpr hmem]
      exact (b i).property
    · have hmem : (b i : E) ∈ eigenspace T (ev i) :=
        mem_eigenspace_iff.mpr (hbeigen i)
      have horth : (b i : E) ∈ (eigenspace T μ)ᗮ :=
        hT.orthogonalFamily_eigenspaces.isOrtho hi hmem
      rw [(Submodule.starProjection_apply_eq_zero_iff (eigenspace T μ)).mpr horth]
      exact U.zero_mem
  have hdecomp := congrArg (fun z : U => (z : E)) (b.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hdecomp
  rw [← hdecomp, map_sum]
  apply U.sum_mem
  intro i hi
  rw [map_smul]
  exact U.smul_mem _ (hbproj i)

include sectionFiniteDimensionalℝE in
theorem eigenvalue_pos (T : E →ₗ[ℝ] E)
    (hpos : ∀ x : E, x ≠ 0 → 0 < inner ℝ x (T x)) (μ : Eigenvalues T) :
    0 < (μ : ℝ) := by
  have retainedsectionFiniteDimensionalℝE := sectionFiniteDimensionalℝE
  obtain ⟨x, hx, hx0⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
    (show HasEigenvalue T (μ : ℝ) from μ.property)
  have h := hpos x hx0
  rw [mem_eigenspace_iff] at hx
  rw [hx, inner_smul_right, real_inner_self_eq_norm_sq] at h
  exact pos_of_mul_pos_left h (sq_nonneg ‖x‖)

theorem norm_sq_eq_sum_spectral (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (x : E) :
    ‖x‖ ^ 2 = ∑ μ : Eigenvalues T, ‖(eigenspace T (μ : ℝ)).starProjection x‖ ^ 2 := by
  have hspan : (⨆ μ : Eigenvalues T, eigenspace T (μ : ℝ)) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hT.orthogonalComplement_iSup_eigenspaces_eq_bot'
  have hsum : (∑ μ : Eigenvalues T, (eigenspace T (μ : ℝ)).starProjection x) = x :=
    hT.orthogonalFamily_eigenspaces'.sum_projection_of_mem_iSup x (by rw [hspan]; trivial)
  calc
    ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
    _ = ∑ μ : Eigenvalues T, inner ℝ x ((eigenspace T (μ : ℝ)).starProjection x) := by
      rw [← inner_sum, hsum]
    _ = ∑ μ : Eigenvalues T, ‖(eigenspace T (μ : ℝ)).starProjection x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro μ hμ
      have h := Submodule.starProjection_inner_eq_zero
        (K := eigenspace T (μ : ℝ)) x
        ((eigenspace T (μ : ℝ)).starProjection x)
        (Submodule.starProjection_apply_mem _ x)
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
      exact sub_eq_zero.mp h

theorem norm_sum_sq_le_of_energy {ι : Type*} [Fintype ι]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hpos : ∀ x : E, x ≠ 0 → 0 < inner ℝ x (T x))
    (U : ι → Submodule ℝ E) (hU : ∀ i x, x ∈ U i → T x ∈ U i)
    (C : ℝ)
    (henergy : ∀ f : ι → E, (∀ i, f i ∈ U i) →
      inner ℝ (∑ i, f i) (T (∑ i, f i)) ≤
        C * ∑ i, inner ℝ (f i) (T (f i)))
    (f : ι → E) (hf : ∀ i, f i ∈ U i) :
    ‖∑ i, f i‖ ^ 2 ≤ C * ∑ i, ‖f i‖ ^ 2 := by
  classical
  let P (μ : Eigenvalues T) := (eigenspace T (μ : ℝ)).starProjection
  have hbound (μ : Eigenvalues T) :
      ‖∑ i, P μ (f i)‖ ^ 2 ≤ C * ∑ i, ‖P μ (f i)‖ ^ 2 := by
    have hp (i : ι) : T (P μ (f i)) = (μ : ℝ) • P μ (f i) := by
      exact mem_eigenspace_iff.mp (Submodule.starProjection_apply_mem _ _)
    have hs : T (∑ i, P μ (f i)) = (μ : ℝ) • ∑ i, P μ (f i) := by
      simp only [map_sum, hp, Finset.smul_sum]
    have hmem (i : ι) : P μ (f i) ∈ U i :=
      spectral_projection_mem T hT (U i) (hU i) (μ : ℝ) (hf i)
    apply (mul_le_mul_iff_right₀ (eigenvalue_pos T hpos μ)).mp
    calc
      (μ : ℝ) * ‖∑ i, P μ (f i)‖ ^ 2 =
          inner ℝ (∑ i, P μ (f i)) (T (∑ i, P μ (f i))) := by
        rw [hs, inner_smul_right, real_inner_self_eq_norm_sq]
      _ ≤ C * ∑ i, inner ℝ (P μ (f i)) (T (P μ (f i))) :=
        henergy (fun i => P μ (f i)) hmem
      _ = (μ : ℝ) * (C * ∑ i, ‖P μ (f i)‖ ^ 2) := by
        simp_rw [hp, inner_smul_right, real_inner_self_eq_norm_sq]
        rw [← Finset.mul_sum]
        ring
  calc
    ‖∑ i, f i‖ ^ 2 = ∑ μ : Eigenvalues T, ‖P μ (∑ i, f i)‖ ^ 2 :=
      norm_sq_eq_sum_spectral T hT _
    _ = ∑ μ : Eigenvalues T, ‖∑ i, P μ (f i)‖ ^ 2 := by
      simp only [map_sum]
    _ ≤ ∑ μ : Eigenvalues T, C * ∑ i, ‖P μ (f i)‖ ^ 2 :=
      Finset.sum_le_sum fun μ _ => hbound μ
    _ = C * ∑ i, ‖f i‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (norm_sq_eq_sum_spectral T hT (f i)).symm

include sectionFiniteDimensionalℝE in
theorem eigenvalue_nonneg (T : E →ₗ[ℝ] E)
    (hpos : ∀ x : E, 0 ≤ inner ℝ x (T x)) (μ : Eigenvalues T) :
    0 ≤ (μ : ℝ) := by
  have retainedsectionFiniteDimensionalℝE := sectionFiniteDimensionalℝE
  obtain ⟨x, hx, hx0⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
    (show HasEigenvalue T (μ : ℝ) from μ.property)
  have h := hpos x
  rw [mem_eigenspace_iff] at hx
  rw [hx, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx0)
  by_contra hneg
  have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hn
  linarith

theorem norm_sum_sq_le_of_energy_ker_orthogonal {ι : Type*} [Fintype ι]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ inner ℝ x (T x))
    (U : ι → Submodule ℝ E) (hU : ∀ i x, x ∈ U i → T x ∈ U i)
    (C : ℝ)
    (henergy : ∀ f : ι → E, (∀ i, f i ∈ U i) →
      inner ℝ (∑ i, f i) (T (∑ i, f i)) ≤
        C * ∑ i, inner ℝ (f i) (T (f i)))
    (f : ι → E) (hf : ∀ i, f i ∈ U i)
    (hker : ∀ i z, T z = 0 → inner ℝ z (f i) = 0) :
    ‖∑ i, f i‖ ^ 2 ≤ C * ∑ i, ‖f i‖ ^ 2 := by
  classical
  let P (μ : Eigenvalues T) := (eigenspace T (μ : ℝ)).starProjection
  have hbound (μ : Eigenvalues T) :
      ‖∑ i, P μ (f i)‖ ^ 2 ≤ C * ∑ i, ‖P μ (f i)‖ ^ 2 := by
    by_cases hzero : (μ : ℝ) = 0
    · have hpzero (i : ι) : P μ (f i) = 0 := by
        apply (Submodule.starProjection_apply_eq_zero_iff (eigenspace T (μ : ℝ))).mpr
        intro z hz
        apply hker i z
        rw [mem_eigenspace_iff] at hz
        simpa [hzero] using hz
      simp [hpzero]
    have hp (i : ι) : T (P μ (f i)) = (μ : ℝ) • P μ (f i) := by
      exact mem_eigenspace_iff.mp (Submodule.starProjection_apply_mem _ _)
    have hs : T (∑ i, P μ (f i)) = (μ : ℝ) • ∑ i, P μ (f i) := by
      simp only [map_sum, hp, Finset.smul_sum]
    have hmem (i : ι) : P μ (f i) ∈ U i :=
      spectral_projection_mem T hT (U i) (hU i) (μ : ℝ) (hf i)
    have hμ : 0 < (μ : ℝ) := lt_of_le_of_ne (eigenvalue_nonneg T hpos μ) (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ hμ).mp
    calc
      (μ : ℝ) * ‖∑ i, P μ (f i)‖ ^ 2 =
          inner ℝ (∑ i, P μ (f i)) (T (∑ i, P μ (f i))) := by
        rw [hs, inner_smul_right, real_inner_self_eq_norm_sq]
      _ ≤ C * ∑ i, inner ℝ (P μ (f i)) (T (P μ (f i))) :=
        henergy (fun i => P μ (f i)) hmem
      _ = (μ : ℝ) * (C * ∑ i, ‖P μ (f i)‖ ^ 2) := by
        simp_rw [hp, inner_smul_right, real_inner_self_eq_norm_sq]
        rw [← Finset.mul_sum]
        ring
  calc
    ‖∑ i, f i‖ ^ 2 = ∑ μ : Eigenvalues T, ‖P μ (∑ i, f i)‖ ^ 2 :=
      norm_sq_eq_sum_spectral T hT _
    _ = ∑ μ : Eigenvalues T, ‖∑ i, P μ (f i)‖ ^ 2 := by
      simp only [map_sum]
    _ ≤ ∑ μ : Eigenvalues T, C * ∑ i, ‖P μ (f i)‖ ^ 2 :=
      Finset.sum_le_sum fun μ _ => hbound μ
    _ = C * ∑ i, ‖f i‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (norm_sq_eq_sum_spectral T hT (f i)).symm

end Problem315.InvariantEnergyVariance

end

end OAI
