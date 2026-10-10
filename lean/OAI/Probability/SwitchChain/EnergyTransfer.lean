import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.EnergyTransfer

theorem norm_sq_le_of_intertwining_energy_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (J : E →ₗ[ℝ] E) (K : F →ₗ[ℝ] F)
    (hJ : ∀ x : E, x ≠ 0 → 0 < ⟪x, J x⟫)
    (hinter : ∀ x : E, K (A x) = A (J x))
    (c : ℝ) (henergy : ∀ x : E, ⟪A x, K (A x)⟫ ≤ c * ⟪x, J x⟫)
    (x : E) : ‖A x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
  classical
  let B : E →ₗ[ℝ] E := A.adjoint.comp A
  have hB : B.IsSymmetric := A.isPositive_adjoint_comp_self.isSymmetric
  let b := hB.eigenvectorBasis rfl
  let ev := hB.eigenvalues rfl
  have hbe (i : Fin (Module.finrank ℝ E)) : B (b i) = ev i • b i :=
    hB.apply_eigenvectorBasis rfl i
  have hev (i : Fin (Module.finrank ℝ E)) : ev i ≤ c := by
    have he := henergy (b i)
    rw [hinter] at he
    have hid : ⟪A (b i), A (J (b i))⟫ = ⟪B (b i), J (b i)⟫ :=
      (A.adjoint_inner_left (J (b i)) (A (b i))).symm
    rw [hid, hbe, inner_smul_left] at he
    simp only [RCLike.conj_to_real] at he
    have hp : 0 < ⟪b i, J (b i)⟫ := hJ (b i) (b.toBasis.ne_zero i)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm] using he)
  have hnorm : ‖A x‖ ^ 2 = ⟪x, B x⟫ := by
    change ‖A x‖ ^ 2 = ⟪x, A.adjoint (A x)⟫
    rw [A.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hnorm, ← b.sum_sq_inner_right x, Finset.mul_sum,
    ← b.sum_inner_mul_inner x (B x)]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪b i, B x⟫ = ev i * ⟪b i, x⟫ := by
    rw [← hB (b i) x, hbe, inner_smul_left]
    simp
  rw [hcoord, real_inner_comm x (b i)]
  nlinarith [mul_le_mul_of_nonneg_right (hev i) (sq_nonneg ⟪x, b i⟫)]

theorem norm_sum_sq_le_of_invariant_energy_bound
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V : ι → Submodule ℝ E) (J : E →ₗ[ℝ] E)
    (hinv : ∀ i x, x ∈ V i → J x ∈ V i)
    (hpos : ∀ i x, x ∈ V i → x ≠ 0 → 0 < ⟪x, J x⟫)
    (c : ℝ)
    (henergy : ∀ f : ι → E, (∀ i, f i ∈ V i) →
      ⟪∑ i, f i, J (∑ i, f i)⟫ ≤ c * ∑ i, ⟪f i, J (f i)⟫)
    (f : ι → E) (hf : ∀ i, f i ∈ V i) :
    ‖∑ i, f i‖ ^ 2 ≤ c * ∑ i, ‖f i‖ ^ 2 := by
  classical
  let D := PiLp 2 (fun i => V i)
  let A : D →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, (x i : E)
      map_add' := by intro x y; simp [D, Finset.sum_add_distrib]
      map_smul' := by intro r x; simp [D, Finset.smul_sum] }
  let L : D →ₗ[ℝ] D :=
    { toFun := fun x => WithLp.toLp 2 (fun i => ⟨J (x i), hinv i _ (x i).property⟩)
      map_add' := by intro x y; ext i; simp [D]
      map_smul' := by intro r x; ext i; simp [D] }
  have hL (x : D) (hx : x ≠ 0) : 0 < ⟪x, L x⟫ := by
    have hnonneg (i : ι) : 0 ≤ ⟪(x i : E), J (x i)⟫ := by
      by_cases hz : (x i : E) = 0
      · simp [hz]
      · exact (hpos i _ (x i).property hz).le
    have hex : ∃ i, (x i : E) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      ext i
      exact hn i
    obtain ⟨i, hi⟩ := hex
    change 0 < ∑ j, ⟪(x j : E), J (x j)⟫
    exact Finset.sum_pos' (fun j _ => hnonneg j)
      ⟨i, Finset.mem_univ i, hpos i _ (x i).property hi⟩
  have hinter (x : D) : J (A x) = A (L x) := by
    change J (∑ i, (x i : E)) = ∑ i, J (x i)
    exact map_sum J _ _
  have hEn (x : D) : ⟪A x, J (A x)⟫ ≤ c * ⟪x, L x⟫ := by
    exact henergy (fun i => (x i : E)) (fun i => (x i).property)
  have h := norm_sq_le_of_intertwining_energy_bound A L J hL hinter c hEn
    (WithLp.toLp 2 (fun i => (⟨f i, hf i⟩ : V i)))
  simpa [D, A, PiLp.norm_sq_eq_of_L2] using h

end Problem315.EnergyTransfer

end

end OAI
