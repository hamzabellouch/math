import OAI.Analysis.Cotype.FiniteL2DualNorm

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def momentL2Linear (m : ℕ) : PiLp 2 (fun _ : Cube m => X) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => X) where
  toFun f := toLp 2 (moment X (fun u => f u))
  map_add' f g := by ext i; simp [moment, average, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [moment, average, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ring

theorem moment_norm_le_cubeL2 {m : ℕ} (f : Cube m → X) (i : Fin m) :
    ‖moment X f i‖ ≤ cubeL2 X f := by
  simpa only [vectorWalsh, character_unitIndex, moment] using vectorWalsh_bound f (unitIndex i)

theorem momentL2Linear_bound (m : ℕ) (f : PiLp 2 (fun _ : Cube m => X)) :
    ‖momentL2Linear m f‖ ≤
      (Real.sqrt m * Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)) * ‖f‖ := by
  have h : ‖momentL2Linear m f‖ ≤ Real.sqrt m * cubeL2 X (fun u => f u) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (cubeL2_nonneg _))).mp
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    calc
      _ ≤ ∑ _ : Fin m, cubeL2 X (fun u => f u)^2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (cubeL2_nonneg _)).mpr (moment_norm_le_cubeL2 _ i))
      _ = _ := by simp
  simpa only [cubeL2_eq_piLp, toLp_ofLp, mul_assoc] using h

def momentL2 (m : ℕ) : PiLp 2 (fun _ : Cube m => X) →L[ℝ] PiLp 2 (fun _ : Fin m => X) :=
  (momentL2Linear (X := X) m).mkContinuous
    (Real.sqrt m * Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)) (momentL2Linear_bound m)

@[simp] theorem momentL2_apply (m : ℕ) (f : PiLp 2 (fun _ : Cube m => X)) (i : Fin m) :
    momentL2 m f i = moment X (fun u => f u) i := rfl

theorem momentL2_surjective (m : ℕ) : Function.Surjective (momentL2 (X := X) m) := by
  intro z
  refine ⟨toLp 2 (rademacherSum X (fun i => z i)), ?_⟩
  ext i
  exact moment_rademacherSum X (fun i => z i) i

theorem momentL2_adjoint (m : ℕ) (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ψ.comp (momentL2 m) = (Fintype.card (Cube m) : ℝ)⁻¹ •
      finiteL2Dual (rademacherSum (X →L[ℝ] ℝ) (tupleDualCoordinates ψ)) := by
  ext f
  calc
    ψ (momentL2 m f) = finiteL2Dual (tupleDualCoordinates ψ) (momentL2 m f) :=
      congrArg (fun t : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ => t (momentL2 m f)) (tupleDual_eq ψ)
    _ = _ := by
      simp only [finiteL2Dual_apply, momentL2_apply, moment, average, map_smul, map_sum,
        smul_apply, rademacherSum, sum_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem momentL2_dual_bound {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D)
    (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ‖ψ‖ ≤ (D / Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)) * ‖ψ.comp (momentL2 m)‖ := by
  let q := Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube m))))
  have hq2 : q^2 = (Fintype.card (Cube m) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have h := hD.2 (tupleDualCoordinates ψ)
  have he : Real.sqrt (∑ i, ‖tupleDualCoordinates ψ i‖ ^ 2) = ‖ψ‖ := by
    rw [← tupleDualCoordinates_norm ψ, PiLp.norm_eq_of_L2]
  rw [he, cubeL2_eq_piLp] at h
  rw [momentL2_adjoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube m) : ℝ)⁻¹), finiteL2Dual_norm]
  change ‖ψ‖ ≤ D/q * ((Fintype.card (Cube m) : ℝ)⁻¹ * _)
  rw [← hq2]
  change ‖ψ‖ ≤ D * (q * _) at h
  have heq (N : ℝ) : D / q * (q^2 * N) = D * (q * N) := by field_simp
  rw [heq]
  exact h

theorem exists_L2_moment_lift [CompleteSpace X] {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (x : Fin m → X) :
    ∃ H : Cube m → X, (∀ i, moment X H i = x i) ∧
      cubeL2 X H ≤ 2 * D * Real.sqrt (∑ i, ‖x i‖^2) := by
  let q := Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube m))))
  obtain ⟨P, hP, hn⟩ := quotient_lift_norm_le_two (momentL2 (X := X) m)
    (momentL2_surjective m) (div_pos hDp hq) (momentL2_dual_bound hD)
    (toLp 2 x : PiLp 2 (fun _ : Fin m => X))
  refine ⟨fun u => P u, fun i => congrArg (fun w : PiLp 2 (fun _ : Fin m => X) => w i) hP, ?_⟩
  rw [cubeL2_eq_piLp, toLp_ofLp]
  have hh := mul_le_mul_of_nonneg_left hn hq.le
  change q * ‖P‖ ≤ _
  have he : q * (2 * (D/q) * ‖(toLp 2 x : PiLp 2 (fun _ : Fin m => X))‖) =
      2*D*Real.sqrt (∑ i, ‖x i‖^2) := by
    rw [PiLp.norm_eq_of_L2]
    simp only
    field_simp
  exact hh.trans_eq he

end Cotype

end

end OAI
