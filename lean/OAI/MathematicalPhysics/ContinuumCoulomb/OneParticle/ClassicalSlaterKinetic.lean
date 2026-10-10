import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalSlater

namespace OAI

/-! Exact kinetic energy of the actual C1 decaying Slater state. The
finite determinant calculation needs L2 classical partials, without a
compact-support restriction on the occupied orbitals. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slaterConfiguration_C1_fderiv {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (s : SpinConfiguration n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (Coulomb.slaterConfiguration v s) x (EuclideanSpace.single (i,b) 1) =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        Coulomb.slotDeterminant (fun a (sx : Fin 2 × Position) => v a sx.2 sx.1)
          (fun a sx => fderiv ℝ (fun y => v a y sx.1) sx.2 (EuclideanSpace.single b 1)) i
          (fun j => (s j, Coulomb.position x j)) := by
  have ht (p : Equiv.Perm (Fin n)) : DifferentiableAt ℝ (Coulomb.tensorOrbital v p s) x :=
    (tensorOrbital_C1 v hv p s).differentiable (by norm_num) x
  rw [Coulomb.slaterConfiguration_expansion, fderiv_const_mul (DifferentiableAt.fun_sum (fun p _ =>
      (ht p).const_mul _)), fderiv_fun_sum (fun p _ => (ht p).const_mul _)]
  simp only [smul_apply, smul_eq_mul, sum_apply,
    fderiv_const_mul (ht _), tensorOrbital_C1_fderiv v hv]
  unfold Coulomb.slotDeterminant
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Coulomb.slotTensor_factor]

theorem classicalSlaterState_cubeGradient {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2)
    (i : Fin n) (b : Fin 3) (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    Coulomb.cubeGradient (classicalSlaterState v hv hL2 hpartial) (i,b) z =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        Coulomb.slotDeterminant (fun a => Coulomb.flatSpinOrbital (v a))
          (fun a => Coulomb.flatSpinOrbital (fun x s =>
            fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1))) i z := by
  change fderiv ℝ (Coulomb.slaterConfiguration v _) _ (EuclideanSpace.single (i,b) 1) = _
  rw [slaterConfiguration_C1_fderiv v hv]
  rfl

theorem classicalSlaterState_kinetic {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2)
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x : Position, star (v i x s) * v j x s) =
      if i = j then (1:ℂ) else 0) :
    Coulomb.kinetic (classicalSlaterState v hv hL2 hpartial) = (1/2:ℝ) * ∑ i, ∑ s, ∑ b : Fin 3,
      ∫ x : Position, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
  have hV (i : Fin n) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume := hL2 i s
  have hD (i : Fin n) (s : Fin 2) (b : Fin 3) :
      MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2 volume := hpartial i s b
  have hO (i j : Fin n) : (∫ a, star (Coulomb.flatSpinOrbital (v i) a) * Coulomb.flatSpinOrbital (v j) a
      ∂Coulomb.spinSpaceMeasure) = if i = j then (1:ℂ) else 0 := by
    rw [Coulomb.flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
    exact ho i j
  have hb (b : Fin 3) : (∑ i, ∑ s, ∫ x, ‖(classicalSlaterState v hv hL2 hpartial).gradient s (i,b) x‖^2) =
      ∑ i, ∑ s, ∫ x : Position,
        ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
    simp_rw [← Coulomb.cubeGradient_full_norm, classicalSlaterState_cubeGradient]
    have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le, integral_const_mul]
    rw [← Finset.mul_sum, Coulomb.slotDeterminant_total_norm_sq _ _
      (fun i => Coulomb.flatSpinOrbital_memLp (v i) (hV i))
      (fun i => Coulomb.flatSpinOrbital_memLp _ (fun s => hD i s b)) hO,
      ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    apply Finset.sum_congr rfl
    intro i _
    have h := Coulomb.flatSpinOrbital_inner
      (fun x s => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1))
      (fun x s => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1))
      (fun s => hD i s b) (fun s => hD i s b)
    have hz (z : ℂ) : star z * z = (↑(‖z‖^2) : ℂ) := by
      rw [mul_comm, Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z
    simp_rw [hz, integral_complex_ofReal] at h
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_sum] using h)
  unfold Coulomb.kinetic
  congr 1
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ b : Fin 3, ∑ i, ∑ s, ∫ x, ‖(classicalSlaterState v hv hL2 hpartial).gradient s (i,b) x‖^2 := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ i, ∑ b : Fin 3, ∑ s, ∫ x, ‖(classicalSlaterState v hv hL2 hpartial).gradient s (i,b) x‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      simp_rw [hb]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

end ContinuumCoulomb

end

end OAI
