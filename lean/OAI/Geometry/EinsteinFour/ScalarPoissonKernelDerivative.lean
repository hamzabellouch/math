import OAI.Geometry.EinsteinFour.ScalarPoissonKernelHelmholtz

namespace OAI

/-! Integer Sobolev regularity in four dimensions is characterized by the
four actual distributional coordinate derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

/-- The actual distributional derivative in one Euclidean coordinate. -/
def scalarCoordinateDerivative (i : Fin 4) (u : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} u

private def scalarBesselReciprocal (x : V) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))

private def scalarBesselCoordinate (i : Fin 4) (x : V) : ℂ :=
  Complex.ofReal (x i * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))

private theorem scalarBesselReciprocal_temperate :
    scalarBesselReciprocal.HasTemperateGrowth := by
  unfold scalarBesselReciprocal
  fun_prop

private theorem scalarBesselCoordinate_temperate (i : Fin 4) :
    (scalarBesselCoordinate i).HasTemperateGrowth := by
  unfold scalarBesselCoordinate
  simp_rw [← EuclideanSpace.inner_basisFun_real]
  fun_prop

private theorem scalarBesselReciprocal_bound (x : V) :
    ‖scalarBesselReciprocal x‖ ≤ 1 := by
  rw [scalarBesselReciprocal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖]) (by norm_num)

private theorem scalarBesselCoordinate_bound (i : Fin 4) (x : V) :
    ‖scalarBesselCoordinate i x‖ ≤ 1 := by
  have hρ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        simp
      _ = _ := by simp
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [EuclideanSpace.inner_basisFun_real,
      (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one, mul_one] using
      abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin 4) ℝ i)
  have hxi2 : |x i| ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg (x i)) (norm_nonneg x) |>.mpr hxi]
  apply le_of_sq_le_sq _ zero_le_one
  simp only [scalarBesselCoordinate, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, mul_pow, hρ, one_pow]
  calc
    |x i| ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ ≤
        (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2)⁻¹ := by
      gcongr
    _ = 1 := mul_inv_cancel₀ (by positivity)

private theorem scalarDerivative_fourierMultiplier (i : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i u = (2 * Real.pi * Complex.I) •
      fourierMultiplierCLM ℂ (fun x : V => (x i : ℂ)) u := by
  rw [scalarCoordinateDerivative, lineDeriv_eq_fourierMultiplierCLM]
  congr 2
  ext x
  simp only [EuclideanSpace.inner_basisFun_real]

private theorem scalar_fourierMultiplier_add {g h : V → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(V, ℂ)) :
    fourierMultiplierCLM ℂ (fun x => g x + h x) u =
      fourierMultiplierCLM ℂ g u + fourierMultiplierCLM ℂ h u := by
  simp only [fourierMultiplierCLM_apply, show (fun x => g x + h x) = g + h from rfl,
    smulLeftCLM_add hg hh, add_apply, fourierInv_add]

private theorem scalar_fourierMultiplier_sum (g : Fin 4 → V → ℂ)
    (hg : ∀ i, (g i).HasTemperateGrowth) (u : 𝓢'(V, ℂ)) :
    fourierMultiplierCLM ℂ (fun x => ∑ i, g i x) u =
      ∑ i, fourierMultiplierCLM ℂ (g i) u := by
  have h := congrArg (fun A : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) => A u)
    (fourierMultiplierCLM_sum ℂ (s := Finset.univ) (fun i _ => hg i))
  simpa only [sum_apply] using h

private theorem scalarBessel_coordinate_term (i : Fin 4) (u : 𝓢'(V, ℂ)) :
    (2 * Real.pi * Complex.I)⁻¹ •
      fourierMultiplierCLM ℂ (scalarBesselCoordinate i) (scalarCoordinateDerivative i u) =
    fourierMultiplierCLM ℂ (fun x : V =>
      Complex.ofReal ((x i) ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) u := by
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, OfNat.ofNat_ne_zero,
      Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  rw [scalarDerivative_fourierMultiplier, map_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul,
    fourierMultiplierCLM_fourierMultiplierCLM_apply]
  · apply congrArg (fun f : V → ℂ => fourierMultiplierCLM ℂ f u)
    funext x
    simp only [Pi.mul_apply, scalarBesselCoordinate, ← Complex.ofReal_mul]
    congr 1
    ring
  · simp_rw [← EuclideanSpace.inner_basisFun_real]
    fun_prop
  · exact scalarBesselCoordinate_temperate i

/-- An exact bounded-multiplier reconstruction of one Bessel derivative. -/
theorem scalar_bessel_one_reconstruction (u : 𝓢'(V, ℂ)) :
    besselPotential V ℂ 1 u =
      fourierMultiplierCLM ℂ scalarBesselReciprocal u +
        ∑ i : Fin 4, (2 * Real.pi * Complex.I)⁻¹ •
          fourierMultiplierCLM ℂ (scalarBesselCoordinate i) (scalarCoordinateDerivative i u) := by
  simp_rw [scalarBessel_coordinate_term]
  rw [← scalar_fourierMultiplier_sum _ (by
    intro i
    simp_rw [← EuclideanSpace.inner_basisFun_real]
    fun_prop)]
  rw [← scalar_fourierMultiplier_add scalarBesselReciprocal_temperate (by
    apply Function.HasTemperateGrowth.sum
    intro i _
    simp_rw [← EuclideanSpace.inner_basisFun_real]
    fun_prop)]
  unfold besselPotential
  apply congrArg (fun f : V → ℂ => fourierMultiplierCLM ℂ f u)
  funext x
  have hnorm : ∑ i : Fin 4, (x i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_basisFun_real] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_sq_inner_left x
  simp only [scalarBesselReciprocal, ← Complex.ofReal_sum, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  symm
  rw [← Finset.sum_mul, hnorm, ← one_add_mul]
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  calc
    (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) =
        (1 + ‖x‖ ^ 2) ^ (1 + (-1 / 2 : ℝ)) := by
      rw [Real.rpow_add hx, Real.rpow_one]
    _ = (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := by norm_num

/-- Four coordinate derivatives characterize one additional Sobolev order. -/
theorem scalar_memSobolev_succ_iff (s : ℝ) (u : 𝓢'(V, ℂ)) :
    MemSobolev (s + 1) 2 u ↔
      MemSobolev s 2 u ∧ ∀ i : Fin 4, MemSobolev s 2 (scalarCoordinateDerivative i u) := by
  constructor
  · intro hu
    refine ⟨hu.mono (by linarith), fun i => ?_⟩
    simpa only [scalarCoordinateDerivative, add_sub_cancel_right] using
      (hu.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i))
  · rintro ⟨hu, hD⟩
    rw [show s + 1 = 1 + s by ring, ← memSobolev_besselPotential_iff]
    rw [scalar_bessel_one_reconstruction]
    apply MemSobolev.add
    · exact hu.fourierMultiplierCLM_of_bounded scalarBesselReciprocal_temperate
        ⟨1, scalarBesselReciprocal_bound⟩
    · have hsum (S : Finset (Fin 4)) : MemSobolev s 2
          (∑ i ∈ S, (2 * Real.pi * Complex.I)⁻¹ •
            fourierMultiplierCLM ℂ (scalarBesselCoordinate i) (scalarCoordinateDerivative i u)) := by
        induction S using Finset.induction_on with
        | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ s 2
        | @insert i S hi ih =>
            rw [Finset.sum_insert hi]
            exact ((hD i).fourierMultiplierCLM_of_bounded (scalarBesselCoordinate_temperate i)
              ⟨1, scalarBesselCoordinate_bound i⟩).smul _ |>.add ih
      exact hsum Finset.univ

end
end PositiveEinsteinFour.Geometry

end OAI
