import OAI.Geometry.EinsteinFour.ScalarPoissonKernelUniqueness

namespace OAI

/-! Quantitative bounded extension of the actual transposed operator after
Bessel regularization. Coefficient bounds imply the dense-range condition used for
distributional uniqueness. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal LineDeriv BigOperators Laplacian

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

/-- Multiplication by a Schwartz coefficient, as a physical L2 operator. -/
def scalarSchwartzMultiplyL2 (a : S) : L2 →L[ℂ] L2 :=
  scalarL2Multiply (a.toLp ∞)

private theorem scalarSchwartz_product_distribution (a φ : S) :
    (SchwartzMap.smulLeftCLM ℂ a φ : 𝓢'(V, ℂ)) = smulLeftCLM ℂ a (φ : 𝓢'(V, ℂ)) := by
  ext ψ
  simp only [SchwartzMap.coe_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth, smul_eq_mul]
  ring

private theorem scalarL2_eq_schwartz (u : L2) (φ : S)
    (hu : (u : 𝓢'(V, ℂ)) = (φ : 𝓢'(V, ℂ))) : u = φ.toLp 2 volume := by
  apply scalarL2_distribution_injective
  change (u : 𝓢'(V, ℂ)) = (φ.toLp 2 volume : 𝓢'(V, ℂ))
  rw [Lp.toTemperedDistribution_toLp_eq]
  exact hu

private theorem scalarSchwartzMultiplyL2_distribution (a φ : S) :
    (scalarSchwartzMultiplyL2 a (φ.toLp 2 volume) : 𝓢'(V, ℂ)) =
      (SchwartzMap.smulLeftCLM ℂ a φ : 𝓢'(V, ℂ)) := by
  unfold scalarSchwartzMultiplyL2
  rw [SchwartzMap.toLp]
  rw [scalarL2Multiply_distribution _ a.hasTemperateGrowth (a.memLp ∞ volume),
    Lp.toTemperedDistribution_toLp_eq, scalarSchwartz_product_distribution]

theorem scalarSchwartzMultiplyL2_toLp (a φ : S) :
    scalarSchwartzMultiplyL2 a (φ.toLp 2 volume) =
      (SchwartzMap.smulLeftCLM ℂ a φ).toLp 2 volume :=
  scalarL2_eq_schwartz _ _ (scalarSchwartzMultiplyL2_distribution a φ)

private theorem scalar_derivative_schwartz_distribution (i : Fin 4) (φ : S) :
    scalarCoordinateDerivative i (φ : 𝓢'(V, ℂ)) = (D i φ : 𝓢'(V, ℂ)) :=
  lineDerivOp_toTemperedDistributionCLM_eq φ (EuclideanSpace.basisFun (Fin 4) ℝ i)

private theorem scalarBesselFirstL2_schwartz_distribution (i : Fin 4) (φ : S) :
    (scalarBesselFirstL2 i (φ.toLp 2 volume) : 𝓢'(V, ℂ)) =
      (D i (scalarSchwartzBesselInverse φ) : 𝓢'(V, ℂ)) := by
  rw [scalarBesselFirstL2_distribution, ← scalarSchwartzBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq, scalar_derivative_schwartz_distribution]

theorem scalarBesselFirstL2_toLp (i : Fin 4) (φ : S) :
    scalarBesselFirstL2 i (φ.toLp 2 volume) =
      (D i (scalarSchwartzBesselInverse φ)).toLp 2 volume :=
  scalarL2_eq_schwartz _ _ (scalarBesselFirstL2_schwartz_distribution i φ)

private theorem scalarBesselSecondL2_schwartz_distribution (i j : Fin 4) (φ : S) :
    (scalarBesselSecondL2 i j (φ.toLp 2 volume) : 𝓢'(V, ℂ)) =
      (D i (D j (scalarSchwartzBesselInverse φ)) : 𝓢'(V, ℂ)) := by
  rw [scalarBesselSecondL2_distribution, ← scalarSchwartzBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq, scalar_derivative_schwartz_distribution,
    scalar_derivative_schwartz_distribution]

theorem scalarBesselSecondL2_toLp (i j : Fin 4) (φ : S) :
    scalarBesselSecondL2 i j (φ.toLp 2 volume) =
      (D i (D j (scalarSchwartzBesselInverse φ))).toLp 2 volume :=
  scalarL2_eq_schwartz _ _ (scalarBesselSecondL2_schwartz_distribution i j φ)

private theorem scalarSchwartzHelmholtz_distribution (φ : S) :
    (scalarSchwartzHelmholtz φ : 𝓢'(V, ℂ)) = normalizedScalarHelmholtz (φ : 𝓢'(V, ℂ)) := by
  unfold scalarSchwartzHelmholtz normalizedScalarHelmholtz
  change SchwartzMap.toTemperedDistributionCLM V ℂ volume _ = _
  rw [map_sub, map_smul]
  rw [laplacian_toTemperedDistributionCLM_eq]
  simp only [Complex.coe_smul]

theorem scalarSchwartzHelmholtz_bessel_toLp (φ : S) :
    (scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ)).toLp 2 volume = φ.toLp 2 volume := by
  apply scalarL2_distribution_injective
  change ((scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ)).toLp 2 volume : 𝓢'(V, ℂ)) =
    (φ.toLp 2 volume : 𝓢'(V, ℂ))
  rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
    scalarSchwartzHelmholtz_distribution, scalarSchwartzBesselInverse_distribution,
    normalizedScalarHelmholtz_eq_bessel, besselPotential_besselPotential_apply]
  norm_num

def scalarAdjointSecondPiece (a φ : S) (i j : Fin 4) : S :=
  SchwartzMap.smulLeftCLM ℂ a (D j (D i φ)) +
    SchwartzMap.smulLeftCLM ℂ (D i a) (D j φ) +
    SchwartzMap.smulLeftCLM ℂ (D j a) (D i φ) +
    SchwartzMap.smulLeftCLM ℂ (D j (D i a)) φ

def scalarAdjointFirstPiece (b φ : S) (i : Fin 4) : S :=
  SchwartzMap.smulLeftCLM ℂ b (D i φ) + SchwartzMap.smulLeftCLM ℂ (D i b) φ

def scalarAdjointSecondL2Term (a : S) (i j : Fin 4) : L2 →L[ℂ] L2 :=
  (scalarSchwartzMultiplyL2 a).comp (scalarBesselSecondL2 j i) +
    (scalarSchwartzMultiplyL2 (D i a)).comp (scalarBesselFirstL2 j) +
    (scalarSchwartzMultiplyL2 (D j a)).comp (scalarBesselFirstL2 i) +
    (scalarSchwartzMultiplyL2 (D j (D i a))).comp scalarBesselInverseL2

def scalarAdjointFirstL2Term (b : S) (i : Fin 4) : L2 →L[ℂ] L2 :=
  (scalarSchwartzMultiplyL2 b).comp (scalarBesselFirstL2 i) +
    (scalarSchwartzMultiplyL2 (D i b)).comp scalarBesselInverseL2

def scalarAdjointL2Perturbation (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) : L2 →L[ℂ] L2 :=
  (∑ i : Fin 4, ∑ j : Fin 4, scalarAdjointSecondL2Term (a i j) i j) -
    ∑ i : Fin 4, scalarAdjointFirstL2Term (b i) i

private theorem scalarAdjointSecondL2Term_toLp (a φ : S) (i j : Fin 4) :
    scalarAdjointSecondL2Term a i j (φ.toLp 2 volume) =
      (scalarAdjointSecondPiece a (scalarSchwartzBesselInverse φ) i j).toLp 2 volume := by
  simp only [scalarAdjointSecondL2Term, add_apply, ContinuousLinearMap.comp_apply,
    scalarBesselSecondL2_toLp, scalarBesselFirstL2_toLp, ← scalarSchwartzBesselInverse_toLp,
    scalarSchwartzMultiplyL2_toLp]
  simp only [scalarAdjointSecondPiece, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (μ := (volume : Measure V)), map_add]

private theorem scalarAdjointFirstL2Term_toLp (b φ : S) (i : Fin 4) :
    scalarAdjointFirstL2Term b i (φ.toLp 2 volume) =
      (scalarAdjointFirstPiece b (scalarSchwartzBesselInverse φ) i).toLp 2 volume := by
  simp only [scalarAdjointFirstL2Term, add_apply, ContinuousLinearMap.comp_apply,
    scalarBesselFirstL2_toLp, ← scalarSchwartzBesselInverse_toLp,
    scalarSchwartzMultiplyL2_toLp]
  simp only [scalarAdjointFirstPiece, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (μ := (volume : Measure V)), map_add]

/-- The bounded L2 perturbation is exactly the regularized formal transpose. -/
theorem scalarAdjointL2Perturbation_toLp (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (φ : S) :
    (scalarSchwartzTranspose a b (scalarSchwartzBesselInverse φ)).toLp 2 volume =
      φ.toLp 2 volume + scalarAdjointL2Perturbation a b (φ.toLp 2 volume) := by
  have hT : scalarSchwartzTranspose a b (scalarSchwartzBesselInverse φ) =
      scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ) +
        (∑ i : Fin 4, ∑ j : Fin 4,
          scalarAdjointSecondPiece (a i j) (scalarSchwartzBesselInverse φ) i j) -
        ∑ i : Fin 4, scalarAdjointFirstPiece (b i) (scalarSchwartzBesselInverse φ) i := by
    unfold scalarSchwartzTranspose
    simp only [scalarSchwartzCoordinateDerivative_second_product]
    simp only [scalarSchwartzCoordinateDerivative_product]
    simp only [scalarAdjointSecondPiece, scalarAdjointFirstPiece]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    abel
  rw [hT]
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ = _
  rw [map_sub, map_add, map_sum]
  simp only [map_sum]
  change (scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ)).toLp 2 volume +
      (∑ i : Fin 4, ∑ j : Fin 4,
        (scalarAdjointSecondPiece (a i j) (scalarSchwartzBesselInverse φ) i j).toLp 2 volume) -
      (∑ i : Fin 4, (scalarAdjointFirstPiece (b i) (scalarSchwartzBesselInverse φ) i).toLp 2 volume) = _
  rw [scalarSchwartzHelmholtz_bessel_toLp]
  simp only [scalarAdjointL2Perturbation, sub_apply, sum_apply,
    scalarAdjointSecondL2Term_toLp, scalarAdjointFirstL2Term_toLp]
  abel

private theorem scalarSchwartzMultiplyL2_bound (a : S) (δ : ℝ)
    (ha : ‖a.toLp ∞ (volume : Measure V)‖ ≤ δ) (f : L2) :
    ‖scalarSchwartzMultiplyL2 a f‖ ≤ δ * ‖f‖ :=
  (scalarL2Multiply_norm _ _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg f))

private theorem scalarAdjointSecondL2Term_bound (a : S) (i j : Fin 4) (δ : ℝ)
    (hδ : 0 ≤ δ) (ha : ‖a.toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hi : ‖(D i a).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hj : ‖(D j a).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hij : ‖(D j (D i a)).toLp ∞ (volume : Measure V)‖ ≤ δ) (f : L2) :
    ‖scalarAdjointSecondL2Term a i j f‖ ≤
      δ * ((2 * Real.pi) ^ 2 + 2 * (2 * Real.pi) + 1) * ‖f‖ := by
  let A := scalarSchwartzMultiplyL2 a (scalarBesselSecondL2 j i f)
  let B := scalarSchwartzMultiplyL2 (D i a) (scalarBesselFirstL2 j f)
  let C := scalarSchwartzMultiplyL2 (D j a) (scalarBesselFirstL2 i f)
  let E := scalarSchwartzMultiplyL2 (D j (D i a)) (scalarBesselInverseL2 f)
  have hA : ‖A‖ ≤ δ * ((2 * Real.pi) ^ 2 * ‖f‖) :=
    (scalarSchwartzMultiplyL2_bound _ _ ha _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselSecondL2_norm j i f) hδ)
  have hB : ‖B‖ ≤ δ * ((2 * Real.pi) * ‖f‖) :=
    (scalarSchwartzMultiplyL2_bound _ _ hi _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselFirstL2_norm j f) hδ)
  have hC : ‖C‖ ≤ δ * ((2 * Real.pi) * ‖f‖) :=
    (scalarSchwartzMultiplyL2_bound _ _ hj _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselFirstL2_norm i f) hδ)
  have hE : ‖E‖ ≤ δ * ‖f‖ :=
    (scalarSchwartzMultiplyL2_bound _ _ hij _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselInverseL2_norm f) hδ)
  change ‖A + B + C + E‖ ≤ _
  have hAB := norm_add_le A B
  have hABC := norm_add_le (A + B) C
  have hABCE := norm_add_le (A + B + C) E
  nlinarith

private theorem scalarAdjointFirstL2Term_bound (b : S) (i : Fin 4) (δ : ℝ)
    (hδ : 0 ≤ δ) (hb : ‖b.toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hi : ‖(D i b).toLp ∞ (volume : Measure V)‖ ≤ δ) (f : L2) :
    ‖scalarAdjointFirstL2Term b i f‖ ≤ δ * ((2 * Real.pi) + 1) * ‖f‖ := by
  have hB := (scalarSchwartzMultiplyL2_bound _ _ hb (scalarBesselFirstL2 i f)).trans
    (mul_le_mul_of_nonneg_left (scalarBesselFirstL2_norm i f) hδ)
  have hI := (scalarSchwartzMultiplyL2_bound _ _ hi (scalarBesselInverseL2 f)).trans
    (mul_le_mul_of_nonneg_left (scalarBesselInverseL2_norm f) hδ)
  change ‖scalarSchwartzMultiplyL2 b (scalarBesselFirstL2 i f) +
    scalarSchwartzMultiplyL2 (D i b) (scalarBesselInverseL2 f)‖ ≤ _
  have hadd := norm_add_le (scalarSchwartzMultiplyL2 b (scalarBesselFirstL2 i f))
    (scalarSchwartzMultiplyL2 (D i b) (scalarBesselInverseL2 f))
  nlinarith

/-- Uniform control of coefficient derivatives makes the formal transpose
an explicit small perturbation. -/
theorem scalarAdjointL2Perturbation_bound (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j, ‖(a i j).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha1 : ∀ i j k, ‖(D k (a i j)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha2 : ∀ i j k l, ‖(D k (D l (a i j))).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb : ∀ i, ‖(b i).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb1 : ∀ i k, ‖(D k (b i)).toLp ∞ (volume : Measure V)‖ ≤ δ) :
    ∀ f : L2, ‖scalarAdjointL2Perturbation a b f‖ ≤
      ((16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ) * ‖f‖ := by
  intro f
  simp only [scalarAdjointL2Perturbation, sub_apply, sum_apply]
  calc
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4, ‖scalarAdjointSecondL2Term (a i j) i j f‖) +
        ∑ i : Fin 4, ‖scalarAdjointFirstL2Term (b i) i f‖ := by
      apply (norm_sub_le _ _).trans
      apply add_le_add
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      · exact norm_sum_le _ _
    _ ≤ (∑ _i : Fin 4, ∑ _j : Fin 4,
          δ * ((2 * Real.pi) ^ 2 + 2 * (2 * Real.pi) + 1) * ‖f‖) +
        ∑ _i : Fin 4, δ * ((2 * Real.pi) + 1) * ‖f‖ := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          scalarAdjointSecondL2Term_bound _ i j δ hδ (ha i j) (ha1 i j i)
            (ha1 i j j) (ha2 i j j i) f))
      · exact Finset.sum_le_sum (fun i _ =>
          scalarAdjointFirstL2Term_bound _ i δ hδ (hb i) (hb1 i i) f)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem scalarAdjointL2Perturbation_opNorm (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j, ‖(a i j).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha1 : ∀ i j k, ‖(D k (a i j)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha2 : ∀ i j k l, ‖(D k (D l (a i j))).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb : ∀ i, ‖(b i).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb1 : ∀ i k, ‖(D k (b i)).toLp ∞ (volume : Measure V)‖ ≤ δ) :
    ‖scalarAdjointL2Perturbation a b‖ ≤
      (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ := by
  exact (scalarAdjointL2Perturbation a b).opNorm_le_bound (by positivity)
    (scalarAdjointL2Perturbation_bound a b δ hδ ha ha1 ha2 hb hb1)

/-- An actual L2 distributional kernel element vanishes under explicit
smallness of the coefficient jets through order two. -/
theorem scalarPerturbedOperator_kernel_small (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j, ‖(a i j).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha1 : ∀ i j k, ‖(D k (a i j)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha2 : ∀ i j k l, ‖(D k (D l (a i j))).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb : ∀ i, ‖(b i).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb1 : ∀ i k, ‖(D k (b i)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : L2) (hu : scalarPerturbedOperator a b (u : 𝓢'(V, ℂ)) = 0) : u = 0 := by
  have hK := (scalarAdjointL2Perturbation_opNorm a b δ hδ ha ha1 ha2 hb hb1).trans_lt hsmall
  apply scalarPerturbedOperator_kernel_of_transpose_equiv a b
    (scalarPerturbationEquiv (scalarAdjointL2Perturbation a b) hK) _ u hu
  intro φ
  rw [scalarAdjointL2Perturbation_toLp, scalarPerturbationEquiv_apply]

end
end PositiveEinsteinFour.Geometry

end OAI
