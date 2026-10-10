import OAI.Geometry.EinsteinFour.ScalarPoissonKernelBootstrap

namespace OAI

/-! A variable-coefficient cutoff commutator loses only one derivative.
Nested cutoffs let this estimate use regularity on a larger neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

private theorem scalar_multiplier_commute (a b : S) (u : T) :
    M a (M b u) = M b (M a u) := by
  rw [smulLeftCLM_smulLeftCLM_apply b.hasTemperateGrowth a.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply a.hasTemperateGrowth b.hasTemperateGrowth]
  rw [mul_comm (b : V → ℂ) (a : V → ℂ)]

private theorem scalar_multiplier_real_smul (a : S) (c : ℝ) (u : T) :
    M a (c • u) = c • M a u :=
  (M a).toLinearMap.map_smul_of_tower c u

private theorem scalar_cutoff_second_product (ψ : S) (u : T) (i j : Fin 4) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative j (M ψ u)) =
      M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) +
        M (D j ψ) (scalarCoordinateDerivative i u) +
        M (D i ψ) (scalarCoordinateDerivative j u) + M (D i (D j ψ)) u := by
  rw [scalarCoordinateDerivative_multiplier]
  change LineDeriv.lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ i) (_ + _) = _
  rw [map_add]
  change scalarCoordinateDerivative i (M (D j ψ) u) +
    scalarCoordinateDerivative i (M ψ (scalarCoordinateDerivative j u)) = _
  rw [scalarCoordinateDerivative_multiplier, scalarCoordinateDerivative_multiplier]
  change M (D i (D j ψ)) u + M (D j ψ) (scalarCoordinateDerivative i u) +
    (M (D i ψ) (scalarCoordinateDerivative j u) +
      M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) = _
  abel

private theorem scalar_cutoff_helmholtz (ψ : S) (u : T) :
    normalizedScalarHelmholtz (M ψ u) = M ψ (normalizedScalarHelmholtz u) -
      (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • scalarLaplacianCommutator ψ u := by
  simp only [normalizedScalarHelmholtz, scalarLaplacianCommutator,
    map_sub, scalar_multiplier_real_smul]
  module

private theorem scalar_cutoff_first_term (a ψ : S) (u : T) (i : Fin 4) :
    M a (scalarCoordinateDerivative i (M ψ u)) =
      M ψ (M a (scalarCoordinateDerivative i u)) + M a (M (D i ψ) u) := by
  rw [scalarCoordinateDerivative_multiplier]
  change M a (M (D i ψ) u + M ψ (scalarCoordinateDerivative i u)) = _
  rw [map_add, scalar_multiplier_commute a ψ]
  abel

private theorem scalar_cutoff_second_term (a ψ : S) (u : T) (i j : Fin 4) :
    M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j (M ψ u))) =
      M ψ (M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) +
        M a (M (D j ψ) (scalarCoordinateDerivative i u) +
          M (D i ψ) (scalarCoordinateDerivative j u) + M (D i (D j ψ)) u) := by
  rw [scalar_cutoff_second_product]
  simp only [map_add]
  rw [scalar_multiplier_commute a ψ]
  abel

/-- The commutator with a cutoff, for the actual differential operator. -/
def scalarPerturbedCutoffCommutator (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (ψ : S) (u : T) : T :=
  scalarPerturbedOperator a b (M ψ u) - M ψ (scalarPerturbedOperator a b u)

theorem scalarPerturbedCutoffCommutator_eq (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (ψ : S) (u : T) :
    scalarPerturbedCutoffCommutator a b ψ u =
      -(Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • scalarLaplacianCommutator ψ u +
        (∑ i : Fin 4, ∑ j : Fin 4, M (a i j)
          (M (D j ψ) (scalarCoordinateDerivative i u) +
            M (D i ψ) (scalarCoordinateDerivative j u) + M (D i (D j ψ)) u)) +
        ∑ i : Fin 4, M (b i) (M (D i ψ) u) := by
  unfold scalarPerturbedCutoffCommutator scalarPerturbedOperator
  rw [scalar_cutoff_helmholtz]
  simp_rw [scalar_cutoff_second_term, scalar_cutoff_first_term]
  simp only [map_add, map_sum, Finset.sum_add_distrib]
  module

private theorem scalar_sobolev_sum (n : ℕ) (f : Fin 4 → T)
    (hf : ∀ i, MemSobolev (n : ℝ) 2 (f i)) : MemSobolev (n : ℝ) 2 (∑ i, f i) := by
  have hs (s : Finset (Fin 4)) : MemSobolev (n : ℝ) 2 (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ (n : ℝ) 2
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (hf i).add ih
  exact hs Finset.univ

/-- The full variable-coefficient cutoff commutator has differential order one. -/
theorem scalarPerturbedCutoffCommutator_memSobolev
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (ψ : S) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (scalarPerturbedCutoffCommutator a b ψ u) := by
  have hstep : MemSobolev (n : ℝ) 2 u ∧
      ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
    apply (scalar_memSobolev_succ_iff (n : ℝ) u).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hu
  rw [scalarPerturbedCutoffCommutator_eq]
  apply MemSobolev.add
  · apply MemSobolev.add
    · exact (scalarLaplacianCommutator_memSobolev n ψ u hu).smul _
    · apply scalar_sobolev_sum n
      intro i
      apply scalar_sobolev_sum n
      intro j
      apply scalar_memSobolev_schwartz_multiplier n
      exact ((scalar_memSobolev_schwartz_multiplier n (D j ψ) _ (hstep.2 i)).add
        (scalar_memSobolev_schwartz_multiplier n (D i ψ) _ (hstep.2 j))).add
        (scalar_memSobolev_schwartz_multiplier n (D i (D j ψ)) _ hstep.1)
  · apply scalar_sobolev_sum n
    intro i
    exact scalar_memSobolev_schwartz_multiplier n (b i) _
      (scalar_memSobolev_schwartz_multiplier n (D i ψ) _ hstep.1)

/-- The outer cutoff equals one near the support of the inner cutoff. -/
def ScalarCutoffNested (ψ χ : S) : Prop :=
  ∀ x ∈ tsupport (ψ : V → ℂ), (χ : V → ℂ) =ᶠ[𝓝 x] fun _ => 1

private theorem scalar_cutoff_nested_value (ψ χ : S) (h : ScalarCutoffNested ψ χ) :
    (χ : V → ℂ) * ψ = ψ := by
  funext x
  by_cases hx : ψ x = 0
  · simp only [Pi.mul_apply, hx, mul_zero]
  · have hm : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
    simp only [Pi.mul_apply, (h x hm).eq_of_nhds, one_mul]

private theorem scalar_cutoff_nested_first_zero (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i : Fin 4) : (D i χ : V → ℂ) * ψ = 0 := by
  funext x
  by_cases hx : ψ x = 0
  · simp only [Pi.mul_apply, hx, mul_zero, Pi.zero_apply]
  · have hm : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
    have hd := (h x hm).fderiv_eq (𝕜 := ℝ)
    have hz : D i χ x = 0 := by
      change (fderiv ℝ (χ : V → ℂ) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) = 0
      simp only [hd, fderiv_const_apply, zero_apply]
    simp only [Pi.mul_apply, hz, zero_mul, Pi.zero_apply]

private theorem scalar_cutoff_nested_second_zero (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i j : Fin 4) : (D i (D j χ) : V → ℂ) * ψ = 0 := by
  funext x
  by_cases hx : ψ x = 0
  · simp only [Pi.mul_apply, hx, mul_zero, Pi.zero_apply]
  · have hm : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
    have hd : (D j χ : V → ℂ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(h x hm).fderiv (𝕜 := ℝ)] with y hy
      change (fderiv ℝ (χ : V → ℂ) y) (EuclideanSpace.basisFun (Fin 4) ℝ j) = 0
      simp only [hy, fderiv_const_apply, zero_apply]
    have hz : D i (D j χ) x = 0 := by
      change (fderiv ℝ (D j χ : V → ℂ) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) = 0
      simp only [hd.fderiv_eq (𝕜 := ℝ), fderiv_const_apply, zero_apply]
    simp only [Pi.mul_apply, hz, zero_mul, Pi.zero_apply]

private theorem scalar_cutoff_nested_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ) (u : T) :
    M ψ (M χ u) = M ψ u := by
  rw [smulLeftCLM_smulLeftCLM_apply χ.hasTemperateGrowth ψ.hasTemperateGrowth,
    scalar_cutoff_nested_value ψ χ h]

private theorem scalar_cutoff_nested_first_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i : Fin 4) (u : T) : M ψ (M (D i χ) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (D i χ).hasTemperateGrowth ψ.hasTemperateGrowth,
    scalar_cutoff_nested_first_zero ψ χ h i]
  exact (smulLeftCLM_const (F := ℂ) 0 u).trans (zero_smul ℂ u)

private theorem scalar_cutoff_nested_second_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i j : Fin 4) (u : T) : M ψ (M (D i (D j χ)) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (D i (D j χ)).hasTemperateGrowth ψ.hasTemperateGrowth,
    scalar_cutoff_nested_second_zero ψ χ h i j]
  exact (smulLeftCLM_const (F := ℂ) 0 u).trans (zero_smul ℂ u)

private theorem scalar_cutoff_nested_derivative (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i : Fin 4) (u : T) :
    M ψ (scalarCoordinateDerivative i (M χ u)) = M ψ (scalarCoordinateDerivative i u) := by
  rw [scalarCoordinateDerivative_multiplier, map_add]
  change M ψ (M (D i χ) u) + M ψ (M χ (scalarCoordinateDerivative i u)) = _
  rw [scalar_cutoff_nested_first_mul ψ χ h, scalar_cutoff_nested_mul ψ χ h, zero_add]

private theorem scalar_cutoff_nested_second_derivative (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i j : Fin 4) (u : T) :
    M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j (M χ u))) =
      M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) := by
  rw [scalar_cutoff_second_product]
  simp only [map_add]
  rw [scalar_cutoff_nested_mul ψ χ h, scalar_cutoff_nested_first_mul ψ χ h,
    scalar_cutoff_nested_first_mul ψ χ h, scalar_cutoff_nested_second_mul ψ χ h]
  simp only [add_zero]

/-- Inner localization of the equation is unchanged by inserting an outer cutoff. -/
theorem scalarPerturbedOperator_nested_cutoff (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (ψ χ : S) (h : ScalarCutoffNested ψ χ) (u : T) :
    M ψ (scalarPerturbedOperator a b (M χ u)) = M ψ (scalarPerturbedOperator a b u) := by
  have hΔ : M ψ (Δ (M χ u)) = M ψ (Δ u) := by
    rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ),
      TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact scalar_cutoff_nested_second_derivative ψ χ h i i u
  have hH : M ψ (normalizedScalarHelmholtz (M χ u)) = M ψ (normalizedScalarHelmholtz u) := by
    simp only [normalizedScalarHelmholtz, map_sub, scalar_multiplier_real_smul]
    rw [scalar_cutoff_nested_mul ψ χ h, hΔ]
  have hsecond (i j : Fin 4) :
      M ψ (M (a i j) (scalarCoordinateDerivative i (scalarCoordinateDerivative j (M χ u)))) =
        M ψ (M (a i j) (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) := by
    rw [scalar_multiplier_commute ψ (a i j), scalar_multiplier_commute ψ (a i j),
      scalar_cutoff_nested_second_derivative ψ χ h]
  have hfirst (i : Fin 4) :
      M ψ (M (b i) (scalarCoordinateDerivative i (M χ u))) =
        M ψ (M (b i) (scalarCoordinateDerivative i u)) := by
    rw [scalar_multiplier_commute ψ (b i), scalar_multiplier_commute ψ (b i),
      scalar_cutoff_nested_derivative ψ χ h]
  simp only [scalarPerturbedOperator, map_add, map_sum, hH, hsecond, hfirst]

/-- One nested-cutoff step gains one local Sobolev order. -/
theorem scalar_nested_cutoff_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (ψ χ : S) (hnest : ScalarCutoffNested ψ χ) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M χ u))
    (hf : MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u))) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M ψ u) := by
  have hzero : MemSobolev 0 2 (M ψ u) := by
    rw [← scalar_cutoff_nested_mul ψ χ hnest]
    exact (scalar_memSobolev_schwartz_multiplier (n + 1) ψ _ hu).mono (by positivity)
  have heq : scalarPerturbedOperator a b (M ψ u) =
      M ψ (scalarPerturbedOperator a b u) + scalarPerturbedCutoffCommutator a b ψ (M χ u) := by
    rw [scalarPerturbedCutoffCommutator,
      scalar_cutoff_nested_mul ψ χ hnest, scalarPerturbedOperator_nested_cutoff a b ψ χ hnest]
    abel
  exact scalar_small_elliptic_integer_regularity a b δ hδ ha ha1 ha2 hb hb1 hsmall n
    (M ψ u) _ hzero
    (hf.add (scalarPerturbedCutoffCommutator_memSobolev a b ψ n (M χ u) hu)) heq

end
end PositiveEinsteinFour.Geometry

end OAI
