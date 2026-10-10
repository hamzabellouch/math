import OAI.Analysis.OperatorAlgebra.DensityQuadraticCompression
import OAI.Analysis.OperatorAlgebra.NormalizedExpectationRoots
import OAI.Analysis.PureInfiniteness.NormalizedQuadraticEstimate
import OAI.Analysis.Nuclearity.SpatialCoefficientEstimate

namespace OAI

/-! Normalized finite-rank spatial vectors preserving prescribed trace tests.
This is the finite tracial part of the injectivity argument. It does not
assert semidiscreteness for an arbitrary von Neumann algebra. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder TensorProduct ComplexStarModule

namespace WeakPureInfiniteness

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I] [Fintype J]

lemma finiteVectorDensity_root_left (n : ℕ) (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k) (x : Fin n → H) (T : H →L[ℂ] H) :
    (inner ℂ (NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x))
      (densityLeftRepresentation T
        (NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x)))).re =
      ∑ k, w k * (inner ℂ (x k) (T (x k))).re := by
  rw [densityRoot_left_quadratic, finiteVectorDensityTensor_functional w hw]
  simp only [finiteVectorDensity, Submodule.coe_sum, Submodule.coe_smul,
    sum_apply, smul_apply, finiteOperatorCoefficient, operatorCoefficient_apply,
    Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul]

/-- A trace-preserving finite family and a nearly central finite family are
realized by the same positive, finite-rank, unit Hilbert--Schmidt vector. -/
theorem expectation_normalized_spatial_vectors (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → selfAdjoint M.toStarSubalgebra) (u : J → unitary M.toStarSubalgebra)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ z : NuclearUltrapower.HilbertSchmidt H, ‖z‖ = 1 ∧
      0 ≤ NuclearUltrapower.hsOperator z ∧
      (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
        ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
      (∀ i, |(τ.functional (a i)).re -
        (inner ℂ z (densityLeftRepresentation
          (((a i : M.toStarSubalgebra) : H →L[ℂ] H)) z)).re| <
          2 * δ * (1 + |(τ.functional (a i)).re|)) ∧
      ∀ j, ‖hsLeftUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z -
        hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z‖ ^ 2 < 2 * δ := by
  classical
  let tests : Option I → selfAdjoint M.toStarSubalgebra :=
    fun i => i.elim 1 a
  obtain ⟨n, w, x, hw, _hws, _hx, ha, hrn, hrp, hrs, hru⟩ :=
    expectation_finite_density_roots M τ E hE hEr hEf tests u hδ
  let r := NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x)
  change ‖r‖ ≤ 1 at hrn
  change 0 ≤ NuclearUltrapower.hsOperator r at hrp
  change (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
    ∀ y, NuclearUltrapower.hsOperator r y ∈ F) at hrs
  have hm : |1 - ‖r‖ ^ 2| < δ := by
    have ht := ha none
    change |(τ.functional 1).re - ∑ k, w k * (inner ℂ (x k) (x k)).re| < δ at ht
    rw [τ.normalized, Complex.one_re] at ht
    have hq (k : Fin n) : (inner ℂ (x k) (x k)).re = ‖x k‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (x k)
    simp_rw [hq] at ht
    simpa only [r, NuclearUltrapower.densityRoot_norm,
      finiteVectorDensityTensor_norm_sq w hw x] using ht
  have hr2 : 1 / 2 < ‖r‖ ^ 2 := by
    have hb := (abs_lt.mp hm).2
    linarith
  have hr : 0 < ‖r‖ := by nlinarith [norm_nonneg r]
  let c : ℂ := (‖r‖⁻¹ : ℝ)
  let z := c • r
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · change ‖c • r‖ = 1
    rw [norm_smul]
    simp only [c, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      inv_mul_cancel₀ hr.ne']
  · change 0 ≤ NuclearUltrapower.hsOperator (c • r)
    rw [map_smul]
    change 0 ≤ (‖r‖⁻¹ : ℝ) • NuclearUltrapower.hsOperator r
    exact smul_nonneg (inv_nonneg.mpr hr.le) hrp
  · obtain ⟨F, hF, hFs⟩ := hrs
    refine ⟨F, hF, ?_⟩
    intro y
    change NuclearUltrapower.hsOperator (c • r) y ∈ F
    rw [map_smul, smul_apply]
    exact F.smul_mem c (hFs y)
  · intro i
    apply normalized_quadratic_error r _ hr2 hm
    change |(τ.functional (a i)).re -
      (inner ℂ r (densityLeftRepresentation (((a i : M.toStarSubalgebra) : H →L[ℂ] H)) r)).re| < δ
    rw [show r = NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x) from rfl,
      finiteVectorDensity_root_left n w hw]
    exact ha (some i)
  · intro j
    rw [hsLeft_sub_right_norm]
    have hj := hru j
    change ‖NuclearUltrapower.hsConjugation _ r - r‖ ^ 2 < δ at hj
    have hb : ‖NuclearUltrapower.hsConjugation
        (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) r - r‖ ^ 2 <
        (2 * δ) * ‖r‖ ^ 2 := by
      nlinarith [mul_pos hδ (sub_pos.mpr hr2)]
    change ‖NuclearUltrapower.hsConjugation _ (c • r) - c • r‖ ^ 2 < 2 * δ
    rw [map_smul, ← smul_sub, norm_smul]
    simp only [c, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), mul_pow, inv_pow]
    exact (inv_mul_lt_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using hb)

/-- The finite tracial approximation with a single prescribed error tolerance. -/
theorem expectation_spatial_finite_approximation (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → selfAdjoint M.toStarSubalgebra) (u : J → unitary M.toStarSubalgebra)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : NuclearUltrapower.HilbertSchmidt H, ‖z‖ = 1 ∧
      0 ≤ NuclearUltrapower.hsOperator z ∧
      (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
        ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
      (∀ i, |(τ.functional (a i)).re -
        (inner ℂ z (densityLeftRepresentation
          (((a i : M.toStarSubalgebra) : H →L[ℂ] H)) z)).re| < ε) ∧
      ∀ j, ‖hsLeftUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z -
        hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z‖ ^ 2 < ε := by
  classical
  let D := 1 + ∑ i, |(τ.functional (a i)).re|
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let δ := min (1 / 2) (ε / (4 * D))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ * (4 * D) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 4 * D)).mp (min_le_right _ _)
  have hδD : 2 * δ * D < ε := by
    nlinarith [mul_pos hδ hD0]
  obtain ⟨z, hzn, hzp, hzf, hza, hzu⟩ :=
    expectation_normalized_spatial_vectors M τ E hE hEr hEf a u hδ hδhalf
  refine ⟨z, hzn, hzp, hzf, ?_, ?_⟩
  · intro i
    have hi : 1 + |(τ.functional (a i)).re| ≤ D := by
      dsimp only [D]
      exact add_le_add (le_refl (1 : ℝ))
        (Finset.single_le_sum (f := fun j : I => |(τ.functional (a j)).re|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    exact (hza i).trans_le ((mul_le_mul_of_nonneg_left hi (by positivity)).trans hδD.le)
  · intro j
    exact (hzu j).trans_le ((le_mul_of_one_le_right (by positivity : 0 ≤ 2 * δ) hD).trans hδD.le)

/-- The same finite witness, with the intertwining error measured in norm
rather than squared norm. This is the form used for tensor coefficients. -/
theorem expectation_spatial_norm_approximation (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → selfAdjoint M.toStarSubalgebra) (u : J → unitary M.toStarSubalgebra)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : NuclearUltrapower.HilbertSchmidt H, ‖z‖ = 1 ∧
      0 ≤ NuclearUltrapower.hsOperator z ∧
      (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
        ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
      (∀ i, |(τ.functional (a i)).re -
        (inner ℂ z (densityLeftRepresentation
          (((a i : M.toStarSubalgebra) : H →L[ℂ] H)) z)).re| < ε) ∧
      ∀ j, ‖hsLeftUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z -
        hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z‖ < ε := by
  obtain ⟨z, hzn, hzp, hzf, hza, hzu⟩ := expectation_spatial_finite_approximation
    M τ E hE hEr hEf a u (lt_min hε (sq_pos_of_pos hε))
  refine ⟨z, hzn, hzp, hzf, fun i => (hza i).trans_le (min_le_left _ _), ?_⟩
  intro j
  have hsq := (hzu j).trans_le (min_le_right _ _)
  nlinarith [norm_nonneg (hsLeftUnitary
    (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z -
      hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z)]

lemma tracial_complex_coefficient_error_le (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (a : M.toStarSubalgebra) (z : NuclearUltrapower.HilbertSchmidt H) :
    ‖τ.functional a - inner ℂ z (densityLeftRepresentation (a : H →L[ℂ] H) z)‖ ≤
      |(τ.functional (ℜ a)).re - (inner ℂ z
        (densityLeftRepresentation ((ℜ a : M.toStarSubalgebra) : H →L[ℂ] H) z)).re| +
      |(τ.functional (ℑ a)).re - (inner ℂ z
        (densityLeftRepresentation ((ℑ a : M.toStarSubalgebra) : H →L[ℂ] H) z)).re| := by
  let π := densityLeftRepresentation.comp M.toStarSubalgebra.subtype
  exact complex_coefficient_error_le τ.functional.toLinearMap
    (fun b => map_star τ.functional b) π.toLinearMap (fun b => map_star π b) a z

/-- Complex tests require two self-adjoint tests, with the same finite-rank
vector serving both and the prescribed unitary family. -/
theorem expectation_complex_spatial_approximation (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → M.toStarSubalgebra) (u : J → unitary M.toStarSubalgebra)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : NuclearUltrapower.HilbertSchmidt H, ‖z‖ = 1 ∧
      0 ≤ NuclearUltrapower.hsOperator z ∧
      (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
        ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
      (∀ i, ‖τ.functional (a i) -
        inner ℂ z (densityLeftRepresentation (a i : H →L[ℂ] H) z)‖ < ε) ∧
      ∀ j, ‖hsLeftUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z -
        hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z‖ < ε := by
  let tests : I × Bool → selfAdjoint M.toStarSubalgebra := fun p =>
    if p.2 then ℑ (a p.1) else ℜ (a p.1)
  obtain ⟨z, hzn, hzp, hzf, hza, hzu⟩ := expectation_spatial_norm_approximation
    M τ E hE hEr hEf tests u (half_pos hε)
  refine ⟨z, hzn, hzp, hzf, ?_, fun j => (hzu j).trans (half_lt_self hε)⟩
  intro i
  have hb := tracial_complex_coefficient_error_le M τ (a i) z
  have hr := hza (i, false)
  have hi := hza (i, true)
  change |(τ.functional (ℜ (a i))).re -
    (inner ℂ z (densityLeftRepresentation ((ℜ (a i) : M.toStarSubalgebra) : H →L[ℂ] H) z)).re| < ε / 2 at hr
  change |(τ.functional (ℑ (a i))).re -
    (inner ℂ z (densityLeftRepresentation ((ℑ (a i) : M.toStarSubalgebra) : H →L[ℂ] H) z)).re| < ε / 2 at hi
  exact hb.trans_lt ((add_lt_add hr hi).trans_eq (by ring))

end WeakPureInfiniteness

end

end OAI
