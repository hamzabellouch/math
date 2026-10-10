import OAI.Analysis.OperatorAlgebra.ExpectationDensityRoots
import OAI.Analysis.OperatorAlgebra.HilbertSchmidtUnitaryActions

namespace OAI

/-! A finite tracial expectation gives unit Hilbert–Schmidt vectors that
approximately intertwine any prescribed finite family of unitaries. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype J]

local instance hsNormedSpace : NormedSpace ℂ (NuclearUltrapower.HilbertSchmidt H) := inferInstance
local instance hsNormSMul : NormSMulClass ℂ (NuclearUltrapower.HilbertSchmidt H) :=
  NormedSpace.toNormSMulClass

theorem expectation_unit_intertwiners (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (u : J → unitary M.toStarSubalgebra) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : NuclearUltrapower.HilbertSchmidt H, ‖z‖ = 1 ∧
      0 ≤ NuclearUltrapower.hsOperator z ∧
      (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
        ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
      ∀ j, ‖hsLeftUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z -
        hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z‖ ^ 2 < ε := by
  let δ := min (ε / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨n, w, x, hw, _hws, _hx, ha, hrn, hrp, hrs, hru⟩ :=
    expectation_finite_density_roots M τ E hE hEr hEf
      (fun _ : Unit => (1 : selfAdjoint M.toStarSubalgebra)) u hδ
  let r := NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x)
  change ‖r‖ ≤ 1 at hrn
  change 0 ≤ NuclearUltrapower.hsOperator r at hrp
  change (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
    ∀ y, NuclearUltrapower.hsOperator r y ∈ F) at hrs
  have hm : |1 - ‖r‖ ^ 2| < δ := by
    have ht := ha ()
    change |(τ.functional 1).re - ∑ k, w k * (inner ℂ (x k) (x k)).re| < δ at ht
    rw [τ.normalized, Complex.one_re] at ht
    have hq (k : Fin n) : (inner ℂ (x k) (x k)).re = ‖x k‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (x k)
    simp_rw [hq] at ht
    simpa only [r, NuclearUltrapower.densityRoot_norm,
      finiteVectorDensityTensor_norm_sq w hw x] using ht
  have hr2 : 1 / 2 < ‖r‖ ^ 2 := by
    have hd : δ ≤ 1 / 2 := min_le_right _ _
    have hb := (abs_lt.mp hm).2
    linarith
  have hr : 0 < ‖r‖ := by nlinarith [norm_nonneg r]
  let c : ℂ := (‖r‖⁻¹ : ℝ)
  let z := c • r
  refine ⟨z, ?_, ?_, ?_, ?_⟩
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
  · intro j
    rw [hsLeft_sub_right_norm]
    have hj := hru j
    change ‖NuclearUltrapower.hsConjugation _ r - r‖ ^ 2 < δ at hj
    have hδe : δ ≤ ε / 4 := min_le_left _ _
    have hb : ‖NuclearUltrapower.hsConjugation
        (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) r - r‖ ^ 2 < ε * ‖r‖ ^ 2 := by
      nlinarith
    change ‖NuclearUltrapower.hsConjugation _ (c • r) - c • r‖ ^ 2 < ε
    rw [map_smul, ← smul_sub, norm_smul]
    simp only [c, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), mul_pow, inv_pow]
    exact (inv_mul_lt_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using hb)

end WeakPureInfiniteness

end

end OAI
