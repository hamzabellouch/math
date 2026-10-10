import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootVelocityRecovery
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-!
# Exponential recovery from actual subgroup curves

The velocity of a curve in a closed matrix subgroup exponentiates inside
that subgroup. The proof uses growing powers of the curve and the
first-order approximation to the matrix exponential. Thus no matrix
Lie-group classification or determinant formula for the exponential is
needed. The converse supplies an exact exponential test for membership
in the actual velocity subspace.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma eventual_exp_bound_of_scaled_increment {n : ℕ}
    [Nonempty (Fin n)]
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hA : Tendsto (fun N : ℕ => (N + 1 : ℝ) • (A N - 1)) atTop (𝓝 V)) :
    ∀ᶠ N in atTop, ‖A N‖ ≤ Real.exp ((‖V‖ + 1) / (N + 1 : ℝ)) := by
  have hb : ∀ᶠ N : ℕ in atTop, ‖(N + 1 : ℝ) • (A N - 1)‖ ≤ ‖V‖ + 1 :=
    (hA.norm.eventually (Iio_mem_nhds (by linarith : ‖V‖ < ‖V‖ + 1))).mono
      (fun _ h => h.le)
  filter_upwards [hb] with N hN
  have hk : (0 : ℝ) < N + 1 := by positivity
  have hr : ‖A N - 1‖ ≤ (‖V‖ + 1) / (N + 1 : ℝ) := by
    apply (le_div_iff₀ hk).mpr
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hk, mul_comm] using hN
  calc
    ‖A N‖ = ‖(A N - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖A N - 1‖ + ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
    _ ≤ (‖V‖ + 1) / (N + 1 : ℝ) + 1 := add_le_add hr (le_of_eq norm_one)
    _ ≤ Real.exp ((‖V‖ + 1) / (N + 1 : ℝ)) := Real.add_one_le_exp _

/-- The reciprocal-time powers of an actual curve converge to the
matrix exponential of its velocity. -/
theorem tendsto_matrix_powers_of_velocity {n : ℕ} [Nonempty (Fin n)]
    (γ : ℝ → G n) (V : Matrix (Fin n) (Fin n) ℝ)
    (hvelocity : HasMatrixVelocity γ V) :
    Tendsto (fun N : ℕ => (γ ((N + 1 : ℝ)⁻¹)).val ^ (N + 1)) atTop
      (𝓝 (NormedSpace.exp V)) := by
  let k : ℕ → ℝ := fun N => N + 1
  let s : ℕ → ℝ := fun N => (k N)⁻¹
  let A : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => (γ (s N)).val
  let B : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => NormedSpace.exp (s N • V)
  let D : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => k N • (A N - 1)
  let E : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => k N • (B N - 1)
  have hk (N : ℕ) : 0 < k N := by dsimp only [k]; positivity
  have hktop : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hs0 : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hktop
  have hD : Tendsto D atTop (𝓝 V) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [Function.comp_def, D, A, s, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, div_eq_mul_inv, inv_inv, mul_comm] using
      (hvelocity i j).comp hs0
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V)) V 0 := by
    convert hasDerivAt_exp_smul_const V (0 : ℝ) using 1 <;>
      first | rfl | simp only [zero_smul, NormedSpace.exp_zero, one_mul]
  have hE : Tendsto E atTop (𝓝 V) := by
    convert hd.tendsto_slope_zero_right.comp hs0 using 1
    · funext N
      simp only [Function.comp_def, E, B, s, zero_add, zero_smul,
        NormedSpace.exp_zero, inv_inv]
    · rfl
  have hdiff (N : ℕ) : k N • (A N - B N) = D N - E N := by
    dsimp only [D, E]
    rw [← smul_sub]
    congr 1
    abel
  have herr : Tendsto (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) atTop (𝓝 0) := by
    have he := (hD.sub hE).norm
    have hnorm (N : ℕ) : (N + 1 : ℝ) * ‖A N - B N‖ = ‖D N - E N‖ := by
      rw [← hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (hk N)]
    simpa only [hnorm, sub_self, norm_zero] using he
  have hA := eventual_exp_bound_of_scaled_increment A V hD
  have hB := eventual_exp_bound_of_scaled_increment B V hE
  have hp := tendsto_matrix_power_difference_zero A B (‖V‖ + 1)
    (by positivity) hA hB herr
  have hBpow (N : ℕ) : B N ^ (N + 1) = NormedSpace.exp V := by
    change NormedSpace.exp (s N • V) ^ (N + 1) = NormedSpace.exp V
    have hpow : NormedSpace.exp ((N + 1) • (s N • V)) =
        NormedSpace.exp (s N • V) ^ (N + 1) :=
      NormedSpace.exp_nsmul (N + 1) (s N • V)
    rw [← hpow]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hscalar : (↑(N + 1) : ℝ) * s N = 1 := by
      change (↑(N + 1) : ℝ) * (k N)⁻¹ = 1
      have he : (↑(N + 1) : ℝ) = k N := by simp [k]
      rw [he, mul_inv_cancel₀ (ne_of_gt (hk N))]
    rw [hscalar, one_smul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [A, s, k, hBpow] using hp

/-- The determinant-one assertion is recovered from the approximating
group elements, not assumed as a general exponential formula. -/
theorem exists_subgroup_element_exp_velocity {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (γ : ℝ → G n) (hγ : ∀ t, γ t ∈ L)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : HasMatrixVelocity γ V) :
    ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp V := by
  have hp := tendsto_matrix_powers_of_velocity γ V hV
  have hd : Matrix.det (NormedSpace.exp V) = 1 := by
    have ht := (continuous_id.matrix_det.tendsto (NormedSpace.exp V)).comp hp
    change Tendsto (fun N : ℕ => Matrix.det ((γ ((N + 1 : ℝ)⁻¹)).val ^ (N + 1)))
      atTop (𝓝 (Matrix.det (NormedSpace.exp V))) at ht
    have he : (fun N : ℕ => Matrix.det ((γ ((N + 1 : ℝ)⁻¹)).val ^ (N + 1))) =
        fun _ => (1 : ℝ) := by
      funext N
      rw [← Matrix.SpecialLinearGroup.coe_pow]
      exact (γ ((N + 1 : ℝ)⁻¹) ^ (N + 1)).property
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let g : G n := ⟨NormedSpace.exp V, hd⟩
  refine ⟨g, ?_, rfl⟩
  apply hL.mem_of_tendsto (show Tendsto
      (fun N : ℕ => γ ((N + 1 : ℝ)⁻¹) ^ (N + 1)) atTop (𝓝 g) from ?_)
    (Eventually.of_forall fun N => L.pow_mem (hγ _) (N + 1))
  apply tendsto_subtype_rng.mpr
  simpa only [Matrix.SpecialLinearGroup.coe_pow] using hp

/-- Exact exponential characterization of the actual tangent subspace
of a closed subgroup. This will allow measurable membership tests without
choosing differentiable curves measurably. -/
theorem mem_matrixVelocitySpace_iff_exp {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    V ∈ matrixVelocitySpace L ↔
      ∀ t : ℝ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp (t • V) := by
  constructor
  · intro hV t
    obtain ⟨γ, hγ, hd⟩ := (matrixVelocitySpace L).smul_mem t hV
    exact exists_subgroup_element_exp_velocity L hL γ hγ (t • V) hd.hasMatrixVelocity
  · intro hexp
    choose γ hγ hg using hexp
    refine ⟨γ, hγ, ?_, ?_⟩
    · apply Subtype.ext
      simp only [hg, zero_smul, NormedSpace.exp_zero,
        Matrix.SpecialLinearGroup.coe_one]
    · intro i j
      have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V)) V 0 := by
        convert hasDerivAt_exp_smul_const V (0 : ℝ) using 1 <;>
          first | rfl | simp only [zero_smul, NormedSpace.exp_zero, one_mul]
      let ev : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
        (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
      have he := ev.hasFDerivAt.comp_hasDerivAt 0 hd
      change HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V) i j) (V i j) 0 at he
      simpa only [hg] using he

end DukePrimeDegree

end

end OAI
