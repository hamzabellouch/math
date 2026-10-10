import OAI.NumberTheory.DukePrimeDegree.Dynamics.MatrixVelocitySpace
import OAI.NumberTheory.DukePrimeDegree.Geometry.MatrixPowerApproximation

namespace OAI

/-!
# Recovering an actual root element from a pure root velocity

A curve in a closed subgroup whose velocity is one elementary matrix
produces the corresponding root element by taking growing powers at
reciprocal times. The proof compares those powers with the exact powers
of a transvection. No diagonal normalization of the subgroup is needed.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

lemma hasIdentityMatrixDerivative_rootCurve {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (v : ℝ) :
    HasIdentityMatrixDerivative
      (fun t => Matrix.SpecialLinearGroup.transvection hij (t * v))
      (Matrix.single i j v) := by
  refine ⟨by simp only [zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero], ?_⟩
  intro a b
  have hentry : (fun t =>
      (Matrix.SpecialLinearGroup.transvection hij (t * v)).val a b) =
      fun t => (1 : Matrix (Fin n) (Fin n) ℝ) a b +
        t * (Matrix.single i j v) a b := by
    funext t
    simp only [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> ring
  rw [hentry]
  convert (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℝ) a b)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const ((Matrix.single i j v) a b)) using 1
  · funext t
    rfl
  · simp only [zero_add, one_mul]

lemma transvection_nat_pow {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : ℝ) (N : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij v ^ N =
      Matrix.SpecialLinearGroup.transvection hij ((N : ℝ) * v) := by
  induction N with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ N ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

/-- Entrywise first-order control gives the norm control needed for
growing products. All matrices here use the submultiplicative operator
norm. -/
theorem tendsto_powers_of_pure_root_velocity {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (γ : ℝ → G n) (v : ℝ)
    (hvelocity : HasMatrixVelocity γ (Matrix.single i j v)) :
    Tendsto (fun N : ℕ => γ ((N + 1 : ℝ)⁻¹) ^ (N + 1)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hij v)) := by
  let : Nonempty (Fin n) := ⟨i⟩
  let k : ℕ → ℝ := fun N => N + 1
  let s : ℕ → ℝ := fun N => (k N)⁻¹
  let V : Matrix (Fin n) (Fin n) ℝ := Matrix.single i j v
  let A : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => (γ (s N)).val
  let B : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => 1 + s N • V
  let D : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => k N • (A N - 1)
  let C : ℝ := ‖V‖ + 1
  have hk (N : ℕ) : 0 < k N := by dsimp only [k]; positivity
  have hs (N : ℕ) : 0 < s N := inv_pos.mpr (hk N)
  have hstop : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hs0 : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hstop
  have hD : Tendsto D atTop (𝓝 V) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    simpa only [Function.comp_def, D, A, V, s, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, div_eq_mul_inv, inv_inv, mul_comm] using
      (hvelocity a b).comp hs0
  have hDbound : ∀ᶠ N in atTop, ‖D N‖ ≤ C := by
    have he := hD.norm.eventually (Iio_mem_nhds (show ‖V‖ < C by dsimp [C]; linarith))
    exact he.mono fun _ h => h.le
  have hAB (N : ℕ) : k N • (A N - B N) = D N - V := by
    have he : A N - B N = (A N - 1) - s N • V := by
      dsimp only [B]
      abel
    rw [he, smul_sub, smul_smul]
    change D N - (k N * (k N)⁻¹) • V = D N - V
    rw [mul_inv_cancel₀ (ne_of_gt (hk N)), one_smul]
  have herr : Tendsto (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) atTop (𝓝 0) := by
    have he := (hD.sub_const V).norm
    have he' : (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) =
        fun N => ‖D N - V‖ := by
      funext N
      rw [← hAB, norm_smul, Real.norm_eq_abs, abs_of_pos (hk N)]
    rw [he']
    simpa only [sub_self, norm_zero] using he
  have hA : ∀ᶠ N in atTop, ‖A N‖ ≤ Real.exp (C / (N + 1 : ℝ)) := by
    filter_upwards [hDbound] with N hN
    have hres : ‖A N - 1‖ ≤ C / k N := by
      apply (le_div_iff₀ (hk N)).mpr
      simpa only [D, norm_smul, Real.norm_eq_abs, abs_of_pos (hk N), mul_comm] using hN
    calc
      ‖A N‖ = ‖(A N - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖A N - 1‖ + ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
      _ ≤ C / k N + 1 := add_le_add hres (le_of_eq norm_one)
      _ ≤ Real.exp (C / k N) := Real.add_one_le_exp _
      _ = _ := rfl
  have hB : ∀ᶠ N in atTop, ‖B N‖ ≤ Real.exp (C / (N + 1 : ℝ)) := by
    apply Eventually.of_forall
    intro N
    have hres : ‖s N • V‖ ≤ C / k N := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hs N)]
      change (k N)⁻¹ * ‖V‖ ≤ C / k N
      rw [mul_comm, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by dsimp [C]; linarith) (hk N).le
    calc
      ‖B N‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ + ‖s N • V‖ := norm_add_le _ _
      _ ≤ 1 + C / k N := add_le_add (le_of_eq norm_one) hres
      _ ≤ Real.exp (C / k N) := by simpa only [add_comm] using Real.add_one_le_exp (C / k N)
      _ = _ := rfl
  have hpowers := tendsto_matrix_power_difference_zero A B C
    (show 0 ≤ C by dsimp [C]; positivity) hA hB herr
  have hBroot (N : ℕ) : B N =
      (Matrix.SpecialLinearGroup.transvection hij (v / k N)).val := by
    change 1 + s N • Matrix.single i j v = _
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.smul_single]
    congr 2
    change (k N)⁻¹ * v = v / k N
    rw [mul_comm, ← div_eq_mul_inv]
  have hBpow (N : ℕ) : B N ^ (N + 1) =
      (Matrix.SpecialLinearGroup.transvection hij v).val := by
    rw [hBroot, ← Matrix.SpecialLinearGroup.coe_pow, transvection_nat_pow]
    have he : (↑(N + 1) : ℝ) * (v / k N) = v := by
      have hcast : (↑(N + 1) : ℝ) = k N := by simp [k]
      rw [hcast]
      exact mul_div_cancel₀ _ (ne_of_gt (hk N))
    rw [he]
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [A, s, k, hBpow, Matrix.SpecialLinearGroup.coe_pow] using hpowers

/-- A pure root tangent direction in a closed matrix subgroup already
gives an actual root element of that subgroup. -/
theorem root_mem_of_pure_matrix_velocity {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (γ : ℝ → G n) (hγ : ∀ t, γ t ∈ L) (v : ℝ)
    (hvelocity : HasMatrixVelocity γ (Matrix.single i j v)) :
    Matrix.SpecialLinearGroup.transvection hij v ∈ L := by
  exact hclosed.mem_of_tendsto (tendsto_powers_of_pure_root_velocity hij γ v hvelocity)
    (Eventually.of_forall fun N => L.pow_mem (hγ _) (N + 1))

theorem root_mem_of_velocitySpace {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (v : ℝ) (hV : Matrix.single i j v ∈ matrixVelocitySpace L) :
    Matrix.SpecialLinearGroup.transvection hij v ∈ L := by
  obtain ⟨γ, hγ, hvelocity⟩ := hV
  exact root_mem_of_pure_matrix_velocity hij L hclosed γ hγ v
    hvelocity.hasMatrixVelocity

/-- The elementary tangent-direction test is exactly full real-root
invariance for a closed subgroup. A single nonzero root element alone
would not suffice for this equivalence. -/
theorem root_direction_mem_velocitySpace_iff {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n))) :
    Matrix.single i j (1 : ℝ) ∈ matrixVelocitySpace L ↔
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L := by
  constructor
  · intro h t
    apply root_mem_of_velocitySpace hij L hclosed t
    have hs := (matrixVelocitySpace L).smul_mem t h
    have he : t • Matrix.single i j (1 : ℝ) = Matrix.single i j t := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rwa [he] at hs
  · intro h
    exact ⟨fun t => Matrix.SpecialLinearGroup.transvection hij (t * 1),
      fun t => h _, hasIdentityMatrixDerivative_rootCurve hij 1⟩

end DukePrimeDegree

end

end OAI
