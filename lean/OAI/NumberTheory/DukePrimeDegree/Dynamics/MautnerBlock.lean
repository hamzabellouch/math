import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerRootPair
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCurveExtraction

namespace OAI

/-!
# A root fixed vector is fixed by its whole coordinate block

The ambient acting group is still the specified measure stabilizer.  It
only needs to contain the root groups inside the chosen coordinate set.
The root-pair diagonal contracts every root touching its first pivot;
commutators then supply the remaining roots of that coordinate block.
This is the fixed-vector step for using a genuine unipotent ergodic flow
on a component of one block group, without a diagonal-ergodicity premise.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonalOneParameter_rootPair_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) :
    diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j) t =
      Matrix.SpecialLinearGroup.diag2n hij (Real.exp t) (Real.exp_ne_zero t) := by
  apply Subtype.ext
  apply congrArg Matrix.diagonal
  funext k
  by_cases hki : k = i
  · subst k
    simp [rootIsolationWeights, hij]
  · by_cases hkj : k = j
    · subst k
      simp [rootIsolationWeights, hij.symm, Real.exp_neg]
    · simp [rootIsolationWeights, hki, hkj]

/-- A diagonal group that fixes a vector also fixes each root with
nonzero weight.  The contracting times are chosen explicitly. -/
theorem root_fixed_of_diagonal_fixed {n : ℕ}
    (H : Subgroup (G n)) (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (hD : ∀ t, diagonalOneParameter ell hell t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y] (x : Y)
    (hfix : ∀ t : ℝ, (⟨diagonalOneParameter ell hell t, hD t⟩ : H) • x = x)
    {p q : Fin n} (hpq : p ≠ q)
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hpq t ∈ H)
    (hw : ell p ≠ ell q) (s : ℝ) :
    (⟨Matrix.SpecialLinearGroup.transvection hpq s, hU s⟩ : H) • x = x := by
  let times : ℕ → ℝ := fun k => -(k : ℝ) / (ell p - ell q)
  let D : ℕ → H := fun k => ⟨diagonalOneParameter ell hell (times k), hD _⟩
  let u : H := ⟨Matrix.SpecialLinearGroup.transvection hpq s, hU s⟩
  apply fixed_of_conjugate_tendsto x D u (fun k => hfix (times k))
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k => (D k * u * (D k)⁻¹ : H).val) atTop (𝓝 (1 : G n))
  have hweight : ell p - ell q ≠ 0 := sub_ne_zero.mpr hw
  have he (k : ℕ) : (D k * u * (D k)⁻¹ : H).val =
      Matrix.SpecialLinearGroup.transvection hpq (Real.exp (-(k : ℝ)) * s) := by
    change diagonalOneParameter ell hell (times k) *
      Matrix.SpecialLinearGroup.transvection hpq s *
      (diagonalOneParameter ell hell (times k))⁻¹ = _
    rw [← diagonalOneParameter_neg, diagonal_conjugation_transvection]
    have ht : (ell p - ell q) * times k = -(k : ℝ) := by
      dsimp only [times]
      field_simp [hweight]
    rw [ht]
  have hparam : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ)) * s) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).mul_const s
  simp_rw [he]
  simpa only [Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
    (continuous_rootTransvection hpq).continuousAt.tendsto.comp hparam

/-- Only the roots with both endpoints in `S` are used.  In particular,
the theorem does not assert ergodicity of a root across distinct blocks. -/
theorem block_roots_fixed_of_one_root_fixed {n : ℕ}
    (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (H : Subgroup (G n))
    (hroot : ∀ p ∈ S, ∀ q ∈ S, ∀ (hpq : p ≠ q) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hpq t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y] (x : Y)
    (hfix : ∀ t : ℝ,
      (⟨Matrix.SpecialLinearGroup.transvection hij t, hroot i hi j hj hij t⟩ : H) • x = x)
    (p : Fin n) (hp : p ∈ S) (q : Fin n) (hq : q ∈ S)
    (hpq : p ≠ q) (t : ℝ) :
    (⟨Matrix.SpecialLinearGroup.transvection hpq t, hroot p hp q hq hpq t⟩ : H) • x = x := by
  let ell := rootIsolationWeights i j
  have hell : ∑ k, ell k = 0 := rootIsolationWeights_sum i j
  have hD (a : ℝ) : diagonalOneParameter ell hell a ∈ H := by
    rw [diagonalOneParameter_rootPair_eq hij]
    exact diag2n_mem_of_opposite_roots hij H (hroot i hi j hj hij)
      (hroot j hj i hi hij.symm) _ (Real.exp_ne_zero a)
  have hDx (a : ℝ) : (⟨diagonalOneParameter ell hell a, hD a⟩ : H) • x = x := by
    have h := diag2n_fixed_of_root_fixed hij H (hroot i hi j hj hij)
      (hroot j hj i hi hij.symm) x hfix (Real.exp a) (Real.exp_ne_zero a)
    have he : (⟨diagonalOneParameter ell hell a, hD a⟩ : H) =
        ⟨Matrix.SpecialLinearGroup.diag2n hij (Real.exp a) (Real.exp_ne_zero a),
          diag2n_mem_of_opposite_roots hij H (hroot i hi j hj hij)
            (hroot j hj i hi hij.symm) _ (Real.exp_ne_zero a)⟩ :=
      Subtype.ext (diagonalOneParameter_rootPair_eq hij a)
    rw [he]
    exact h
  have hweight (k : Fin n) (hki : k ≠ i) : ell k ≠ ell i := by
    by_cases hkj : k = j
    · subst k
      norm_num [ell, rootIsolationWeights, hij, hij.symm]
    · simp [ell, rootIsolationWeights, hki, hkj, hij]
  have hpivot (k : Fin n) (hk : k ∈ S) (hki : k ≠ i) (s : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hki s, hroot k hk i hi hki s⟩ : H) • x = x :=
    root_fixed_of_diagonal_fixed H ell hell hD x hDx hki
      (hroot k hk i hi hki) (hweight k hki) s
  have hpivot' (k : Fin n) (hk : k ∈ S) (hik : i ≠ k) (s : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hik s, hroot i hi k hk hik s⟩ : H) • x = x :=
    root_fixed_of_diagonal_fixed H ell hell hD x hDx hik
      (hroot i hi k hk hik) (Ne.symm (hweight k hik.symm)) s
  by_cases hpi : p = i
  · subst p
    exact hpivot' q hq hpq t
  by_cases hqi : q = i
  · subst q
    exact hpivot p hp hpq t
  have hiq : i ≠ q := Ne.symm hqi
  let a (s : ℝ) : H := ⟨Matrix.SpecialLinearGroup.transvection hpi s,
    hroot p hp i hi hpi s⟩
  let b (s : ℝ) : H := ⟨Matrix.SpecialLinearGroup.transvection hiq s,
    hroot i hi q hq hiq s⟩
  have he : a t * b 1 * a (-t) * b (-1) =
      (⟨Matrix.SpecialLinearGroup.transvection hpq t,
        hroot p hp q hq hpq t⟩ : H) := by
    apply Subtype.ext
    simpa only [a, b, Subgroup.coe_mul, Subgroup.coe_mk, mul_one] using
      transvection_chain_commutator hpi hiq hpq t (1 : ℝ)
  have ha_fixed (s : ℝ) : a s • x = x := hpivot p hp hpi s
  have hb_fixed (s : ℝ) : b s • x = x := hpivot' q hq hiq s
  rw [← he]
  simp only [mul_smul, ha_fixed, hb_fixed]

end DukePrimeDegree

end

end OAI
