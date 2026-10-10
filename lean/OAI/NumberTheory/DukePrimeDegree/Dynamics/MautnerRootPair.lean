import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerMetric
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootShearing

namespace OAI

/-!
# Mautner's root-pair calculation inside the actual acting subgroup

The subgroup parameter is essential: the ambient finite measure is not
assumed invariant under all of SLₙ. The two opposite roots belong to its
invariant block group, and the isometric action is restricted to that
group. A concrete two-by-two identity supplies the diagonal fixed vector.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The elementary Gauss identity used in the Mautner argument. -/
lemma root_pair_gauss_identity {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a s : ℝ) (ha : a ≠ 0) (hs : s ≠ 0) :
    Matrix.SpecialLinearGroup.transvection hij s *
      Matrix.SpecialLinearGroup.transvection hij.symm ((a - 1) / s) *
      Matrix.SpecialLinearGroup.transvection hij (-s / a) =
    Matrix.SpecialLinearGroup.transvection hij.symm ((a - 1) / (s * a)) *
      Matrix.SpecialLinearGroup.diag2n hij a ha := by
  apply Subtype.ext
  ext p q
  rw [root_mul_entry, root_left_mul_entry, root_left_mul_entry]
  change _ = (Matrix.transvection j i ((a - 1) / (s * a)) *
    Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1)) p q
  rw [Matrix.mul_diagonal]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have hp : p = i ∨ p = j ∨ (p ≠ i ∧ p ≠ j) := by tauto
  have hq : q = i ∨ q = j ∨ (q ≠ i ∧ q ≠ j) := by tauto
  rcases hp with rfl | rfl | ⟨hpi, hpj⟩ <;>
    rcases hq with rfl | rfl | ⟨hqi, hqj⟩
  all_goals simp_all [eq_comm]
  all_goals field_simp [ha, hs] <;> ring

lemma diag2n_mem_of_opposite_roots {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (H : Subgroup (G n))
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    (a : ℝ) (ha : a ≠ 0) : Matrix.SpecialLinearGroup.diag2n hij a ha ∈ H := by
  have he := root_pair_gauss_identity hij a 1 ha one_ne_zero
  have hmem := H.mul_mem (H.mul_mem (hU 1) (hV ((a - 1) / 1))) (hU (-1 / a))
  rw [he] at hmem
  have hcancel := H.mul_mem (H.inv_mem (hV ((a - 1) / (1 * a)))) hmem
  simpa only [inv_mul_cancel_left] using hcancel

/-- Root-fixed vectors are fixed by every nonzero root-pair diagonal.
The large root parameters are never estimated directly; the isometry
removes them before taking the limit. -/
theorem diag2n_fixed_of_root_fixed {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (H : Subgroup (G n))
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y]
    (x : Y) (hfix : ∀ t : ℝ,
      (⟨Matrix.SpecialLinearGroup.transvection hij t, hU t⟩ : H) • x = x)
    (a : ℝ) (ha : a ≠ 0) :
    (⟨Matrix.SpecialLinearGroup.diag2n hij a ha,
      diag2n_mem_of_opposite_roots hij H hU hV a ha⟩ : H) • x = x := by
  let s : ℕ → ℝ := fun k => (k : ℝ) + 1
  let t : ℕ → ℝ := fun k => (a - 1) / s k
  let A : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.transvection hij (s k), hU _⟩
  let B : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.transvection hij (-s k / a), hU _⟩
  let C : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.transvection hij.symm (t k), hV _⟩
  let D : H := ⟨Matrix.SpecialLinearGroup.diag2n hij a ha,
    diag2n_mem_of_opposite_roots hij H hU hV a ha⟩
  have hs (k : ℕ) : s k ≠ 0 := by dsimp only [s]; positivity
  have hstop : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop (𝓝 0) := tendsto_const_nhds.div_atTop hstop
  have hC : Tendsto C atTop (𝓝 1) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun k => Matrix.SpecialLinearGroup.transvection hij.symm (t k))
      atTop (𝓝 (1 : G n))
    simpa only [C, Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
      (continuous_rootTransvection hij.symm).continuousAt.tendsto.comp ht
  have hsmall : Tendsto (fun k => (a - 1) / (s k * a)) atTop (𝓝 0) := by
    have he (k : ℕ) : (a - 1) / (s k * a) = t k / a := by
      dsimp only [t]
      rw [div_div]
    simp_rw [he]
    simpa only [zero_div] using ht.div_const a
  have hlim : Tendsto (fun k => A k * C k * B k) atTop (𝓝 D) := by
    apply tendsto_subtype_rng.mpr
    have he (k : ℕ) : (A k * C k * B k : H).val =
        Matrix.SpecialLinearGroup.transvection hij.symm ((a - 1) / (s k * a)) * D.val :=
      root_pair_gauss_identity hij a (s k) ha (hs k)
    simp_rw [he]
    simpa only [Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul] using
      ((continuous_rootTransvection hij.symm).continuousAt.tendsto.comp hsmall).mul_const D.val
  exact fixed_of_sandwich_tendsto x A B C D (fun k => hfix _) (fun k => hfix _) hC hlim

lemma diag2n_conjugates_opposite_root {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a t : ℝ) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha *
      Matrix.SpecialLinearGroup.transvection hij.symm t *
      (Matrix.SpecialLinearGroup.diag2n hij a ha)⁻¹ =
    Matrix.SpecialLinearGroup.transvection hij.symm (t / (a * a)) := by
  have he : Matrix.SpecialLinearGroup.diag2n hij a ha *
      Matrix.SpecialLinearGroup.transvection hij.symm t =
      Matrix.SpecialLinearGroup.transvection hij.symm (t / (a * a)) *
        Matrix.SpecialLinearGroup.diag2n hij a ha := by
    apply Subtype.ext
    ext p q
    change (Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) *
      Matrix.transvection j i t) p q =
      (Matrix.transvection j i (t / (a * a)) *
        Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1)) p q
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hp : p = i ∨ p = j ∨ (p ≠ i ∧ p ≠ j) := by tauto
    have hq : q = i ∨ q = j ∨ (q ≠ i ∧ q ≠ j) := by tauto
    rcases hp with rfl | rfl | ⟨hpi, hpj⟩ <;>
      rcases hq with rfl | rfl | ⟨hqi, hqj⟩
    all_goals simp_all [eq_comm]
    all_goals field_simp [ha]
  rw [he, mul_inv_cancel_right]

/-- In an isometric action of the actual root-pair subgroup, an upper
root fixed vector is also fixed by the opposite root. -/
theorem opposite_root_fixed_of_root_fixed {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (H : Subgroup (G n))
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y]
    (x : Y) (hfix : ∀ t : ℝ,
      (⟨Matrix.SpecialLinearGroup.transvection hij t, hU t⟩ : H) • x = x)
    (t : ℝ) :
    (⟨Matrix.SpecialLinearGroup.transvection hij.symm t, hV t⟩ : H) • x = x := by
  let s : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hs (k : ℕ) : s k ≠ 0 := by dsimp only [s]; positivity
  let D : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.diag2n hij (s k) (hs k),
    diag2n_mem_of_opposite_roots hij H hU hV _ (hs k)⟩
  let v : H := ⟨Matrix.SpecialLinearGroup.transvection hij.symm t, hV t⟩
  apply fixed_of_conjugate_tendsto x D v
  · intro k
    exact diag2n_fixed_of_root_fixed hij H hU hV x hfix _ (hs k)
  · apply tendsto_subtype_rng.mpr
    change Tendsto (fun k => (D k * v * (D k)⁻¹ : H).val) atTop (𝓝 (1 : G n))
    have he (k : ℕ) : (D k * v * (D k)⁻¹ : H).val =
        Matrix.SpecialLinearGroup.transvection hij.symm (t / (s k * s k)) :=
      diag2n_conjugates_opposite_root hij (s k) t (hs k)
    simp_rw [he]
    have hstop : Tendsto s atTop atTop :=
      tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
        tendsto_natCast_atTop_atTop
    have hi : Tendsto (fun k => (s k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hstop
    have hsmall : Tendsto (fun k => t / (s k * s k)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_inv, mul_zero] using
        tendsto_const_nhds.mul (hi.mul hi)
    simpa only [Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
      (continuous_rootTransvection hij.symm).continuousAt.tendsto.comp hsmall

end DukePrimeDegree

end

end OAI
