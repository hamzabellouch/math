import OAI.Geometry.EinsteinFour.JacobiMeshCoefficient
import OAI.Geometry.EinsteinFour.JacobiWronskian
import OAI.Geometry.EinsteinFour.JacobiDirichletPositivity

namespace OAI

/-! From uniform preconjugate approximation to positive curvature matrices. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The exact Wronskian, uniform inverse bounds and endpoint normalization
give positivity of the full discrete curvature matrix on a fine mesh. -/
theorem curvatureDirichlet_eventually_posDef_of_approximation
    {t : ℝ} (ht : 0 < t) (R : ℕ → ℕ → NormalMatrix)
    (hR : ∀ N i, (R N i)ᵀ = R N i)
    {B V : ℝ → NormalMatrix}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hV : ContinuousOn V (Set.Icc 0 t))
    (hB0 : B 0 = 1) (hV0 : V 0 = 1)
    (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s))
    {eB eV : ℕ → ℝ} (heB : Tendsto eB atTop (nhds 0)) (heV : Tendsto eV atTop (nhds 0))
    (hb : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N + 1 →
      ‖relativeDiscretePosition (R N) (t / (N + 1)) i -
        B ((i : ℝ) * (t / (N + 1)))‖ ≤ eB N)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, i ≤ N →
      ‖discreteVelocity (R N) (t / (N + 1)) (i + 1) -
        V ((i : ℝ) * (t / (N + 1)))‖ ≤ eV N) :
    ∀ᶠ N : ℕ in atTop,
      (curvatureDirichlet t (fun i : Fin N => R N (i.val + 1) - 1)).PosDef := by
  let C : ℝ → NormalMatrix := fun s => V s * Ring.inverse (B s)
  have hC : ContinuousOn C (Set.Icc 0 t) := inverse_product_continuousOn hB hV hunit
  have hC0 : C 0 = 1 := by simp [C, hB0, hV0, Ring.inverse_one]
  obtain ⟨e, he, hcoef⟩ := mesh_inverse_product_converges ht.le hB hV hunit heB heV hb hv
  have happrox : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 0 < i → i ≤ N →
      ‖pivotCoefficient (R N) (t / (N + 1)) i -
        C ((i : ℝ) * (t / (N + 1)))‖ ≤ e N := by
    filter_upwards [hcoef] with N hN i _ hi
    simpa only [pivotCoefficient, Matrix.nonsing_inv_eq_ringInverse, C] using (hN i hi).2
  have hsym : ∀ N i : ℕ,
      ((1 : NormalMatrix) + ((1 : ℝ) / i) • pivotCoefficient (R N) (t / (N + 1)) i)ᵀ =
        1 + ((1 : ℝ) / i) • pivotCoefficient (R N) (t / (N + 1)) i := by
    intro N i
    exact one_add_pivotCoefficient_symmetric (R N)
      (ne_of_gt (div_pos ht (by positivity))) (hR N) i
  have hpos := eventually_matrix_ratio_posDef ht hC hC0 he happrox hsym
  obtain ⟨K, _, hinv⟩ := eventually_mesh_inverse_bounds ht.le hB hunit heB hb
  filter_upwards [hpos, hinv] with N hp hi
  let h : ℝ := t / (N + 1)
  have hh : 0 < h := div_pos ht (by positivity)
  have hxunit (i : ℕ) (hi0 : 1 ≤ i) (hiN : i ≤ N + 1) :
      IsUnit (discretePosition (R N) h i) := by
    have hbi := (hi i hiN).1
    rw [relativeDiscretePosition_pos _ _ (by omega)] at hbi
    exact isUnit_of_divided_time (mul_ne_zero (by exact_mod_cast (by omega : i ≠ 0)) hh.ne') hbi
  have hyunit (i : ℕ) (hi0 : 1 ≤ i) (hiN : i ≤ N + 1) :
      IsUnit (normalizedDiscrete (R N) h i).det := by
    have hs : IsUnit (algebraMap ℝ NormalMatrix h⁻¹) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hh.ne')).map (algebraMap ℝ NormalMatrix)
    have hu : IsUnit (normalizedDiscrete (R N) h i) := by
      simpa only [normalizedDiscrete, Algebra.smul_def] using hs.mul (hxunit i hi0 hiN)
    exact (Matrix.isUnit_iff_isUnit_det _).mp hu
  apply curvatureDirichlet_posDef_of_ratios ht.ne' (R N) hyunit
  intro i hi0 hiN
  have hxdet := (Matrix.isUnit_iff_isUnit_det _).mp (hxunit i hi0 (hiN.trans (Nat.le_succ N)))
  rw [normalizedDiscrete_ratio _ hh.ne' i hxdet,
    discretePosition_ratio _ hh.ne' (by omega) hxdet]
  exact hp i (by omega) hiN

end

end PositiveEinsteinFour.Jacobi

end OAI
