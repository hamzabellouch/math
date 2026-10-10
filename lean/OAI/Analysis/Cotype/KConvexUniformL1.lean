import OAI.Analysis.Cotype.UniformL1
import OAI.Analysis.Cotype.RademacherComparison

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem radProjection_kernel {n : ℕ} (x : Cube n → X) (ε : Cube n) :
    radProjection X x ε = ∑ u : Cube n,
      ((Fintype.card (Cube n) : ℝ)⁻¹ * ∑ i, sign (ε i)*sign (u i)) • x u := by
  simp only [radProjection, rademacherSum, moment, average,
    Finset.smul_sum, smul_smul, Finset.sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem scalar_sign_row_L2 {n : ℕ} (ε : Cube n) :
    cubeL2 ℝ (rademacherSum ℝ (fun i => sign (ε i))) = Real.sqrt n := by
  apply (sq_eq_sq₀ (cubeL2_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [scalar_rademacher_L2_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp [pow_two, sign_sq]

theorem radProjection_l1Family_pointwise {n : ℕ} {x : Cube n → X} {c : ℝ}
    (hc : 0 ≤ c) (hx : L1Family x c) (ε : Cube n) :
    c * Real.sqrt n ≤ 4 * ‖radProjection X x ε‖ := by
  let a : Cube n → ℝ := fun u =>
    (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ i, sign (ε i)*sign (u i)
  have hsum : (∑ u, |a u|) =
      average (fun u => ‖rademacherSum ℝ (fun i => sign (ε i)) u‖) := by
    simp only [a, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card (Cube n) : ℝ)⁻¹ by positivity),
      ← Finset.mul_sum, average, smul_eq_mul, Real.norm_eq_abs, rademacherSum]
    congr 2
    funext u
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hl := hx.2 a
  rw [hsum, ← radProjection_kernel x ε] at hl
  have hk := rademacher_L2_le_four_L1 (fun i => sign (ε i))
  rw [scalar_sign_row_L2] at hk
  nlinarith [mul_le_mul_of_nonneg_left hk hc]

theorem sqrt_le_of_kBound_l1Family {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (h : ∀ (n : ℕ) (f : Cube n → X), cubeL2 X (radProjection X f) ≤ K*cubeL2 X f)
    {n : ℕ} {x : Cube n → X} (hx : L1Family x c) :
    c * Real.sqrt n ≤ 4*K := by
  have hl : c * Real.sqrt n / 4 ≤ cubeL2 X (radProjection X x) := by
    have hh := cubeL2_mono (fun ε : Cube n => show
        ‖(c * Real.sqrt n / 4 : ℝ)‖ ≤ ‖radProjection X x ε‖ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [radProjection_l1Family_pointwise hc.le hx ε])
    simpa only [cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ c*Real.sqrt n/4)] using hh
  have hu := (h n x).trans (mul_le_of_le_one_right hK (cubeL2_bound (by norm_num) hx.1))
  linarith

theorem not_uniformL1_of_kConvex (h : KConvex X) : ¬ UniformL1 X := by
  obtain ⟨K,hK,h⟩ := h
  intro hu
  obtain ⟨L,hL,hx⟩ := uniformL1_iff_cube.mp hu
  obtain ⟨n,hn⟩ := exists_nat_gt ((4*K*L)^2)
  obtain ⟨x,hx⟩ := hx n
  have hb := sqrt_le_of_kBound_l1Family hK (inv_pos.mpr hL) h hx
  have he : L*(L⁻¹*Real.sqrt n) = Real.sqrt n := by field_simp
  have hb' : Real.sqrt n ≤ 4*K*L := by
    have hh := mul_le_mul_of_nonneg_left hb hL.le
    rw [he] at hh
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hp : 0 ≤ 4*K*L := by positivity
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

end Cotype

end

end OAI
