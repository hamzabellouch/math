import OAI.MeasureTheory.Falconer.Slicing.SliceBudget

namespace OAI

/-! # The concrete polynomial thresholds in Gaussian slice selection -/

namespace Falconer
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem slice_cube_ratio_le {K X : ℝ} (hK : 0 < K) (hX : X ≤ K) :
    X/K^3 ≤ 1/K^2 := by
  apply (div_le_iff₀ (pow_pos hK 3)).mpr
  calc
    X ≤ K := hX
    _ = (1/K^2)*K^3 := by field_simp

theorem gaussian_point_scale_cost {K C : ℝ} (hK : 0 < K)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*B i)*ENNReal.ofReal (K^3) ≤
      ENNReal.ofReal (1/K^2) := by
  have hs := pruning_real_weighted_sum (pow_pos hK 6) w hw B hB
  have he : ((Fintype.card ι:ℝ)*C/K^6)*K^3 = (Fintype.card ι:ℝ)*C/K^3 := by
    field_simp
  calc
    _ ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*C/K^6)*ENNReal.ofReal (K^3) := mul_le_mul' hs le_rfl
    _ = ENNReal.ofReal (((Fintype.card ι:ℝ)*C/K^6)*K^3) := by
      rw [← ENNReal.ofReal_mul' (by positivity : 0 ≤ K^3)]
    _ ≤ _ := by rw [he]; exact ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hcard)

theorem gaussian_direction_scale_cost {K C S : ℝ} (hK : 0 < K) (hS : 0 ≤ S)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    ENNReal.ofReal S*(∑ i, (ENNReal.ofReal (K^3*w i))⁻¹*B i) ≤
      ENNReal.ofReal (S/K^2) := by
  have hs := (pruning_real_weighted_sum (pow_pos hK 3) w hw B hB).trans
    (ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hcard))
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (1/K^2) := mul_le_mul' le_rfl hs
    _ = _ := by rw [← ENNReal.ofReal_mul hS]; congr 1; ring

theorem gaussian_mass_scale_cost {K C S : ℝ} (hK : 0 < K) (hS : 0 ≤ S)
    (hC : C ≤ K) {Q : ℝ≥0∞} (hQ : Q ≤ ENNReal.ofReal C) :
    ENNReal.ofReal S*((ENNReal.ofReal (K^3))⁻¹*Q) ≤ ENNReal.ofReal (S/K^2) := by
  have hs : (ENNReal.ofReal (K^3))⁻¹*Q ≤ ENNReal.ofReal (1/K^2) := by
    calc
      _ ≤ (ENNReal.ofReal (K^3))⁻¹*ENNReal.ofReal C := mul_le_mul' le_rfl hQ
      _ = ENNReal.ofReal (C/K^3) := by
        rw [mul_comm]
        change ENNReal.ofReal C / ENNReal.ofReal (K^3) = _
        rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 3)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hC)
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (1/K^2) := mul_le_mul' le_rfl hs
    _ = _ := by rw [← ENNReal.ofReal_mul hS]; congr 1; ring

theorem gaussian_active_scale_cost {K w N R : ℝ} (hK : 0 < K) (hw : 0 < w)
    (hN : 0 < N) (hR : 0 < R) (h : ℕ) :
    ENNReal.ofReal (K^6*w)*
      (ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
        ENNReal.ofReal (K^11*(w*(N*(2*R)^h))))*ENNReal.ofReal (K^3) =
      ENNReal.ofReal (1/K^2) := by
  have hp : 0 < (2*R)^h := pow_pos (by positivity) h
  have hd : 0 < K^11*(w*(N*(2*R)^h)) := by positivity
  rw [← ENNReal.ofReal_mul hN.le,← ENNReal.ofReal_div_of_pos hd,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ K^6*w),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (K^6*w)*((N*(2*R)^h)/(K^11*(w*(N*(2*R)^h)))))]
  congr 1
  field_simp [hK.ne',hw.ne',hN.ne',hp.ne']

theorem gaussian_four_polynomial_costs {K C S w₀ N R : ℝ}
    (hK : 0 < K) (hS : 0 ≤ S) (hw₀ : 0 < w₀) (hN : 0 < N) (hR : 0 < R)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K) (hC : C ≤ K)
    (hlarge : 4*(1+2*S+1) ≤ K)
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (CP CD : ι → ℝ≥0∞) (hCP : ∀ i, CP i ≤ ENNReal.ofReal (C*w i))
    (hCD : ∀ i, CD i ≤ ENNReal.ofReal (C*v i))
    (h : ℕ) {base Q : ℝ≥0∞}
    (hbase : base ≤ ENNReal.ofReal (1/(4*K))) (hQ : Q ≤ ENNReal.ofReal C) :
    base + (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*CP i)*ENNReal.ofReal (K^3) +
      ENNReal.ofReal S*(∑ i, (ENNReal.ofReal (K^3*v i))⁻¹*CD i) +
      ENNReal.ofReal S*((ENNReal.ofReal (K^3))⁻¹*Q) +
      ENNReal.ofReal (K^6*w₀)*
        (ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
          ENNReal.ofReal (K^11*(w₀*(N*(2*R)^h))))*ENNReal.ofReal (K^3) <
      ENNReal.ofReal (1/K) := by
  apply slice_four_cost_budget hK hS (show (0:ℝ) ≤ 1 by norm_num) hlarge hbase
    (gaussian_point_scale_cost hK hcard w hw CP hCP)
    (gaussian_direction_scale_cost hK hS hcard v hv CD hCD)
    (gaussian_mass_scale_cost hK hS hC hQ)
  exact (gaussian_active_scale_cost hK hw₀ hN hR h).le

end Falconer

end OAI
