import OAI.Geometry.RCD.Metric.CompactCenterVolumePower
import OAI.Geometry.RCD.Heat.CanonicalHeatTimeRatio

namespace OAI

/-! # Quantitative kernel bounds for compact endpoint supports -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_endpoint_kernel_upper (z : X) {R : ℝ} (hR : 1 ≤ R) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 →
      ∀ (x y : X), dist y z ≤ R → 2*R ≤ dist x z →
        hX.canonicalHeatKernel hn p t x y ≤
          A*(Real.sqrt t)⁻¹^n*Real.exp (-(dist x z)^2/(20*t)+B) := by
  obtain ⟨V,hV,hvol⟩ := hX.compact_center_volume_power hn z hR
  obtain ⟨C,B,hC,hB,hupper⟩ := hX.canonicalHeatKernel_upper_five hn p
  refine ⟨C/V,B,div_pos hC hV,hB,?_⟩
  intro t ht ht1 x y hy hx
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hvoly := hvol y hy ht ht1
  have hvol0 : 0 < (hausdorff n X).real (ball y (Real.sqrt t)) :=
    (mul_pos hV (pow_pos hs n)).trans_le hvoly
  have hratio : C/(hausdorff n X).real (ball y (Real.sqrt t)) ≤ (C/V)*(Real.sqrt t)⁻¹^n := by
    calc
      _ ≤ C/(V*(Real.sqrt t)^n) := div_le_div_of_nonneg_left hC.le (by positivity) hvoly
      _ = _ := by rw [inv_pow]; field_simp
  have htri : dist x z ≤ dist x y+R := (dist_triangle x y z).trans (add_le_add le_rfl hy)
  have hsq : (dist x z)^2/4 ≤ (dist x y)^2 := by
    nlinarith [sq_nonneg (dist x y-dist x z/2),dist_nonneg (x := x) (y := y)]
  have hf := div_le_div_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ 5*t)
  have he : ((dist x z)^2/4)/(5*t)=(dist x z)^2/(20*t) := by ring
  rw [he] at hf
  have hBt : B*t≤B := mul_le_of_le_one_right hB ht1
  have hexp : -(dist x y)^2/(5*t)+B*t ≤ -(dist x z)^2/(20*t)+B := by
    simp only [neg_div] at *
    linarith
  exact (hupper t ht x y).trans (mul_le_mul hratio (Real.exp_le_exp.mpr hexp)
    (Real.exp_pos _).le (by positivity))

theorem compact_endpoint_kernel_lower (z : X) {R : ℝ} (hR : 1 ≤ R) :
    ∃ a E : ℝ, 0 < a ∧ 0 < E ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 →
      ∀ (x y : X), dist x z ≤ R → dist y z ≤ R →
        a*Real.exp (-E/t) ≤ hX.canonicalHeatKernel hn p t x y := by
  obtain ⟨c,D,hc,hD,hlower⟩ := hX.canonicalHeatKernel_rough_gaussian_lower hn p
  let V := (hausdorff n X).real (ball z (R+1))
  have hR0 : 0 < R+1 := by linarith
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport z (R+1) hR0).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  refine ⟨c/V,D*(2*R)^2,div_pos hc hV,by positivity,?_⟩
  intro t ht ht1 x y hx hy
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs1 : Real.sqrt t ≤ 1 := by nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  have hsub : ball y (Real.sqrt t) ⊆ ball z (R+1) := by
    apply ball_subset_ball'
    linarith
  have hvol : (hausdorff n X).real (ball y (Real.sqrt t)) ≤ V :=
    measureReal_mono hsub (hX.finiteOnBounded _ isBounded_ball).ne
  have hvol0 : 0 < (hausdorff n X).real (ball y (Real.sqrt t)) :=
    ENNReal.toReal_pos (hX.fullSupport y _ hs).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hdist : dist x y ≤ 2*R := by
    have hh := dist_triangle x z y
    rw [dist_comm z y] at hh
    linarith
  have hsq : (dist x y)^2 ≤ (2*R)^2 := pow_le_pow_left₀ dist_nonneg hdist 2
  have hexp : -D*(2*R)^2/t ≤ -D*(dist x y)^2/t := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hsq (by linarith)) ht.le
  rw [← neg_mul]
  calc
    _ ≤ (c/(hausdorff n X).real (ball y (Real.sqrt t)))*Real.exp (-D*(dist x y)^2/t) :=
      mul_le_mul (div_le_div_of_nonneg_left hc.le hvol0 hvol)
        (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ ≤ _ := hlower t ht ht1 x y

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
