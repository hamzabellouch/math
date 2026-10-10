import OAI.NumberTheory.JointDickman.Analysis.LaplaceCutoff

namespace OAI

/-! # Laplace tails with the shrinking cutoff of the zero-free contour -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem stretched_exp_isLittleO_rpow {a α : ℝ} (ha : 0 < a) (hα : 0 < α) (b : ℝ) :
    (fun L : ℝ => Real.exp (-a*L^α)) =o[atTop] (fun L => L^b) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop ha (b/α)).comp_tendsto
    (tendsto_rpow_atTop hα)
  apply h.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  dsimp only [Function.comp_apply]
  rw [←Real.rpow_mul hL.le]
  congr 1
  field_simp

theorem fractional_laplace_moving_tail_isBigO {z : ℝ} (hz1 : z < 1)
    {η : ℝ → ℝ} (hη : ∀ᶠ L in atTop, 0 ≤ η L) (j : ℕ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi (η L), t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =O[atTop] (fun L => Real.exp (-(L*η L/2))) := by
  refine isBigO_iff.mpr ⟨Real.Gamma ((j:ℝ)+1-z),?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hη] with L hL hηL
  have hL0 : 0 < L := by linarith
  have hn : 0 ≤ ∫ t : ℝ in Ioi (η L), t^((j:ℝ)-z)*Real.exp (-(L*t)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hηL.trans ht.le) _) (Real.exp_pos _).le
  have hg : 0 ≤ Real.Gamma ((j:ℝ)+1-z) :=
    (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)).le
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(L*η L/2))*(L/2)^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) :=
      fractional_laplace_tail_bound hz1 hL0 hηL j
    _ ≤ Real.exp (-(L*η L/2))*1*Real.Gamma ((j:ℝ)+1-z) := by
      apply mul_le_mul_of_nonneg_right _ hg
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    _ = _ := by ring

theorem fractional_laplace_moving_tail_isLittleO {z a α : ℝ} (hz1 : z < 1)
    (ha : 0 < a) (hα : 0 < α) {η : ℝ → ℝ}
    (hη : ∀ᶠ L in atTop, 0 ≤ η L)
    (hgrowth : ∀ᶠ L in atTop, a*L^α ≤ L*η L/2) (j : ℕ) (b : ℝ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi (η L), t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =o[atTop] (fun L => L^b) := by
  apply (fractional_laplace_moving_tail_isBigO hz1 hη j).trans_isLittleO
  apply IsBigO.trans_isLittleO (g := fun L : ℝ => Real.exp (-a*L^α)) _
    (stretched_exp_isLittleO_rpow ha hα b)
  apply isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [hgrowth] with L hL
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  exact Real.exp_le_exp.mpr (by linarith)

end JointDickman

end OAI
