import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget LogCellPartition Filter

def jointMeshFactor (r : Row) (L : ℝ) (n M : ℕ) : ℝ :=
  (((meshIntervals r L)^n*M^n:ℕ):ℝ)

def smoothGrowthFactor (k : ℕ) (C σ L : ℝ) : ℝ :=
  Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)*(Real.exp (σ*L)+1))

def costCoefficient (r : Row) (k : ℕ) (C A : ℝ) : ℝ :=
  ((2:ℝ)^k+2)*(|r.a₁|+Real.log 4+1)+2*|C|+|A|

theorem jointMesh_smooth_cost_le (r : Row) (k : ℕ) (C A : ℝ) {σ L : ℝ}
    (hσ : 0 ≤ σ) (hL : 1 ≤ L) (n M : ℕ)
    (hn : n ≤ 2^k*Conclusion.bulkSize k L+2) (hM : 0 < M)
    (hmod : Real.log (M:ℝ) ≤ Real.exp (r.μ*L)) :
    jointMeshFactor r L n M*smoothGrowthFactor k C σ L*A ≤
      Real.exp (costCoefficient r k C A*((Conclusion.bulkSize k L:ℝ)+1)*
        (Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L))) := by
  let m : ℝ := (Conclusion.bulkSize k L:ℝ)+1
  let W : ℝ := Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L)
  let q : ℝ := |r.a₁|+Real.log 4+1
  let H : ℝ := Real.exp (r.δ*L)+r.a₁*L+Real.log 4+Real.exp (r.μ*L)
  let b : ℝ := (2:ℝ)^k+2
  have hLn : 0 ≤ L := by linarith
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (Conclusion.bulkSize k L) (α:=ℝ)]
  have hm0 : 0 ≤ m := by linarith
  have hl4 : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hq : 1 ≤ q := by dsimp [q]; linarith [abs_nonneg r.a₁]
  have hq0 : 0 ≤ q := by linarith
  have heσ : 1 ≤ Real.exp (σ*L) := Real.one_le_exp (mul_nonneg hσ hLn)
  have hW : 1 ≤ W := by dsimp [W]; linarith [Real.exp_pos (r.δ*L),Real.exp_pos (r.μ*L)]
  have hW0 : 0 ≤ W := by linarith
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hH0 : 0 ≤ H := by
    dsimp [H]
    have ha := row_a₁_pos r
    positivity
  have hn' : (n:ℝ) ≤ b*m := by
    have hh : (n:ℝ) ≤ (2:ℝ)^k*(Conclusion.bulkSize k L:ℝ)+2 := by exact_mod_cast hn
    dsimp [b,m]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) k]
  have hH : H ≤ q*W := by
    have h1 := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg (r.δ*L))
    have h2 := mul_le_mul_of_nonneg_right
      (show r.a₁ ≤ q by dsimp [q]; linarith [le_abs_self r.a₁]) hLn
    have h3 : Real.log 4 ≤ q*Real.exp (σ*L) := by
      apply (show Real.log 4 ≤ q by dsimp [q]; linarith [abs_nonneg r.a₁]).trans
      simpa using mul_le_mul_of_nonneg_left heσ hq0
    have h4 := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg (r.μ*L))
    dsimp [H,W]
    nlinarith
  have hcount : (n:ℝ)*H ≤ (b*q)*m*W := by
    have hh := mul_le_mul hn' hH hH0 (mul_nonneg hb0 hm0)
    convert hh using 1; ring
  have hvar : C*m*(Real.exp (σ*L)+1) ≤ (2*|C|)*m*W := by
    have hsmall : Real.exp (σ*L)+1 ≤ 2*W := by
      dsimp [W] at *
      linarith [Real.exp_pos (r.δ*L),Real.exp_pos (r.μ*L)]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) hm0) hsmall
      (by positivity : 0 ≤ Real.exp (σ*L)+1) (mul_nonneg (abs_nonneg C) hm0)
    convert hh using 1; ring
  have hA : |A| ≤ |A| *m*W := by
    have hh : 1 ≤ m*W := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (abs_nonneg A)
    simpa only [mul_one,mul_assoc] using hh'
  have htotal : (n:ℝ)*H+C*m*(Real.exp (σ*L)+1)+|A| ≤ costCoefficient r k C A*m*W := by
    dsimp [costCoefficient,b,q] at *
    nlinarith only [hcount,hvar,hA]
  have hfactor : jointMeshFactor r L n M ≤ Real.exp ((n:ℝ)*H) := by
    have hpos : 0 < jointMeshFactor r L n M := by
      unfold jointMeshFactor
      exact_mod_cast mul_pos (pow_pos (meshIntervals_pos r L) _) (pow_pos hM _)
    have hh := log_joint_mesh_card_le r hLn n M hM hmod
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr hh
  have hAexp : A ≤ Real.exp |A| := by linarith [le_abs_self A,Real.add_one_le_exp |A|]
  calc
    _ ≤ jointMeshFactor r L n M*smoothGrowthFactor k C σ L*Real.exp |A| :=
      mul_le_mul_of_nonneg_left hAexp (by unfold jointMeshFactor smoothGrowthFactor; positivity)
    _ ≤ Real.exp ((n:ℝ)*H)*smoothGrowthFactor k C σ L*Real.exp |A| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp ((n:ℝ)*H+C*m*(Real.exp (σ*L)+1)+|A|) := by
      simp only [smoothGrowthFactor,m,Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr htotal

theorem eventually_weighted_progression_decay (r : Row) (k : ℕ) (C A : ℝ)
    {σ c : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ r.δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ n M : ℕ,
      n ≤ 2^k*Conclusion.bulkSize k L+2 → 0 < M →
      Real.log (M:ℝ) ≤ Real.exp (r.μ*L) →
      jointMeshFactor r L n M*smoothGrowthFactor k C σ L*A*
        Real.exp (-c*Real.exp ((r.a₀/3)*L)) ≤ Real.exp (-Real.exp (r.target*L)) := by
  filter_upwards [eventually_joint_progression_error r k (costCoefficient r k C A) hσ hc,
    eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro n M hn hM hmod
  apply le_trans (mul_le_mul_of_nonneg_right
    (jointMesh_smooth_cost_le r k C A hσ0 hL n M hn hM hmod) (Real.exp_nonneg _))
  rw [← Real.exp_add]
  convert hbudget using 1; congr 1; ring

theorem eventually_weighted_integer_decay (r : Row) (k : ℕ) (C A : ℝ)
    {σ c : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ r.δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ n M : ℕ,
      n ≤ 2^k*Conclusion.bulkSize k L+2 → 0 < M →
      Real.log (M:ℝ) ≤ Real.exp (r.μ*L) →
      jointMeshFactor r L n M*smoothGrowthFactor k C σ L*A*
        Real.exp (-c*Real.exp (r.a₀*L)) ≤ Real.exp (-Real.exp (r.target*L)) := by
  filter_upwards [eventually_joint_integer_error r k (costCoefficient r k C A) hσ hc,
    eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro n M hn hM hmod
  apply le_trans (mul_le_mul_of_nonneg_right
    (jointMesh_smooth_cost_le r k C A hσ0 hL n M hn hM hmod) (Real.exp_nonneg _))
  rw [← Real.exp_add]
  convert hbudget using 1; congr 1; ring

end Ostmann.Arithmetic.PrimeCellActualErrorBudget

end

end OAI
