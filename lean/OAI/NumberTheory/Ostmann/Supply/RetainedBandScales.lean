import OAI.NumberTheory.Ostmann.Supply.TensorModeBudget

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter
open scoped BigOperators

def supplyRadius (L : ℝ) : ℕ := ⌈Real.exp (Real.exp L/2)⌉₊
def supplyTruncation (L : ℝ) : ℕ := ⌈10000*L⌉₊

theorem supplyRadius_tendsto : Tendsto supplyRadius atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    (Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.atTop_div_const (by norm_num)))

theorem supplyRadius_pos (L : ℝ) : 0<supplyRadius L :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem eventually_supplyTruncation_le_exp {r c : ℝ} (hr : 0<r) (hc : 0<c) :
    ∀ᶠL:ℝ in atTop, (2*supplyTruncation L:ℕ)≤c*Real.exp (r*L) := by
  have hb := (isLittleO_pow_exp_pos_mul_atTop 1 hr).bound
    (div_pos hc (by norm_num : (0:ℝ)<20002))
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with L hb hL
  have hceil := Nat.ceil_lt_add_one (show 0≤10000*L by positivity)
  have hk : (supplyTruncation L:ℝ)≤10001*L := by
    unfold supplyTruncation
    linarith
  simp only [pow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤L),
    abs_of_pos (Real.exp_pos _)] at hb
  have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤20002)
  push_cast
  nlinarith

theorem eventually_retainedBand_numeric :
    ∀ᶠL:ℝ in atTop, 0≤L ∧
      (2*supplyTruncation L:ℕ)*Real.exp ((9/10:ℝ)*L)≤Real.exp L/2 ∧
      (2*supplyTruncation L:ℕ)/Real.exp ((1/20:ℝ)*L)≤1/16 := by
  filter_upwards [eventually_supplyTruncation_le_exp (by norm_num : (0:ℝ)<1/10)
      (by norm_num : (0:ℝ)<1/2),
    eventually_supplyTruncation_le_exp (by norm_num : (0:ℝ)<1/20)
      (by norm_num : (0:ℝ)<1/16),eventually_ge_atTop (0:ℝ)] with L h1 h2 hL
  refine ⟨hL,?_,?_⟩
  · have h := mul_le_mul_of_nonneg_right h1 (Real.exp_pos ((9/10:ℝ)*L)).le
    have he : Real.exp ((1/10:ℝ)*L)*Real.exp ((9/10:ℝ)*L)=Real.exp L := by
      rw [←Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ ((1/2:ℝ)*Real.exp ((1/10:ℝ)*L))*Real.exp ((9/10:ℝ)*L) := h
      _ = Real.exp L/2 := by rw [mul_assoc,he]; ring
  · exact (div_le_iff₀ (Real.exp_pos _)).mpr h2

end Ostmann.Supply

end

end OAI
