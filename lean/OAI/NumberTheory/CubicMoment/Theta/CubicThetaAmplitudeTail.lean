import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientEnergy

namespace OAI

/-! The explicit coefficient formulas give sharper tail bounds than the
uniform bound 81. Only the two ramification classes that can occur are used. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.amplitude_unramified_bound {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    R.amplitude≤3^(4-((R.order/3:ℕ):ℝ))/
      (norm (R.squarefreePart*R.cubePart^3))^(1/3:ℝ) := by
  have hc := one_le_norm (primary_ne_zero R.squarefree_primary)
  have hd := one_le_norm (primary_ne_zero R.cube_primary)
  have hs : 1≤Real.sqrt (norm R.squarefreePart) := by
    simpa using Real.sqrt_le_sqrt hc
  have hN : 0<norm (R.squarefreePart*R.cubePart^3) :=
    norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero R.squarefree_primary)
      (pow_ne_zero _ (primary_ne_zero R.cube_primary)))
  have hmul : norm (R.squarefreePart*R.cubePart^3)=
      norm R.squarefreePart*norm R.cubePart^3 := by
    simp only [norm,Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,map_pow]
  have hcube : ((norm (R.squarefreePart*R.cubePart^3))^(1/3:ℝ))^3=
      norm (R.squarefreePart*R.cubePart^3) := by
    rw [←Real.rpow_mul_natCast hN.le]
    norm_num
  have hden : (norm (R.squarefreePart*R.cubePart^3))^(1/3:ℝ)≤
      Real.sqrt (norm R.squarefreePart)*norm R.cubePart := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hN.le _) (by positivity) (by decide : 3≠0)).mp
    rw [hcube,hmul,mul_pow]
    have hsq := Real.sq_sqrt (norm_nonneg R.squarefreePart)
    have hh := mul_le_mul_of_nonneg_left hs (norm_nonneg R.squarefreePart)
    have hh' := mul_le_mul_of_nonneg_right hh (by positivity : 0≤norm R.cubePart^3)
    nlinarith
  unfold amplitude
  exact div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos hN _) hden

lemma CubicThetaCoordinates.amplitude_high_order_bound {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hk : 3≤R.order) : R.amplitude≤27 := by
  have hc := one_le_norm (primary_ne_zero R.squarefree_primary)
  have hd := one_le_norm (primary_ne_zero R.cube_primary)
  have hs : 1≤Real.sqrt (norm R.squarefreePart) := by simpa using Real.sqrt_le_sqrt hc
  have hpow : (3:ℝ)^(4-((R.order/3:ℕ):ℝ))≤27 := by
    have hk' : 1≤R.order/3 := by omega
    have hkR : (1:ℝ)≤(R.order/3:ℕ) := by exact_mod_cast hk'
    calc
      _ ≤ (3:ℝ)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 27 := by norm_num
  unfold amplitude
  exact (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hs hd)).trans hpow

lemma CubicThetaCoordinates.nonzero_order_cases {n : Eisenstein}
    (R : CubicThetaCoordinates n) (h : R.coefficient≠0) :
    (R.order=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)) ∨ 3≤R.order := by
  by_cases hk : 3≤R.order
  · exact Or.inr hk
  · left
    unfold coefficient at h
    split_ifs at h with h0 h1
    · exact (hk h0.2).elim
    · exact ⟨by omega,h1.2⟩
    · exact (h rfl).elim

end CubicFirstMoment

end

end OAI
