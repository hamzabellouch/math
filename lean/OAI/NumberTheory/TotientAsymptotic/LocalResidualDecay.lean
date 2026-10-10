import OAI.NumberTheory.TotientAsymptotic.LocalPrimeSupport

namespace OAI

/-! Summable numerical bounds for the local residual reciprocal masses. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localPrimeHeight_linear_geometric {A : ℝ} (hA : 0 ≤ A) (L : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ h : ℕ,
      localPrimeHeight A L h ≤ C*((h:ℝ)+1)*(rho^h)⁻¹ := by
  let C := A*(L+2:ℕ)*(rho^(L+2))⁻¹+2
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _))
        (inv_pos.mpr (pow_pos rho_pos _)).le) (by norm_num)
  · intro h
    have hk : (h+L+2:ℕ) ≤ (L+2:ℕ)*((h:ℝ)+1) := by
      push_cast
      nlinarith only [Nat.cast_nonneg (α:=ℝ) L,Nat.cast_nonneg (α:=ℝ) h]
    have hinv : 1 ≤ (rho^h)⁻¹ :=
      (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
    have hh : 1 ≤ ((h:ℝ)+1)*(rho^h)⁻¹ :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α:=ℝ) h; linarith) hinv
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hA)
      (mul_nonneg (inv_pos.mpr (pow_pos rho_pos h)).le
        (inv_pos.mpr (pow_pos rho_pos (L+2))).le)
    unfold localPrimeHeight
    rw [show h+L+2=h+(L+2) by omega,pow_add,mul_inv]
    dsimp [C]
    push_cast at hmul ⊢
    nlinarith only [hmul,hh]

theorem local_residual_mass_decay {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (L : ℕ) :
    ∀ᶠ h : ℕ in atTop,C*localPrimeHeight A L h*rho^(3*h) ≤ rho^h := by
  obtain ⟨D,hD,hbound⟩ := localPrimeHeight_linear_geometric hA L
  have ht : Tendsto (fun h : ℕ => C*D*((h:ℝ)+1)*rho^h) atTop (nhds 0) := by
    have hlin := tendsto_pow_const_mul_const_pow_of_lt_one 1 rho_pos.le rho_lt_one
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one
    convert (hlin.add hpow).const_mul (C*D) using 1
    · funext h
      simp only [pow_one]
      ring_nf
    · ring_nf
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with h hh
  have hsmall : C*D*((h:ℝ)+1)*rho^h ≤ 1 := hh.le
  have hr : rho^h ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have hpow : rho^(3*h)=(rho^h)^3 := by rw [←pow_mul]; congr 1; omega
  have he : C*(D*((h:ℝ)+1)*(rho^h)⁻¹)*rho^(3*h) =
      (C*D*((h:ℝ)+1)*rho^h)*rho^h := by
    rw [hpow]
    field_simp
  calc
    _ ≤ C*(D*((h:ℝ)+1)*(rho^h)⁻¹)*rho^(3*h) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound h) hC)
        (pow_pos rho_pos _).le
    _ = (C*D*((h:ℝ)+1)*rho^h)*rho^h := he
    _ ≤ rho^h := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hsmall (pow_pos rho_pos h).le

lemma local_geometric_inverse_fourth {c t : ℝ} {h : ℕ}
    (hc : 0 < c) (ht : c*(rho^h)⁻¹ ≤ t) :
    t^(-4:ℝ) ≤ (c^4)⁻¹*rho^(4*h) := by
  have hc0 : 0 < c*(rho^h)⁻¹ := mul_pos hc (inv_pos.mpr (pow_pos rho_pos _))
  have ht0 : 0 < t := hc0.trans_le ht
  have hh := inv_anti₀ (pow_pos hc0 4) (pow_le_pow_left₀ hc0.le ht 4)
  have he : t^(-4:ℝ)=(t^4)⁻¹ := by
    rw [Real.rpow_neg ht0.le]
    norm_num
  rw [he]
  apply hh.trans_eq
  rw [mul_pow,inv_pow,mul_inv,inv_inv,←pow_mul]
  congr 1
  congr 1
  omega

end TotientAsymptotic

end

end OAI
