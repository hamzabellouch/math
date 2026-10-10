import OAI.MeasureTheory.Falconer.Shells.HighShellStationaryScale

namespace OAI

namespace PlanarFalconer

theorem source_block_dominates_slack {sig kap : ℝ} (hsig : 0 ≤ sig)
    (hpar : sig < kap/1000) (N : ℕ) :
    sig*(N:ℝ) ≤ (Nat.ceil (kap*N):ℝ) := by
  apply le_trans _ (Nat.le_ceil _)
  have : sig ≤ kap := by linarith
  exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg N)

theorem high_shell_descriptor_scale {sig v : ℝ} (hsig : 0 ≤ sig)
    (N l a t : ℕ) (hl : 2*(l:ℝ) ≤ (t:ℝ)-a)
    (hgap : 0 ≤ v-a) (hv : (t:ℝ)-sig*N ≤ v) :
    (sourceAngularRadius N sig l)⁻¹ ≤ (2:ℝ)^((v-a)/2) := by
  rw [sourceAngularRadius_inv]
  apply max_le
  · exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hsig]

theorem high_shell_extracted_scale {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) {sig v : ℝ}
    (hsig : 0 ≤ sig) (N a t j : ℕ)
    (hl : ∀ i ∈ S, 2*(descriptorLength (b i):ℝ) ≤ (t:ℝ)-a)
    (hgap : 0 ≤ v-a) (hv : (t:ℝ)-sig*N ≤ v) (hk : ∑ i ∈ S, k i ≤ 2*j) :
    (∏ i ∈ S, ((sourceAngularRadius N sig (descriptorLength (b i)))⁻¹)^(k i)) ≤
      (2:ℝ)^((j:ℝ)*(v-a)) := by
  calc
    _ ≤ ∏ i ∈ S, ((2:ℝ)^((v-a)/2))^(k i) := by
      apply Finset.prod_le_prod₀ (fun index _ =>
        pow_nonneg (inv_nonneg.mpr (sourceAngularRadius_pos N sig (descriptorLength (b index))).le) _)
      intro i hi
      exact pow_le_pow_left₀ (inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le)
        (high_shell_descriptor_scale hsig N _ a t (hl i hi) hgap hv) _
    _ = ((2:ℝ)^((v-a)/2))^(∑ i ∈ S, k i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ ((2:ℝ)^((v-a)/2))^(2*j) :=
      pow_le_pow_right₀ (Real.one_le_rpow (by norm_num) (by linarith)) hk
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring

theorem high_shell_inverse_power_split (a v r d : ℝ) (j : ℕ) :
    ((r*d)⁻¹)^j = ((2:ℝ)^(-(j:ℝ)*(v-a))) *
      ((r/(2:ℝ)^v)⁻¹)^j * ((d/(2:ℝ)^(-a))⁻¹)^j := by
  have hp : (2:ℝ)^(v-a) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have he : (2:ℝ)^(-(j:ℝ)*(v-a)) = (((2:ℝ)^(v-a))⁻¹)^j := by
    rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [he,← mul_pow,← mul_pow]
  congr 1
  rw [inv_div,inv_div,mul_inv_rev]
  have he : (2:ℝ)^v*(2:ℝ)^(-a) = (2:ℝ)^(v-a) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; rfl
  symm
  calc
    _ = r⁻¹*d⁻¹*(((2:ℝ)^(v-a))⁻¹*((2:ℝ)^v*(2:ℝ)^(-a))) := by ring
    _ = _ := by rw [he,inv_mul_cancel₀ hp]; ring

theorem high_shell_weight_cancellation {r d s : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s) :
    (d/s)^(-(1/2:ℝ))*(r*d)^(1/2:ℝ) = (r*s)^(1/2:ℝ) := by
  rw [Real.div_rpow hd.le hs.le, Real.mul_rpow hr.le hd.le,
    Real.mul_rpow hr.le hs.le]
  have he : d^(-(1/2:ℝ))*d^(1/2:ℝ) = 1 := by
    rw [← Real.rpow_add hd]; norm_num
  have hs' : s^(-(1/2:ℝ)) = (s^(1/2:ℝ))⁻¹ := Real.rpow_neg hs.le _
  rw [hs',div_inv_eq_mul]
  calc
    _ = r^(1/2:ℝ)*s^(1/2:ℝ)*(d^(-(1/2:ℝ))*d^(1/2:ℝ)) := by ring
    _ = _ := by rw [he,mul_one]

theorem high_shell_energy_prefactor (a v : ℝ) :
    (2:ℝ)^(-a)*(2:ℝ)^v*(2:ℝ)^(v-a) = (2:ℝ)^(2*(v-a)) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

end PlanarFalconer

end OAI
