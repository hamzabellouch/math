import OAI.NumberTheory.TotientAsymptotic.CollisionSuffixSize
import OAI.NumberTheory.TotientAsymptotic.NormalPrimeBands

namespace OAI

/-! Dyadic endpoints for actual shifted-prime suffixes. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma dyadic_shift_log_bound {p n : ℕ} {y : ℝ} (hp : p.Prime) (hn : 0 < n)
    (htail : Real.log (n : ℝ) ≤ (1/100 : ℝ)*Real.log p)
    (hpbig : 100*Real.log 2 ≤ Real.log p)
    (hlo : y/2 < ((p-1)*n : ℕ)) (hhi : (((p-1)*n : ℕ) : ℝ) ≤ y) :
    (0 < y) ∧ Real.log y ≤ (51/50 : ℝ)*Real.log p ∧ y^(9/10 : ℝ) ≤ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv0 : (0 : ℝ) < ((p-1)*n : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) hn
  have hy : 0 < y := hv0.trans_le hhi
  have hv : (((p-1)*n : ℕ) : ℝ) ≤ (p : ℝ)*n := by
    exact_mod_cast Nat.mul_le_mul_right n (Nat.sub_le p 1)
  have hlv := Real.log_le_log hv0 hv
  rw [Real.log_mul hp0.ne' hn0.ne'] at hlv
  have hly := Real.log_le_log hy (show y ≤ 2*(((p-1)*n : ℕ) : ℝ) by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hv0.ne'] at hly
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog : Real.log y ≤ (51/50 : ℝ)*Real.log p := by linarith
  refine ⟨hy,hlog,?_⟩
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hy _) hp0).mp
  rw [Real.log_rpow hy]
  linarith

/-- The first prime in every actual positive-index suffix lies above
`y^0.9` at its dyadic counting endpoint. The endpoint has the same Ford
band scale, uniformly over every retained index. -/
theorem collision_suffix_dyadic_size : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → i+2 ≤ L x H → L x H < m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η → ∀ y : ℝ,
    y/2 < ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) →
    (((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) : ℝ) ≤ y →
    y^(9/10 : ℝ) ≤ remainderPrime η i ∧
    (87/100 : ℝ)*fordBandScale x i ≤ B y ∧ B y ≤ (113/100 : ℝ)*fordBandScale x i := by
  filter_upwards [collision_tail_log_small,ford_band_polynomial_lower 1,
    eventually_ge_atTop 200] with H htail hpoly hH
  filter_upwards [htail,hpoly,collision_coarse_sizes] with x ht hp hc
  intro i hi hiR hiL hL η hη y hlo hhi
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa using hp i him hHi
  have hb200 : (200 : ℝ) ≤ fordBandScale x i := by
    have hh : 200 ≤ m x-i := hH.trans hHi
    have hhR : (200 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hh
    exact hhR.trans hb
  obtain ⟨hbl,hbu,_⟩ := hc H i hi hiL hL η hη
  have hprime := (hη.2.1 i (Finset.mem_Icc.mpr ⟨hi,by omega⟩)).1
  have hprime1 : (1 : ℝ) < remainderPrime η i := by exact_mod_cast hprime.one_lt
  have hexp : Real.exp ((22/25 : ℝ)*fordBandScale x i) ≤ Real.log (remainderPrime η i : ℝ) := by
    simpa only [B,Real.exp_log (Real.log_pos hprime1)] using Real.exp_le_exp.mpr hbl
  have hpbig : 100*Real.log 2 ≤ Real.log (remainderPrime η i : ℝ) := by
    have he := Real.add_one_le_exp ((22/25 : ℝ)*fordBandScale x i)
    nlinarith [Real.log_two_lt_d9]
  have htp := suffixPreimage_pos hη (i := i)
  have htn := Nat.totient_pos.mpr htp
  have hlogn : Real.log ((suffixPreimage η i).totient : ℝ) ≤
      (1/100 : ℝ)*Real.log (remainderPrime η i : ℝ) := by
    have hbound : Real.log ((suffixPreimage η i).totient : ℝ) ≤
        Real.log (suffixPreimage η i : ℝ) := Real.log_le_log (by exact_mod_cast htn)
          (by exact_mod_cast Nat.totient_le (suffixPreimage η i))
    have hh := ht i hi hiR hiL hL η hη
    have hl := Real.log_pos hprime1
    linarith
  obtain ⟨hy,hlog,hpow⟩ := dyadic_shift_log_bound hprime htn hlogn hpbig hlo hhi
  have hp3 : 3 ≤ remainderPrime η i := by
    by_contra! hn
    have he : remainderPrime η i=2 := by have := hprime.two_le; omega
    rw [he] at hpbig
    norm_num only [Nat.cast_ofNat] at hpbig
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hpminus : (1 : ℝ) < (remainderPrime η i-1 : ℕ) := by exact_mod_cast (show 2 ≤ remainderPrime η i-1 by omega)
  have hshift : ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y := by
    have hh : remainderPrime η i-1 ≤ (remainderPrime η i-1)*(suffixPreimage η i).totient := by
      exact Nat.le_mul_of_pos_right _ htn
    have hhR : ((remainderPrime η i-1 : ℕ) : ℝ) ≤
        ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) := by exact_mod_cast hh
    exact hhR.trans hhi
  have hBy : B (remainderPrime η i-1 : ℕ) ≤ B y :=
    Real.log_le_log (Real.log_pos hpminus) (Real.log_le_log (zero_lt_one.trans hpminus) hshift)
  have hlower := shifted_doubleLog_lower hp3
  have hupper := Real.log_le_log (Real.log_pos (hpminus.trans_le hshift)) hlog
  rw [Real.log_mul (by norm_num : (51/50 : ℝ) ≠ 0) (Real.log_pos hprime1).ne'] at hupper
  have hlogc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51/50)
  refine ⟨hpow,?_,?_⟩
  · linarith
  · change Real.log (Real.log y) ≤ _
    change Real.log (Real.log (remainderPrime η i : ℝ))-1 ≤ _ at hlower
    change _ ≤ Real.log (Real.log (remainderPrime η i : ℝ)) at hbl
    change Real.log (Real.log (remainderPrime η i : ℝ)) ≤ _ at hbu
    linarith

end TotientAsymptotic

end

end OAI
