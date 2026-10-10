import Mathlib

namespace OAI

/-! Discrete Interpolation. -/

noncomputable section
open Set Filter Topology
namespace TameInterpolation

lemma discrete_maximum (m : ℕ) (z : ℕ → ℝ) (h0 : z 0 ≤ 0) (hm : z m ≤ 0)
    (hr : ∀ j, j+2 ≤ m → 2*z (j+1) ≤ z j+z (j+2)) :
    ∀ j, j ≤ m → z j ≤ 0 := by
  let S := Finset.range (m+1)
  have hS : S.Nonempty := ⟨0,by simp [S]⟩
  let M := S.sup' hS z
  have hupper (j : ℕ) (hj : j ≤ m) : z j ≤ M :=
    Finset.le_sup' z (by simpa [S] using Nat.lt_succ_of_le hj)
  have hm0 : M ≤ 0 := by
    by_contra! hM
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' hS z
    have hex : ∃ i, i ≤ m ∧ z i = M := ⟨i,by simpa [S] using hi,he.symm⟩
    let q := Nat.find hex
    have hq := Nat.find_spec hex
    change q ≤ m ∧ z q = M at hq
    have hq0 : 0 < q := by
      by_contra! hn
      have hzero : q = 0 := by omega
      rw [hzero] at hq
      linarith only [h0,hq.2,hM]
    have hqm : q < m := by
      by_contra! hn
      have heq : q = m := by omega
      rw [heq] at hq
      linarith only [hm,hq.2,hM]
    have hrec := hr (q-1) (by omega)
    have hleft := hupper (q-1) (by omega)
    have hright := hupper (q+1) (by omega)
    have he1 : q-1+1 = q := by omega
    have he2 : q-1+2 = q+1 := by omega
    rw [he1,he2,hq.2] at hrec
    have hprev : z (q-1) = M := by linarith only [hrec,hleft,hright]
    have hmin := Nat.find_min' hex (show q-1 ≤ m ∧ z (q-1) = M from ⟨by omega,hprev⟩)
    change q ≤ q-1 at hmin
    omega
  exact fun j hj => (hupper j hj).trans hm0

lemma positive_sequence_product (m j : ℕ) (hm : 0 < m) (hj : j ≤ m)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (C : ℝ) (hC : 0 < C)
    (hr : ∀ i, i+2 ≤ m → (a (i+1))^2 ≤ C*a i*a (i+2)) :
    a j*a (m-j) ≤ C^(j*(m-j))*a 0*a m := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  let z : ℕ → ℝ := fun i => Real.log (a i) - ((i:ℝ)/(m:ℝ))*Real.log (a m) -
    (1-(i:ℝ)/(m:ℝ))*Real.log (a 0) - ((i:ℝ)*((m:ℝ)-(i:ℝ))/2)*Real.log C
  have hz0 : z 0 ≤ 0 := by simp [z]
  have hzm : z m ≤ 0 := by simp [z,hm']
  have hzr (i : ℕ) (hi : i+2 ≤ m) : 2*z (i+1) ≤ z i+z (i+2) := by
    have hlog := Real.log_le_log (sq_pos_of_pos (ha (i+1))) (hr i hi)
    rw [Real.log_pow,Real.log_mul (mul_ne_zero hC.ne' (ha i).ne') (ha (i+2)).ne',
      Real.log_mul hC.ne' (ha i).ne'] at hlog
    have he : z i+z (i+2)-2*z (i+1) =
        Real.log (a i)+Real.log (a (i+2))-2*Real.log (a (i+1))+Real.log C := by
      dsimp [z]
      push_cast
      ring
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog,he]
  have h1 := discrete_maximum m z hz0 hzm hzr j hj
  have h2 := discrete_maximum m z hz0 hzm hzr (m-j) (by omega)
  have he : z j+z (m-j) = Real.log (a j)+Real.log (a (m-j))-
      Real.log (a 0)-Real.log (a m)-((j*(m-j):ℕ):ℝ)*Real.log C := by
    dsimp [z]
    rw [Nat.cast_sub hj,Nat.cast_mul,Nat.cast_sub hj]
    field_simp
    ring
  have hlog : Real.log (a j*a (m-j)) ≤ Real.log (C^(j*(m-j))*a 0*a m) := by
    rw [Real.log_mul (ha j).ne' (ha (m-j)).ne',
      Real.log_mul (mul_ne_zero (pow_ne_zero _ hC.ne') (ha 0).ne') (ha m).ne',
      Real.log_mul (pow_ne_zero _ hC.ne') (ha 0).ne',Real.log_pow]
    linarith only [h1,h2,he]
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (mul_pos (ha j) (ha (m-j))),
    Real.exp_log (mul_pos (mul_pos (pow_pos hC _) (ha 0)) (ha m))] at hh
  exact hh

lemma clamp_recurrence (m : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (C : ℝ) (hC : 1 ≤ C)
    (hr : ∀ i, i+2 ≤ m → (a (i+1))^2 ≤ C*a i*a (i+2))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ i, i+2 ≤ m → (max (a (i+1)) ε)^2 ≤ C*max (a i) ε*max (a (i+2)) ε := by
  intro i hi
  by_cases hmid : a (i+1) ≤ ε
  · rw [max_eq_right hmid]
    have hprod : ε*ε ≤ max (a i) ε*max (a (i+2)) ε :=
      mul_le_mul (le_max_right _ _) (le_max_right _ _) hε.le (hε.le.trans (le_max_right _ _))
    nlinarith [mul_nonneg hε.le hε.le]
  · rw [max_eq_left (le_of_not_ge hmid)]
    exact (hr i hi).trans (by gcongr <;> first | exact le_max_left _ _ | exact ha _)

theorem nonnegative_sequence_product (m j : ℕ) (hm : 0 < m) (hj : j ≤ m)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (C : ℝ) (hC : 1 ≤ C)
    (hr : ∀ i, i+2 ≤ m → (a (i+1))^2 ≤ C*a i*a (i+2)) :
    a j*a (m-j) ≤ C^(j*(m-j))*a 0*a m := by
  have hbound (ε : ℝ) (hε : 0 < ε) :
      a j*a (m-j) ≤ C^(j*(m-j))*max (a 0) ε*max (a m) ε := by
    apply (mul_le_mul (le_max_left _ _) (le_max_left _ _) (ha _) (le_trans (ha _) (le_max_left _ _))).trans
    exact positive_sequence_product m j hm hj (fun i => max (a i) ε)
      (fun i => hε.trans_le (le_max_right _ _)) C (by linarith only [hC])
      (clamp_recurrence m a ha C hC hr ε hε)
  have hcont : Continuous (fun ε : ℝ => C^(j*(m-j))*max (a 0) ε*max (a m) ε) :=
    (continuous_const.mul (continuous_const.max continuous_id)).mul (continuous_const.max continuous_id)
  have hlim : Tendsto (fun ε : ℝ => C^(j*(m-j))*max (a 0) ε*max (a m) ε)
      (𝓝[>] 0) (𝓝 (C^(j*(m-j))*a 0*a m)) := by
    simpa only [max_eq_left (ha 0),max_eq_left (ha m)] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε
end TameInterpolation

end

end OAI
