import OAI.Geometry.NodalSets.Elliptic.SmoothDefectBounds

namespace OAI

namespace Yau.Jets
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Yau.Waves

theorem scaled_taylor_lower_derivative_bound {f : Coord → ℂ} {m K l k k0 : ℕ}
    (hf : ContDiff ℝ ∞ f) (hm : 3 * K + 4 * k0 + 6 < m + 1) (hk : k ≤ k0) (hl : l ≤ k)
    (y z : Coord) {C R N : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hN : 1 ≤ N)
    (hzero : ∀ j, j ≤ m → iteratedFDeriv ℝ j f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (m + 1) f (y + t • z)‖ ≤ C)
    (hradius : ‖z‖ ≤ R * N ^ (-1 / 3 : ℝ)) :
    N ^ ((k : ℝ) + 2) * ‖iteratedFDeriv ℝ l f (y + z)‖ ≤
      C * R ^ (m + 1 - l) * N ^ (-(K : ℝ)) := by
  have hkm : l ≤ m := by omega
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let q : ℕ := m + 1 - l
  have ht := vanishing_jet_derivative_bound hf hkm y z C hzero hbound
  have hfact : (1 : ℝ) ≤ ((m - l).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m - l))
  have hsmall : ‖iteratedFDeriv ℝ l f (y + z)‖ ≤ C * (R * N ^ (-1 / 3 : ℝ)) ^ q := by
    calc
      _ ≤ C * ‖z‖ ^ q := ht.trans (div_le_self (mul_nonneg hC (pow_nonneg (norm_nonneg _) _)) hfact)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hradius q) hC
  have hp : (N ^ (-1 / 3 : ℝ)) ^ q = N ^ (-(q : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have he : (k : ℝ) + 2 + (-(q : ℝ) / 3) ≤ -(K : ℝ) := by
    have hq : (q : ℝ) = (m : ℝ) + 1 - l := by
      dsimp [q]
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [hq]
    have hm' : (3 : ℝ) * K + 4 * k0 + 6 < m + 1 := by exact_mod_cast hm
    have hk' : (k : ℝ) ≤ k0 := by exact_mod_cast hk
    have hl' : (l : ℝ) ≤ k := by exact_mod_cast hl
    linarith
  calc
    _ ≤ N ^ ((k : ℝ) + 2) * (C * (R * N ^ (-1 / 3 : ℝ)) ^ q) :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hpos.le _)
    _ = C * R ^ q * N ^ ((k : ℝ) + 2 + (-(q : ℝ) / 3)) := by
      rw [mul_pow, hp, Real.rpow_add hpos ((k : ℝ) + 2) (-(q : ℝ) / 3)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN he)
      (mul_nonneg hC (pow_nonneg hR _))

theorem uniform_flat_scaled_derivative_bound {T : Type*} [TopologicalSpace T]
    {s : Set T} {R : ℝ} {f : T → Coord → ℂ} (hf : UniformSmoothBounded s R f)
    {m K k0 : ℕ} (hm : 3*K + 4*k0 + 6 < m+1) (hR : 0 ≤ R)
    (hz : ∀ t ∈ s, FlatAt m (f t) 0) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) →
      ∀ l, l ≤ k0 → N ^ ((k0 : ℝ)+2) * ‖iteratedFDeriv ℝ l (f t) x‖ ≤
        C * N ^ (-(K : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := hf.2 (m+1)
  let C := 1 + ∑ l ∈ Finset.range (k0+1), B * R ^ (m+1-l)
  have hterm (l : ℕ) : 0 ≤ B * R ^ (m+1-l) := by positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx l hl
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ (-1/3 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hxR : ‖x‖ ≤ R := hx.trans ((mul_le_mul_of_nonneg_left hpow hR).trans_eq (mul_one R))
  have hsegment : ∀ a ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ (m+1) (f t) (0 + a • x)‖ ≤ B := by
    intro a ha
    apply hb t ht _ _ (m+1) le_rfl
    simp only [zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
    exact (mul_le_mul_of_nonneg_right ha.2 (norm_nonneg x)).trans (by simpa using hxR)
  have h := scaled_taylor_lower_derivative_bound (hf.1 t) hm (le_refl k0) hl
    (0 : Coord) x hB.le hR hN (hz t ht) hsegment hx
  simp only [zero_add] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNp.le _)
  have htC := Finset.single_le_sum (fun i _ ↦ hterm i) (Finset.mem_range.mpr (by omega : l < k0+1))
  dsimp [C]
  linarith

theorem uniform_flat_derivative_decay {T : Type*} [TopologicalSpace T]
    {s : Set T} {R : ℝ} {f : T → Coord → ℂ} (hf : UniformSmoothBounded s R f)
    {m K k0 : ℕ} (hm : 3*K + 4*k0 + 6 < m+1) (hR : 0 ≤ R)
    (hz : ∀ t ∈ s, FlatAt m (f t) 0) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) →
      DerivativeBound k0 (f t) x (C * N ^ (-(K : ℝ) - k0 - 2)) := by
  obtain ⟨C, hC, hc⟩ := uniform_flat_scaled_derivative_bound hf hm hR hz
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx l hl
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ (C * N ^ (-(K : ℝ))) / N ^ ((k0 : ℝ)+2) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
      simpa [mul_comm] using hc t ht N hN x hx l hl
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub hNp]
      congr 2
      ring

end
end Yau.Jets

end OAI
