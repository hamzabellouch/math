import OAI.MeasureTheory.Falconer.Graphs.GraphTestScales

namespace OAI

/-! # The actual graph degree, with its profile cost and dimensional loss -/

namespace Falconer

theorem height_mono_start (A : ℕ → ℝ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) :
    PlanarFalconer.height A g p ≤ PlanarFalconer.height A a p := by
  obtain ⟨j,hgj,hjp,hj⟩ := PlanarFalconer.intervalMin_attained A hgp
  have hmin := PlanarFalconer.intervalMin_le A (hag.trans hgj) hjp
  unfold PlanarFalconer.height
  rw [hj]
  linarith

theorem profile_graph_degree (d : ℕ) (A : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {σ : ℝ} (hσ : 0 ≤ σ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (hgap : (g:ℝ)-(a:ℝ) ≤ 2*σ*N) :
    (((2*⌈4*((2:ℝ)^N)^(30*σ)⌉₊+1)^d *
      (⌈((2:ℝ)^N)^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ)⌉₊ *
        2^(d*(g-a))) : ℕ) : ℝ) ≤
      2*11^d*((2:ℝ)^N)^(PlanarFalconer.height A a p+
        (1000*((d:ℝ)+1)+32*d)*σ) := by
  let R := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hX : 1 ≤ R^(30*σ) := Real.one_le_rpow hR (by positivity)
  have hL : ((2*⌈4*R^(30*σ)⌉₊+1:ℕ):ℝ) ≤ 11*R^(30*σ) := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*R^(30*σ))).le
    push_cast
    linarith
  have hH := height_mono_start A hag hgp
  have hT : 1 ≤ R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ) :=
    Real.one_le_rpow hR (add_nonneg (PlanarFalconer.height_nonneg A hgp) (by positivity))
  have hC : (⌈R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ)⌉₊:ℝ) ≤
      2*R^(PlanarFalconer.height A a p+1000*((d:ℝ)+1)*σ) := by
    calc
      _ ≤ 2*R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ) := by
        have hh := (Nat.ceil_lt_add_one
          (by positivity : 0 ≤ R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ))).le
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (by norm_num)
  have hg : ((2^(d*(g-a)):ℕ):ℝ) ≤ R^(2*(d:ℝ)*σ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat]
    have he : ((d*(g-a):ℕ):ℝ) = (d:ℝ)*((g:ℝ)-a) := by
      rw [Nat.cast_mul,Nat.cast_sub hag]
    rw [← Real.rpow_natCast,he,← dyadic_rpow_change_base hN]
    apply Real.rpow_le_rpow_of_exponent_le hR
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) d)
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_mul]
  apply (mul_le_mul
    (pow_le_pow_left₀ (by positivity) hL d)
    (mul_le_mul hC hg (Nat.cast_nonneg _) (by positivity))
    (by positivity) (by positivity)).trans_eq
  rw [mul_pow]
  have hp : (R^(30*σ))^d = R^(30*(d:ℝ)*σ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hRpos.le]
    congr 1
    ring
  rw [hp]
  calc
    _ = 2*11^d*(R^(30*(d:ℝ)*σ)*
        R^(PlanarFalconer.height A a p+1000*((d:ℝ)+1)*σ)*R^(2*(d:ℝ)*σ)) := by ring
    _ = _ := by rw [← Real.rpow_add hRpos,← Real.rpow_add hRpos]; congr 2; ring

theorem profile_graph_degree_two (d : ℕ) (A₁ A₂ : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {σ : ℝ} (hσ : 0 ≤ σ) {a g₁ g₂ p : ℕ}
    (hag₁ : a ≤ g₁) (hgp₁ : g₁ ≤ p) (hgap₁ : (g₁:ℝ)-(a:ℝ) ≤ 2*σ*N)
    (hag₂ : a ≤ g₂) (hgp₂ : g₂ ≤ p) (hgap₂ : (g₂:ℝ)-(a:ℝ) ≤ 2*σ*N) :
    (((2*⌈4*((2:ℝ)^N)^(30*σ)⌉₊+1)^d * min
      (⌈((2:ℝ)^N)^(PlanarFalconer.height A₁ g₁ p+1000*((d:ℝ)+1)*σ)⌉₊ *
        2^(d*(g₁-a)))
      (⌈((2:ℝ)^N)^(PlanarFalconer.height A₂ g₂ p+1000*((d:ℝ)+1)*σ)⌉₊ *
        2^(d*(g₂-a))) : ℕ) : ℝ) ≤
      2*11^d*((2:ℝ)^N)^(min (PlanarFalconer.height A₁ a p)
        (PlanarFalconer.height A₂ a p)+(1000*((d:ℝ)+1)+32*d)*σ) := by
  by_cases h : PlanarFalconer.height A₁ a p ≤ PlanarFalconer.height A₂ a p
  · rw [min_eq_left h]
    exact (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (min_le_left _ _))).trans
      (profile_graph_degree d A₁ hN hσ hag₁ hgp₁ hgap₁)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (min_le_right _ _))).trans
      (profile_graph_degree d A₂ hN hσ hag₂ hgp₂ hgap₂)

end Falconer

end OAI
