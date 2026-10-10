import OAI.Probability.ContinuumTransition.QuadraticLaplace

namespace OAI

universe u_1

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

def twoBoxCounts (K k n₁ n₂ : ℕ) : Fin K → ℕ :=
  fun i => if (i : ℕ) < k then n₁ else n₂

theorem sum_twoBoxCounts {M : Type u_1} [AddCommMonoid M] (f : ℕ → M)
    {K k : ℕ} (hk : k ≤ K) (n₁ n₂ : ℕ) :
    ∑ i, f (twoBoxCounts K k n₁ n₂ i) = k • f n₁ + (K-k) • f n₂ := by
  induction K generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    simp [hk0]
  | succ K ih =>
    cases k with
    | zero => simp [twoBoxCounts]
    | succ k =>
      have hkle : k ≤ K := by omega
      simp only [twoBoxCounts, Fin.sum_univ_succ, Fin.val_zero, Nat.zero_lt_succ,
        ite_true, Fin.val_succ, Nat.succ_lt_succ_iff]
      rw [show (∑ i : Fin K, f (if (i : ℕ) < k then n₁ else n₂)) =
          k • f n₁ + (K-k) • f n₂ from ih hkle]
      simp only [Nat.succ_sub_succ_eq_sub, succ_nsmul]
      abel

theorem tileCount_exact {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : ℕ) :
    tileCount ℓ ((k : ℝ) * (ℓ+2)) = k^3 := by
  have hh : ℓ+2 ≠ 0 := by linarith
  simp [tileCount, mul_div_cancel_right₀ _ hh]

noncomputable def mixCount (θ : ℝ) (n : ℕ) : ℕ := ⌊θ*(n : ℝ)^3⌋₊
def mixSide (n : ℕ) : ℝ := (n : ℝ)*((n : ℝ)+2)
noncomputable def mixTotal (θ d₁ d₂ : ℝ) (n : ℕ) : ℕ :=
  mixCount θ n * mixCount d₁ n + (n^3-mixCount θ n)*mixCount d₂ n

theorem mixCount_le {θ : ℝ} (hθ1 : θ ≤ 1) (n : ℕ) : mixCount θ n ≤ n^3 := by
  have hx : θ*(n : ℝ)^3 ≤ (n : ℝ)^3 :=
    mul_le_of_le_one_left (pow_nonneg (Nat.cast_nonneg n) 3) hθ1
  simpa only [mixCount, ← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_mono hx

theorem tendsto_mixCount {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun n : ℕ => (mixCount θ n : ℝ)/(n : ℝ)^3) atTop (𝓝 θ) :=
  (tendsto_nat_floor_mul_div_atTop hθ).comp
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop)

theorem tendsto_mixSide : Tendsto mixSide atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [] with n
  dsimp [mixSide]
  nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

theorem mixTotal_ratio {θ d₁ d₂ : ℝ} (hθ1 : θ ≤ 1) {n : ℕ} (hn : 0 < n) :
    (mixTotal θ d₁ d₂ n : ℝ)/(mixSide n)^3 =
      ((n : ℝ)+2)⁻¹^3*(n : ℝ)^3 *
        (((mixCount θ n : ℝ)/(n : ℝ)^3)*((mixCount d₁ n : ℝ)/(n : ℝ)^3) +
        (1-(mixCount θ n : ℝ)/(n : ℝ)^3)*((mixCount d₂ n : ℝ)/(n : ℝ)^3)) := by
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  unfold mixTotal mixSide
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (mixCount_le hθ1 n), Nat.cast_pow]
  field_simp

theorem tendsto_mixTotal {θ d₁ d₂ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    Tendsto (fun n : ℕ => (mixTotal θ d₁ d₂ n : ℝ)/(mixSide n)^3)
      atTop (𝓝 (θ*d₁+(1-θ)*d₂)) := by
  have hdil := dilution_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hdil.mul (((tendsto_mixCount hθ).mul (tendsto_mixCount hd₁)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mixCount hθ)).mul (tendsto_mixCount hd₂)))
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (mixTotal_ratio hθ1 hn).symm

theorem mixBox_inequality {a : ℝ → ℕ → ℝ} (hbox : HasBoxInequality a)
    {θ d₁ d₂ : ℝ} (hθ1 : θ ≤ 1) {n : ℕ} (hnpos : 0 < n) :
    a (mixSide n) (mixTotal θ d₁ d₂ n) ≤
      ((n : ℝ)+2)⁻¹^3*(n : ℝ)^3 *
        (((mixCount θ n : ℝ)/(n : ℝ)^3)*a (n : ℝ) (mixCount d₁ n) +
        (1-(mixCount θ n : ℝ)/(n : ℝ)^3)*a (n : ℝ) (mixCount d₂ n)) := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hcount : tileCount (n : ℝ) (mixSide n) = n^3 := tileCount_exact hnp.le n
  have hk : mixCount θ n ≤ n^3 := mixCount_le hθ1 n
  have hk' : mixCount θ n ≤ tileCount (n : ℝ) (mixSide n) := hcount.symm ▸ hk
  have hx := hbox (n : ℝ) (mixSide n) hnp (by dsimp [mixSide]; positivity)
    (twoBoxCounts (tileCount (n : ℝ) (mixSide n)) (mixCount θ n)
      (mixCount d₁ n) (mixCount d₂ n))
  rw [sum_twoBoxCounts (fun m : ℕ => m) hk', sum_twoBoxCounts (a (n : ℝ)) hk'] at hx
  simp only [nsmul_eq_mul, hcount] at hx
  change a (mixSide n) (mixTotal θ d₁ d₂ n) ≤ _ at hx
  refine hx.trans_eq ?_
  unfold mixSide
  rw [Nat.cast_sub hk, Nat.cast_pow]
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem convexOn_of_box_limits {a : ℝ → ℕ → ℝ} {F : ℝ → ℝ}
    (hbox : HasBoxInequality a)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => a p.1 p.2)
      (densityFilter d) (𝓝 (F d))) : ConvexOn ℝ (Ici 0) F := by
  refine ⟨convex_Ici _, ?_⟩
  intro d₁ hd₁ d₂ hd₂ θ η hθ hη hsum
  simp only [smul_eq_mul]
  have hθ1 : θ ≤ 1 := by linarith
  have hηeq : η = 1-θ := by linarith
  subst η
  have hd : 0 ≤ θ*d₁+(1-θ)*d₂ := add_nonneg (mul_nonneg hθ hd₁) (mul_nonneg hη hd₂)
  have hdil := dilution_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hseq : Tendsto (fun n : ℕ => (mixSide n, mixTotal θ d₁ d₂ n))
      atTop (densityFilter (θ*d₁+(1-θ)*d₂)) :=
    tendsto_densityFilter_iff.mpr ⟨tendsto_mixSide, tendsto_mixTotal hθ hθ1 hd₁ hd₂⟩
  have hvN : Tendsto (fun n => a (mixSide n) (mixTotal θ d₁ d₂ n))
      atTop (𝓝 (F (θ*d₁+(1-θ)*d₂))) := (hlim _ hd).comp hseq
  have hva₁ : Tendsto (fun n : ℕ => a (n : ℝ) (mixCount d₁ n)) atTop (𝓝 (F d₁)) :=
    (hlim _ hd₁).comp ((floor_density_tendsto hd₁).comp tendsto_natCast_atTop_atTop)
  have hva₂ : Tendsto (fun n : ℕ => a (n : ℝ) (mixCount d₂ n)) atTop (𝓝 (F d₂)) :=
    (hlim _ hd₂).comp ((floor_density_tendsto hd₂).comp tendsto_natCast_atTop_atTop)
  have hR := hdil.mul (((tendsto_mixCount hθ).mul hva₁).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mixCount hθ)).mul hva₂))
  simp only [one_mul] at hR
  apply le_of_tendsto_of_tendsto hvN hR
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
  exact mixBox_inequality hbox hθ1 hnpos

theorem convexOn_canonicalDensity {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ (Ici 0) (canonicalDensity φ β) := by
  apply convexOn_of_box_limits
    (finiteCanonical_hasBoxInequality hφ hβ hstable (fun r hr =>
      (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)))
  exact fun d hd => finiteCanonical_tendsto hφ ht hβ hstable hcore hd

end ContinuumTemperature
end

end OAI
