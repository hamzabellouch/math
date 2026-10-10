import OAI.Probability.RadialTransition.CanonicalLimit

namespace OAI

universe uG

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

lemma sum_fin_two {G : Type uG} [AddCommMonoid G] (k r : ℕ) (hr : r ≤ k) (u v : G) :
    (∑ i : Fin k, if (i : ℕ) < r then u else v) = r • u + (k - r) • v := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, Fin.card_filter_val_lt, min_eq_right hr]
  congr 1
  have he : (Finset.univ.filter (fun i : Fin k => ¬(i : ℕ) < r)).card = k - r := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp only [Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt, min_eq_right hr]
  rw [he]

theorem boxCost_limit_convex {H : ℝ → ℕ → ℝ} {A : ℝ → ℝ}
    (hrep : HasBoxReplication H)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun z : ℝ × ℕ => H z.1 z.2)
      (thermodynamicFilter d) (nhds (A d))) : ConvexOn ℝ (Ici 0) A := by
  refine ⟨convex_Ici _, ?_⟩
  intro d₁ hd₁ d₂ hd₂ a b ha hb hab
  simp only [smul_eq_mul]
  have ha1 : a ≤ 1 := by linarith
  let B (j : ℕ) : ℕ := j + 1
  let s (j : ℕ) : ℝ := B j
  let k (j : ℕ) : ℕ := B j ^ 3
  let r (j : ℕ) : ℕ := ⌊a * (k j : ℝ)⌋₊
  let m₁ (j : ℕ) : ℕ := ⌊d₁ * s j ^ 3⌋₊
  let m₂ (j : ℕ) : ℕ := ⌊d₂ * s j ^ 3⌋₊
  let N (j : ℕ) : ℕ := r j * m₁ j + (k j - r j) * m₂ j
  let L (j : ℕ) : ℝ := (B j : ℝ) * (s j + 2)
  have hspos (j : ℕ) : 0 < s j := by dsimp [s, B]; positivity
  have hkpos (j : ℕ) : 0 < (k j : ℝ) := by dsimp [k, B]; positivity
  have hkr (j : ℕ) : r j ≤ k j := by
    apply Nat.floor_le_of_le
    exact mul_le_of_le_one_left (by positivity) ha1
  have hs : Tendsto s atTop atTop := by
    have hh := tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
    simpa only [s, B, Nat.cast_add, Nat.cast_one] using hh
  have hk : Tendsto (fun j => (k j : ℝ)) atTop atTop := by
    simpa only [k, s, Nat.cast_pow, Function.comp_def] using (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hs
  have hr : Tendsto (fun j => (r j : ℝ) / k j) atTop (nhds a) :=
    (tendsto_nat_floor_mul_div_atTop ha).comp hk
  have hrem : Tendsto (fun j => ((k j - r j : ℕ) : ℝ) / k j) atTop (nhds b) := by
    have hh := hr.const_sub 1
    rw [show 1 - a = b by linarith] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun j => by dsimp only; rw [Nat.cast_sub (hkr j)]; field_simp [(hkpos j).ne'])
  have hm₁ : Tendsto (fun j => (m₁ j : ℝ) / s j ^ 3) atTop (nhds d₁) :=
    (floor_density_tendsto hd₁).comp hs
  have hm₂ : Tendsto (fun j => (m₂ j : ℝ) / s j ^ 3) atTop (nhds d₂) :=
    (floor_density_tendsto hd₂).comp hs
  have hratio : Tendsto (fun j => (s j / (s j + 2)) ^ 3) atTop (nhds 1) := by
    simpa only [one_pow, Function.comp_def] using (tendsto_side_ratio.comp hs).pow 3
  have hL : Tendsto L atTop atTop := hs.atTop_mul_atTop₀
    (tendsto_atTop_add_const_right atTop (2 : ℝ) hs)
  have hden : Tendsto (fun j => (N j : ℝ) / L j ^ 3) atTop (nhds (a * d₁ + b * d₂)) := by
    have hh := hratio.mul ((hr.mul hm₁).add (hrem.mul hm₂))
    simp only [one_mul] at hh
    apply hh.congr'
    refine Eventually.of_forall (fun j => ?_)
    have hs0 := (hspos j).ne'
    have hk0 := (hkpos j).ne'
    have hsum0 : s j + 2 ≠ 0 := by linarith [hspos j]
    dsimp only [N, L, Function.comp_def]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    have hkEq : (B j : ℝ) ^ 3 = k j := by simp [k]
    rw [mul_pow, hkEq]
    have hsk : s j ^ 3 = (k j : ℝ) := hkEq
    field_simp
    rw [hsk]
  have hnl : Tendsto (fun j => (L j, N j)) atTop (thermodynamicFilter (a * d₁ + b * d₂)) := by
    apply tendsto_inf.mpr
    exact ⟨tendsto_comap_iff.mpr hL, tendsto_comap_iff.mpr hden⟩
  have hH : Tendsto (fun j => H (L j) (N j)) atTop (nhds (A (a * d₁ + b * d₂))) :=
    (hlim _ (add_nonneg (mul_nonneg ha hd₁) (mul_nonneg hb hd₂))).comp hnl
  have hH₁ : Tendsto (fun j => H (s j) (m₁ j)) atTop (nhds (A d₁)) :=
    (hlim d₁ hd₁).comp ((floor_tendsto_thermodynamicFilter hd₁).comp hs)
  have hH₂ : Tendsto (fun j => H (s j) (m₂ j)) atTop (nhds (A d₂)) :=
    (hlim d₂ hd₂).comp ((floor_tendsto_thermodynamicFilter hd₂).comp hs)
  have hupper : Tendsto (fun j => (s j / (s j + 2)) ^ 3 *
      ((r j : ℝ) / k j * H (s j) (m₁ j) + ((k j - r j : ℕ) : ℝ) / k j * H (s j) (m₂ j)))
      atTop (nhds (a * A d₁ + b * A d₂)) := by
    simpa only [one_mul] using hratio.mul ((hr.mul hH₁).add (hrem.mul hH₂))
  apply le_of_tendsto_of_tendsto hH hupper
  refine Eventually.of_forall (fun j => ?_)
  let f : Fin (k j) → ℕ := fun i => if (i : ℕ) < r j then m₁ j else m₂ j
  have hsum : (∑ i, f i) = N j := by
    simpa only [f, N, nsmul_eq_mul, smul_eq_mul] using sum_fin_two (k j) (r j) (hkr j) (m₁ j) (m₂ j)
  have hcost : (∑ i, H (s j) (f i)) = (r j : ℝ) * H (s j) (m₁ j) +
      ((k j - r j : ℕ) : ℝ) * H (s j) (m₂ j) := by
    dsimp only [f]
    simp only [apply_ite]
    simpa only [nsmul_eq_mul] using sum_fin_two (k j) (r j) (hkr j)
      (H (s j) (m₁ j)) (H (s j) (m₂ j))
  have hh := hrep (s j) (L j) (B j) (hspos j)
    (by dsimp [L]; positivity) le_rfl f
  rw [hsum, hcost] at hh
  apply hh.trans_eq
  have hs0 := (hspos j).ne'
  have hk0 := (hkpos j).ne'
  have hsum0 : s j + 2 ≠ 0 := by linarith [hspos j]
  dsimp only [L]
  have hkEq : (B j : ℝ) ^ 3 = k j := by simp [k]
  rw [mul_pow, hkEq]
  have hsk : s j ^ 3 = (k j : ℝ) := hkEq
  field_simp
  rw [hsk]

def finiteGrandPressure (φ : Potential) (t L β h : ℝ) : ℝ :=
  Real.log (grandPartition φ t L β h) / (t * L ^ 3)

def grandPressure (φ : Potential) (t : ℝ) : Pressure :=
  fun β h => limsup (fun L : ℝ => finiteGrandPressure φ t L β h) atTop

theorem grandPressure_spec {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (h : ℝ) :
    Tendsto (fun L : ℝ => finiteGrandPressure φ t L β h) atTop (nhds (grandPressure φ t β h)) ∧
      0 ≤ grandPressure φ t β h ∧ grandPressure φ t β h ≤ Real.exp (β * B + t * h) / t := by
  obtain ⟨p, hp0, hpB, hlim⟩ := grandPressure_exists hφ hb hstable ht hβ hc h
  have he : grandPressure φ t β h = p := hlim.limsup_eq
  rw [he]
  exact ⟨hlim, hp0, hpB⟩

theorem finiteGrandPressure_convex_mix {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β γ a b : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 0 < L)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (h j : ℝ) (ha : 0 ≤ a) (hbb : 0 ≤ b) (hab : a + b = 1) :
    finiteGrandPressure φ t L (a * β + b * γ) (a * h + b * j) ≤
      a * finiteGrandPressure φ t L β h + b * finiteGrandPressure φ t L γ j := by
  have hmix : 0 ≤ a * β + b * γ := by positivity
  have hh := log_tsum_convex_mix ha hbb hab
    (grandPartition_summable hφ hb hstable hL.le hmix t (a * h + b * j))
    (grandPartition_summable hφ hb hstable hL.le hβ t h)
    (grandPartition_summable hφ hb hstable hL.le hγ t j)
    (fun n => mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n _))
    (fun n => mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n _))
    (fun n => mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n _))
    (fun n => by
      simp only [Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n _).ne', Real.log_exp]
      have hh := log_partition_convex_mix hφ hb hL n β γ ha hbb hab
      nlinarith)
  dsimp only [finiteGrandPressure]
  have hh' := div_le_div_of_nonneg_right hh (show 0 ≤ t * L ^ 3 by positivity)
  simpa only [grandPartition, add_div, mul_div_assoc] using hh'

theorem grandPressure_convex_mix {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β γ a b : ℝ} (hstable : StableWith φ B) (ht : 0 < t)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (h j : ℝ) (ha : 0 ≤ a) (hbb : 0 ≤ b) (hab : a + b = 1) :
    grandPressure φ t (a * β + b * γ) (a * h + b * j) ≤
      a * grandPressure φ t β h + b * grandPressure φ t γ j := by
  have hl := (grandPressure_spec hφ hb hstable ht (β := a * β + b * γ) (by positivity) hc (a * h + b * j)).1
  have hr := ((grandPressure_spec hφ hb hstable ht hβ hc h).1.const_mul a).add
    ((grandPressure_spec hφ hb hstable ht hγ hc j).1.const_mul b)
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact finiteGrandPressure_convex_mix hφ hb hstable ht hL hβ hγ h j ha hbb hab

end RadialTransition

end

end OAI
