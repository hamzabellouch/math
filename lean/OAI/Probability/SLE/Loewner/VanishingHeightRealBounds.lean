import OAI.Probability.SLE.Geometry.OutwardRealBarrier
import OAI.Probability.SLE.Stochastic.ScalarExponentialLower

namespace OAI

/-! Vanishing forward height forces the real coordinate to remain
between the future driver bounds. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

lemma forward_height_lower_of_real_gap {a b ε : ℝ} (hε : 0 < ε)
    (X y u : ℝ → ℝ) (hc : ContinuousOn y (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt y
      (-2*y t/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hy : ∀ t ∈ Icc a b, 0 ≤ y t)
    (hgap : ∀ t ∈ Ico a b, ε ≤ |X t-u t|) :
    ∀ t ∈ Icc a b, y a*Real.exp (-(2/ε^2)*(t-a)) ≤ y t := by
  apply scalar_exponential_lower y _ hc hd
  intro t ht
  have hsq := (sq_le_sq₀ hε.le (abs_nonneg (X t-u t))).mpr (hgap t ht)
  rw [sq_abs] at hsq
  have hden : ε^2 ≤ (X t-u t)^2+(y t)^2 := by nlinarith [sq_nonneg (y t)]
  have hdv := div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hy t (Ico_subset_Icc_self ht)))
    (sq_pos_of_pos hε) hden
  calc
    -(2/ε^2)*y t = -(2*y t/ε^2) := by ring
    _ ≤ -(2*y t/((X t-u t)^2+(y t)^2)) := neg_le_neg hdv
    _ = -2*y t/((X t-u t)^2+(y t)^2) := by ring

theorem real_le_future_driver_bound_of_height_zero {a τ c : ℝ} (haτ : a < τ)
    (X y u : ℝ → ℝ)
    (hX : ContinuousOn X (Ico a τ)) (hyc : ContinuousOn y (Ico a τ))
    (hXd : ∀ t ∈ Ico a τ, HasDerivWithinAt X
      (2*(X t-u t)/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a τ, HasDerivWithinAt y
      (-2*y t/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hyp : ∀ t ∈ Ico a τ, 0 < y t)
    (hu : ∀ t ∈ Ico a τ, u t ≤ c)
    (hlim : Tendsto y (𝓝[<] τ) (𝓝 0)) : X a ≤ c := by
  by_contra hn
  have hca : c < X a := lt_of_not_ge hn
  let ε : ℝ := X a-c
  have hε : 0 < ε := sub_pos.mpr hca
  have hya : 0 < y a := hyp a ⟨le_rfl,haτ⟩
  have hpoint (t : ℝ) (ht : t ∈ Ico a τ) :
      y a*Real.exp (-(2/ε^2)*(τ-a)) ≤ y t := by
    have hsub : Icc a t ⊆ Ico a τ := fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩
    have hsub' : Ico a t ⊆ Ico a τ := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    have hD (s : ℝ) (hs : s ∈ Ico a t) : 0 < (X s-u s)^2+(y s)^2 := by
      have hp := hyp s (hsub' hs)
      positivity
    have hbar := outward_real_barrier X u (fun s => (X s-u s)^2+(y s)^2)
      (hX.mono hsub) (fun s hs => hXd s (hsub' hs)) hD
      (fun s hs => hu s (hsub' hs)) hca
    have hlower := forward_height_lower_of_real_gap hε X y u (hyc.mono hsub)
      (fun s hs => hyd s (hsub' hs)) (fun s hs => (hyp s (hsub hs)).le)
      (fun s hs => ?_) t ⟨ht.1,le_rfl⟩
    · have hC : 0 ≤ 2/ε^2 := by positivity
      have hexp : Real.exp (-(2/ε^2)*(τ-a)) ≤ Real.exp (-(2/ε^2)*(t-a)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left ht.2.le hC]
      exact (mul_le_mul_of_nonneg_left hexp hya.le).trans hlower
    · have hb := hbar s (Ico_subset_Icc_self hs)
      have hu' := hu s (hsub' hs)
      exact (by dsimp [ε]; linarith : ε ≤ X s-u s).trans (le_abs_self _)
  have hzero : y a*Real.exp (-(2/ε^2)*(τ-a)) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds haτ)] with t ht hta
    exact hpoint t ⟨hta.le,ht⟩
  exact not_le_of_gt (mul_pos hya (Real.exp_pos _)) hzero

theorem future_driver_lower_le_real_of_height_zero {a τ c : ℝ} (haτ : a < τ)
    (X y u : ℝ → ℝ)
    (hX : ContinuousOn X (Ico a τ)) (hyc : ContinuousOn y (Ico a τ))
    (hXd : ∀ t ∈ Ico a τ, HasDerivWithinAt X
      (2*(X t-u t)/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a τ, HasDerivWithinAt y
      (-2*y t/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hyp : ∀ t ∈ Ico a τ, 0 < y t)
    (hu : ∀ t ∈ Ico a τ, c ≤ u t)
    (hlim : Tendsto y (𝓝[<] τ) (𝓝 0)) : c ≤ X a := by
  have hXd' (t : ℝ) (ht : t ∈ Ico a τ) : HasDerivWithinAt (fun s => -X s)
      (2*((-X t)-(-u t))/(((-X t)-(-u t))^2+(y t)^2)) (Ici t) t := by
    convert! (hXd t ht).neg using 1
    ring
  have hyd' (t : ℝ) (ht : t ∈ Ico a τ) : HasDerivWithinAt y
      (-2*y t/(((-X t)-(-u t))^2+(y t)^2)) (Ici t) t := by
    convert! hyd t ht using 1
    congr 1
    ring
  have hh := real_le_future_driver_bound_of_height_zero haτ
    (fun t => -X t) y (fun t => -u t) hX.neg hyc hXd' hyd' hyp
    (fun t ht => neg_le_neg (hu t ht)) hlim
  linarith

end SLEExactGauge

end

end OAI
