import Mathlib

namespace OAI

open Filter Set Uniformity
open scoped Topology ENNReal

namespace Problem340

lemma log_nat_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

lemma expGrowthSup_nat_pow (d : ℕ) :
    ExpGrowth.expGrowthSup (fun n : ℕ => (n : ℝ≥0∞) ^ d) = 0 := by
  have h : Tendsto (fun n : ℕ => (d : ℝ) * (Real.log (n : ℝ) / n))
      atTop (𝓝 0) := by
    simpa using log_nat_div_tendsto_zero.const_mul (d : ℝ)
  have h' := EReal.tendsto_coe.mpr h
  have heq : (fun n : ℕ => ENNReal.log ((n : ℝ≥0∞) ^ d) / (n : EReal))
      =ᶠ[atTop] (fun n : ℕ => (((d : ℝ) * (Real.log (n : ℝ) / n) : ℝ) : EReal)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ENNReal.log_pow]
    have hlog : ENNReal.log (n : ℝ≥0∞) = (Real.log (n : ℝ) : EReal) := by
      rw [← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos hnR]
    rw [hlog]
    change (((d : ℝ) * Real.log (n : ℝ) / n : ℝ) : EReal) = _
    congr 1
    ring
  exact (h'.congr' heq.symm).limsup_eq

lemma expGrowthSup_le_zero_of_polynomial_bound {u : ℕ → ℝ≥0∞} (C d : ℕ)
    (h : ∀ᶠ n in atTop, u n ≤ (C : ℝ≥0∞) * (n + 1) ^ d) :
    ExpGrowth.expGrowthSup u ≤ 0 := by
  have hbound : ∀ᶠ n in atTop,
      u n ≤ ((C : ℝ≥0∞) * 2 ^ d) * (n : ℝ≥0∞) ^ d := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    apply hn.trans
    calc
      (C : ℝ≥0∞) * (n + 1) ^ d ≤ (C : ℝ≥0∞) * (2 * (n : ℝ≥0∞)) ^ d := by
        gcongr
        exact_mod_cast (show n + 1 ≤ 2 * n by omega)
      _ = ((C : ℝ≥0∞) * 2 ^ d) * (n : ℝ≥0∞) ^ d := by rw [mul_pow, mul_assoc]
  exact (ExpGrowth.expGrowthSup_le_of_eventually_le (by finiteness) hbound).trans_eq
    (expGrowthSup_nat_pow d)

lemma coverEntropy_eq_zero_of_polynomial_cover_bound {X : Type*} [UniformSpace X]
    (T : X → X) {F : Set X} (hF : F.Nonempty)
    (h : ∀ U ∈ 𝓤 X, ∃ C d : ℕ, ∀ n : ℕ,
      Dynamics.coverMincard T F U n ≤ (C * (n + 1) ^ d : ℕ)) :
    Dynamics.coverEntropy T F = 0 := by
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T hF)
  apply iSup₂_le
  intro U hU
  obtain ⟨C, d, hbound⟩ := h U hU
  apply expGrowthSup_le_zero_of_polynomial_bound C d
  exact Filter.Eventually.of_forall fun n => by
    simpa using ENat.toENNReal_mono (hbound n)

lemma coverEntropy_eq_zero_of_polynomial_net_bound {X : Type*} [UniformSpace X]
    (T : X → X) {F : Set X} (hF : F.Nonempty)
    (h : ∀ U ∈ 𝓤 X, ∃ C d : ℕ, ∀ n : ℕ,
      Dynamics.netMaxcard T F U n ≤ (C * (n + 1) ^ d : ℕ)) :
    Dynamics.coverEntropy T F = 0 := by
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T hF)
  rw [Dynamics.coverEntropy_eq_iSup_netEntropyEntourage]
  apply iSup₂_le
  intro U hU
  obtain ⟨C, d, hbound⟩ := h U hU
  apply expGrowthSup_le_zero_of_polynomial_bound C d
  exact Filter.Eventually.of_forall fun n => by
    simpa using ENat.toENNReal_mono (hbound n)

lemma netMaxcard_le_card_of_orbit_code {X ι : Type*} [Fintype ι]
    (T : X → X) (F : Set X) (U : SetRel X X) [U.IsRefl] (n : ℕ)
    (code : X → ι)
    (hcode : ∀ x ∈ F, ∀ y ∈ F, code x = code y →
      (x, y) ∈ Dynamics.dynEntourage T U n) :
    Dynamics.netMaxcard T F U n ≤ (Fintype.card ι : ℕ) := by
  classical
  apply iSup₂_le
  intro s hs
  have hinj : Set.InjOn code (s : Set X) := by
    intro x hx y hy hxy
    exact Set.PairwiseDisjoint.elim_set hs.2 hx hy y
      (hcode x (hs.1 hx) y (hs.1 hy) hxy)
      (SetRel.rfl (Dynamics.dynEntourage T U n))
  have hcard : s.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_card_of_injOn code (fun x _ => Finset.mem_univ (code x)) hinj
  exact_mod_cast hcard

lemma coverEntropy_eq_zero_of_eventually_polynomial_net_bound {X : Type*} [UniformSpace X]
    (T : X → X) {F : Set X} (hF : F.Nonempty)
    (h : ∀ U ∈ 𝓤 X, ∃ C d : ℕ, ∀ᶠ n in atTop,
      Dynamics.netMaxcard T F U n ≤ (C * (n + 1) ^ d : ℕ)) :
    Dynamics.coverEntropy T F = 0 := by
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T hF)
  rw [Dynamics.coverEntropy_eq_iSup_netEntropyEntourage]
  apply iSup₂_le
  intro U hU
  obtain ⟨C, d, hbound⟩ := h U hU
  apply expGrowthSup_le_zero_of_polynomial_bound C d
  filter_upwards [hbound] with n hn
  simpa using ENat.toENNReal_mono hn

lemma coverEntropy_eq_zero_of_polynomial_orbit_codes {X : Type*} [PseudoMetricSpace X]
    (T : X → X) {F : Set X} (hF : F.Nonempty)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C d : ℕ, ∀ᶠ n in atTop,
      ∃ code : X → Fin (C * (n + 1) ^ d),
        ∀ x ∈ F, ∀ y ∈ F, code x = code y →
          ∀ j < n, dist (T^[j] x) (T^[j] y) < ε) :
    Dynamics.coverEntropy T F = 0 := by
  apply coverEntropy_eq_zero_of_eventually_polynomial_net_bound T hF
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨C, d, hcode⟩ := h ε hε
  refine ⟨C, d, ?_⟩
  filter_upwards [hcode] with n hn
  obtain ⟨code, hshadow⟩ := hn
  have : SetRel.IsRefl U := isRefl_of_mem_uniformity hU
  simpa using netMaxcard_le_card_of_orbit_code T F U n code (by
    intro x hx y hy hxy
    apply Dynamics.mem_dynEntourage.mpr
    intro j hj
    exact hεU (hshadow x hx y hy hxy j hj))

end Problem340

end OAI
