import OAI.NumberTheory.EgyptianFractions.SmallPrimeDivisors

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- An explicit uniform error coefficient for the pointwise truncated-divisor estimate. -/
def divisorPointwiseError (E S : ℝ) : ℝ :=
  4 * (Real.log S) ^ 2 / Real.sqrt S +
    2 * (1 + Real.log (2 * E) + Real.log (Real.log S)) / Real.log S

theorem divisorPointwiseError_tendsto (E : ℝ) :
    Tendsto (divisorPointwiseError E) atTop (𝓝 0) := by
  have h1 : Tendsto (fun S : ℝ => (Real.log S) ^ 2 / Real.sqrt S) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun S : ℝ => Real.log (Real.log S) / Real.log S) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hc : Tendsto (fun S : ℝ => (1 + Real.log (2 * E)) / Real.log S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := (h1.const_mul 4).add ((hc.add h2).const_mul 2)
  convert h using 1
  · ext S
    simp only [divisorPointwiseError]
    ring
  · norm_num

/-- Explicit estimate uniform over the admissible logarithmic size interval. -/
theorem truncatedDivisorCount_pointwise_error_bound (E S X : ℝ) {n : ℕ}
    (hE : 1 ≤ E) (hS : 1 < S) (hES : 1 + E / Real.log 2 ≤ S)
    (hn : n ≠ 0) (hX : 1 < X)
    (hlo : S / (2 * Real.log S) ≤ Real.log X)
    (hhi : Real.log X ≤ E * S) (hnhi : Real.log (n : ℝ) ≤ E * S) :
    Real.log (truncatedDivisorCount X n : ℝ) ≤ divisorPointwiseError E S * Real.log X := by
  have hS0 : 0 < S := by linarith
  have hE0 : 0 < E := by linarith
  have hls : 0 < Real.log S := Real.log_pos hS
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv : 0 < Real.log X := Real.log_pos hX
  have hroot : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS0
  have hroot1 : 1 < Real.sqrt S := by
    nlinarith [Real.sq_sqrt hS0.le, Real.sqrt_nonneg S]
  have hsize : S ≤ Real.log X * (2 * Real.log S) :=
    (div_le_iff₀ (by positivity)).1 hlo
  have hbasePos : 0 < 1 + E * S / Real.log 2 := by positivity
  have hbase : 1 + E * S / Real.log 2 ≤ S ^ 2 := by
    have hcoef : E / Real.log 2 ≤ S - 1 := by linarith
    have hc := mul_le_mul_of_nonneg_right hcoef hS0.le
    have heq : E * S / Real.log 2 = (E / Real.log 2) * S := by ring
    rw [heq]
    nlinarith
  have hlogbase : Real.log (1 + E * S / Real.log 2) ≤ 2 * Real.log S := by
    have h := Real.log_le_log hbasePos hbase
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hterm1 : Real.sqrt S * Real.log (1 + E * S / Real.log 2) ≤
      (4 * (Real.log S) ^ 2 / Real.sqrt S) * Real.log X := by
    calc
      _ ≤ Real.sqrt S * (2 * Real.log S) :=
        mul_le_mul_of_nonneg_left hlogbase (Real.sqrt_nonneg S)
      _ = (2 * S * Real.log S) / Real.sqrt S := by
        apply (eq_div_iff hroot.ne').2
        nlinarith [Real.sq_sqrt hS0.le]
      _ ≤ (4 * (Real.log S) ^ 2 * Real.log X) / Real.sqrt S := by
        apply div_le_div_of_nonneg_right _ hroot.le
        have h := mul_le_mul_of_nonneg_right hsize (show 0 ≤ 2 * Real.log S by positivity)
        nlinarith
      _ = _ := by ring
  have hratio : E * S / Real.log X ≤ 2 * E * Real.log S := by
    apply (div_le_iff₀ hv).2
    have h := mul_le_mul_of_nonneg_left hsize hE0.le
    nlinarith
  have hB : 1 + Real.log (E * S / Real.log X) ≤
      1 + Real.log (2 * E) + Real.log (Real.log S) := by
    have h := Real.log_le_log (show 0 < E * S / Real.log X by positivity) hratio
    rw [Real.log_mul (by positivity : 2 * E ≠ 0) hls.ne'] at h
    linarith
  have hterm2 : (1 + Real.log (E * S / Real.log X)) * Real.log X /
      Real.log (Real.sqrt S) ≤
      (2 * (1 + Real.log (2 * E) + Real.log (Real.log S)) / Real.log S) * Real.log X := by
    rw [Real.log_sqrt hS0.le]
    calc
      _ ≤ (1 + Real.log (2 * E) + Real.log (Real.log S)) * Real.log X /
          (Real.log S / 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB hv.le) (by positivity)
      _ = _ := by ring
  have hbound := truncatedDivisorCount_pointwise_log_bound X (Real.sqrt S) (E * S)
    hn hX hroot1 hhi hnhi
  dsimp [divisorPointwiseError]
  nlinarith

/-- Uniform subpower growth of truncated divisor moments over the full size interval. -/
theorem truncatedDivisorCount_uniform_subpower (E r ε : ℝ) (hE : 1 ≤ E)
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ∃ S0 : ℝ, ∀ S : ℝ, S0 ≤ S → ∀ X : ℝ, ∀ n : ℕ,
      n ≠ 0 → 1 < X → S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ E * S → Real.log (n : ℝ) ≤ E * S →
      (truncatedDivisorCount X n : ℝ) ^ r ≤ Real.exp (ε * Real.log X) := by
  have herror : ∀ᶠ S : ℝ in atTop, r * divisorPointwiseError E S < ε := by
    apply Filter.Tendsto.eventually_lt_const hε
    simpa using (divisorPointwiseError_tendsto E).const_mul r
  have hevent : ∀ᶠ S : ℝ in atTop, ∀ X : ℝ, ∀ n : ℕ,
      n ≠ 0 → 1 < X → S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ E * S → Real.log (n : ℝ) ≤ E * S →
      (truncatedDivisorCount X n : ℝ) ^ r ≤ Real.exp (ε * Real.log X) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      eventually_ge_atTop (1 + E / Real.log 2), herror] with S hS hES herr
    intro X n hn hX hlo hhi hnhi
    have hcount : 0 < truncatedDivisorCount X n := by
      apply Finset.card_pos.mpr
      exact ⟨1, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩,
        by simpa using hX.le⟩⟩
    rw [Real.rpow_def_of_pos (by exact_mod_cast hcount)]
    apply Real.exp_le_exp.mpr
    have hb := truncatedDivisorCount_pointwise_error_bound E S X hE hS hES hn hX hlo hhi hnhi
    have hbr := mul_le_mul_of_nonneg_right hb hr
    have he := mul_le_mul_of_nonneg_right herr.le (Real.log_pos hX).le
    nlinarith
  exact hevent.exists_forall_of_atTop

/-- The uniform pointwise estimate in the shifted-interval range of the moment lemma. -/
theorem truncatedDivisorCount_shifted_uniform_subpower (D r ε : ℝ) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ∃ S0 : ℝ, ∀ S : ℝ, S0 ≤ S → ∀ X Y : ℝ, ∀ N h : ℕ,
      1 ≤ X → S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ D * S → (N : ℝ) ≤ Real.exp (D * S) →
      1 ≤ h → (h : ℝ) ≤ Y → Y ≤ X →
      (truncatedDivisorCount X (N + h) : ℝ) ^ r ≤ Real.exp (ε * Real.log X) := by
  obtain ⟨S0, hS0⟩ := truncatedDivisorCount_uniform_subpower (D + 1) r ε (by linarith) hr hε
  refine ⟨max S0 (max 2 (Real.log 2)), ?_⟩
  intro S hS X Y N h hX hlo hhi hN hh hhY hYX
  have hSS : S0 ≤ S := (le_max_left _ _).trans hS
  have hS2 : 2 ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans hS)
  have hSlog : Real.log 2 ≤ S := (le_max_right _ _).trans ((le_max_right _ _).trans hS)
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := lt_of_lt_of_le (by positivity) hlo
  have hXlt : 1 < X := by
    by_contra hx
    have hXe : X = 1 := by linarith
    simp [hXe] at hlogX
  have hXS : X ≤ Real.exp (D * S) := by
    have he := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log (by linarith : 0 < X)] using he
  have htwo : (2 : ℝ) ≤ Real.exp S := by
    have he := Real.exp_le_exp.mpr hSlog
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hnpos : 0 < N + h := by omega
  have hnle : ((N + h : ℕ) : ℝ) ≤ Real.exp ((D + 1) * S) := by
    have hhle : (h : ℝ) ≤ Real.exp (D * S) := hhY.trans (hYX.trans hXS)
    calc
      ((N + h : ℕ) : ℝ) ≤ 2 * Real.exp (D * S) := by push_cast; linarith
      _ ≤ Real.exp S * Real.exp (D * S) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnlog : Real.log ((N + h : ℕ) : ℝ) ≤ (D + 1) * S := by
    have hl := Real.log_le_log (by exact_mod_cast hnpos) hnle
    simpa only [Real.log_exp] using hl
  exact hS0 S hSS X (N + h) (Nat.ne_of_gt hnpos) hXlt hlo
    (by nlinarith) hnlog

end Problem337

end

end OAI
