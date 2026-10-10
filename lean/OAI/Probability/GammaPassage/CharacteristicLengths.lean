import OAI.Probability.GammaPassage.ShortCrossingProbability
import OAI.Probability.GammaPassage.RecordScales

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

noncomputable def firstDyadicExponent (p : ℕ → ℝ) (q : ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ j, p j ≤ q then Nat.find h else 0

theorem firstDyadicExponent_spec (p : ℕ → ℝ) (q : ℝ) (h : ∃ j, p j ≤ q) :
    p (firstDyadicExponent p q) ≤ q := by
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_spec h

theorem firstDyadicExponent_le (p : ℕ → ℝ) (q : ℝ) (j : ℕ) (hj : p j ≤ q) :
    firstDyadicExponent p q ≤ j := by
  have h : ∃ j, p j ≤ q := ⟨j,hj⟩
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_min' h hj

theorem firstDyadicExponent_min (p : ℕ → ℝ) (q : ℝ) (j : ℕ)
    (hj : j < firstDyadicExponent p q) : q < p j := by
  by_contra hh
  exact (not_le_of_gt hj) (firstDyadicExponent_le p q j (le_of_not_gt hh))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

noncomputable def sourceDyadicCrossingProbability (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) (k j : ℕ) : ℝ :=
  P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) (sourceCrossingK shape rate μ b)
    ((2 : ℝ)^k) ((2 : ℤ)^j) 0}

noncomputable def characteristicExponent (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) : ℕ :=
  firstDyadicExponent (sourceDyadicCrossingProbability P τ shape rate μ b k) q

noncomputable def characteristicLength (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) : ℤ :=
  (2 : ℤ)^(characteristicExponent P τ shape rate μ b q k)

variable {P τ}

theorem characteristicLength_pos (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) :
    0 < characteristicLength P τ shape rate μ b q k := by unfold characteristicLength; positivity

/-- The first dyadic crossing threshold exists and occurs by `2^(3*k)`. -/
theorem gamma_characteristic_lengths_exist (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∀ᶠ k : ℕ in atTop,
      characteristicExponent P τ shape rate (gammaMeanNorm h hshape hrate) b q k ≤ 3*k ∧
      P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b)
        ((2 : ℝ)^k) (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k) 0} ≤ q := by
  filter_upwards [(gamma_source_tilt h hshape hrate b hb).eventually (gt_mem_nhds hq)] with k hk
  have hh : sourceDyadicCrossingProbability P τ shape rate (gammaMeanNorm h hshape hrate) b k (3*k) ≤ q := hk.le
  exact ⟨firstDyadicExponent_le _ _ _ hh,firstDyadicExponent_spec _ _ ⟨3*k,hh⟩⟩

/-- Every smaller dyadic size has crossing probability strictly above q. -/
theorem characteristicLength_minimal (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k j : ℕ)
    (hj : (2 : ℤ)^j < characteristicLength P τ shape rate μ b q k) :
    q < sourceDyadicCrossingProbability P τ shape rate μ b k j := by
  have hj' : j < characteristicExponent P τ shape rate μ b q k := by
    by_contra hh
    have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (le_of_not_gt hh)
    exact (not_le_of_gt hj) he
  exact firstDyadicExponent_min _ _ _ hj'

/-- The characteristic lengths grow faster than the transverse scale:
`L_k / 2^k → ∞`. -/
theorem gamma_characteristic_lengths_ratio (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k : ℕ => (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ)/(2 : ℝ)^k) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hK : 0 < sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b := by unfold sourceCrossingK; positivity
  have hs := gamma_short_crossing_probability h hshape hrate b (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b) C hb hK hC q hq1
  have h2 := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2)
  filter_upwards [h2.eventually hs,gamma_characteristic_lengths_exist h hshape hrate b q hb hq] with k hk he
  have hL : 1 ≤ characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k := characteristicLength_pos shape rate (gammaMeanNorm h hshape hrate) b q k
  have hgt : C*(2 : ℝ)^k < (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ) := by
    by_contra hn
    exact (not_lt_of_ge he.2) (hk _ hL (le_of_not_gt hn))
  have hr : C < (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ)/(2 : ℝ)^k :=
    (lt_div_iff₀ (by positivity)).mpr hgt
  exact (le_max_right _ _).trans hr.le

/-- Characteristic lengths have arbitrarily large record scales satisfying
the dyadic comparison bound. -/
theorem gamma_characteristic_record_scales (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∃ k0 : ℕ, ∀ N, ∃ k, N < k ∧ k0 ≤ k ∧
      ∀ j, j ≤ k-k0 → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ) ≤
        (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q (k-j) : ℝ) := by
  obtain ⟨k0,hk0⟩ := eventually_atTop.mp (gamma_characteristic_lengths_exist h hshape hrate b q hb hq)
  refine ⟨k0,record_scales_from (fun k => (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ)) k0 (fun k _ => by exact_mod_cast characteristicLength_pos shape rate (gammaMeanNorm h hshape hrate) b q k) ?_⟩
  intro k hk
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (hk0 k hk).1
  have he : characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k ≤ (2 : ℤ)^(3*k) := hh
  exact_mod_cast he

end GammaFPP.CrossingBridge

end OAI
