import OAI.Probability.GammaPassage.RealDirectionGeometry
import OAI.Probability.GammaPassage.MeanNorm
import OAI.Probability.GammaPassage.SpatialModulus

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

theorem real_scale_connections (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (A : ℝ) (_hA : 0 < A)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed p‖ ≤ C*t → ‖latticeEmbed q‖ ≤ C*t →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        A*(latticeDistance p q : ℝ)/t+ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (div_pos hε (show 0 < C+1 by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc k)
  filter_upwards [eventually_ge_atTop (max 1 ((N : ℝ)/C))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  let n : ℕ := ⌈C*t⌉₊
  have htn : C*t ≤ (n : ℝ) := Nat.le_ceil _
  have hnu : (n : ℝ) ≤ (C+1)*t := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ C*t by positivity)
    dsimp [n]
    nlinarith
  have hnN : N ≤ n := by
    have hh := (div_le_iff₀ hC).mp ((le_max_right _ _).trans ht)
    have hh' : (N : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hh'
  intro p q hp hq
  have hp' := lattice_mem_box_of_norm p n (hp.trans htn)
  have hq' := lattice_mem_box_of_norm q n (hq.trans htn)
  have hdiff := passageTime_origin_difference_le w hw p q
  have hconn := hN n hnN p hp' q hq'
  have he : (1/(k+1 : ℝ))*(n : ℝ) ≤ ε*t := by
    have ha := mul_le_mul_of_nonneg_left hnu (show 0 ≤ 1/(k+1 : ℝ) by positivity)
    have hb := (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hk
    nlinarith
  rw [← sub_div,abs_div,abs_of_pos ht0]
  apply (div_le_iff₀ ht0).mpr
  rw [add_mul,div_mul_cancel₀ _ ht0.ne']
  linarith

theorem real_scale_connections_normalized (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (A : ℝ) (hA : 0 < A)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖scaledLatticePoint t p‖ ≤ C → ‖scaledLatticePoint t q‖ ≤ C →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        (2*A)*‖scaledLatticePoint t p-scaledLatticePoint t q‖+ε := by
  filter_upwards [real_scale_connections w hw A hA hc C hC ε hε,
    eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro p q hp hq
  rw [scaledLatticePoint_norm t ht0] at hp hq
  have he := ht p q ((div_le_iff₀ ht0).mp hp) ((div_le_iff₀ ht0).mp hq)
  have hd := latticeDistance_le_norm p q
  rw [norm_sub_rev] at hd
  rw [scaledLatticePoint_sub_norm t ht0]
  apply he.trans
  have hh := (div_le_div_of_nonneg_right hd ht0.le)
  simp only [mul_div_assoc] at hh ⊢
  nlinarith [mul_le_mul_of_nonneg_left hh hA.le]

theorem real_direction_limits_of_lattice_limits (w : Edge → ℝ)
    (hw : ∀ e, 0 ≤ w e) (A : ℝ) (hA : 0 < A) (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z))))
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n) :
    ∀ v : Plane, Tendsto (fun t : ℝ => passageTime w 0 (latticeFloor (t • v))/t)
      atTop (𝓝 (μ v)) := by
  obtain ⟨B,hB,hLip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  intro v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (1/2 : ℝ) (ε/(8*(B+4*A)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (B+4*A)*δ ≤ ε/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*(B+4*A) by linarith)).mp (min_le_right (1/2 : ℝ) (ε/(8*(B+4*A))))
    dsimp [δ]
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (2/δ))
  have hM0 : (0 : ℝ) < M := (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).trans hM
  let z := latticeFloor ((M : ℝ) • v)
  let u := (1/(M : ℝ)) • latticeEmbed z
  have huv : ‖u-v‖ < δ := by
    apply (scaled_floor_error M hM0 v).trans_lt
    apply (div_lt_iff₀ hM0).mpr
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM)
    nlinarith
  have hμuv := hLip u v
  let C := ‖v‖+2
  have hC : 0 < C := by dsimp [C]; positivity
  have huC : ‖u‖ < C := by
    have hh := norm_add_le (u-v) v
    rw [sub_add_cancel] at hh
    dsimp [C]
    linarith
  have hp := scaled_floor_tendsto v
  have hq := scaled_lattice_ray_tendsto z M hM0
  have hpC : ∀ᶠ t : ℝ in atTop, ‖scaledLatticePoint t (latticeFloor (t • v))‖ ≤ C :=
    (hp.norm.eventually (gt_mem_nhds (show ‖v‖ < C by dsimp [C]; linarith))).mono (fun _ h => h.le)
  have hqC : ∀ᶠ t : ℝ in atTop, ‖scaledLatticePoint t (⌊t/(M : ℝ)⌋₊ • z)‖ ≤ C :=
    (hq.norm.eventually (gt_mem_nhds huC)).mono (fun _ h => h.le)
  have hpq : ∀ᶠ t : ℝ in atTop,
      ‖scaledLatticePoint t (latticeFloor (t • v))-
        scaledLatticePoint t (⌊t/(M : ℝ)⌋₊ • z)‖ < 2*δ := by
    have hh : ‖v-u‖ < 2*δ := by rw [norm_sub_rev]; linarith
    exact (hp.sub hq).norm.eventually (gt_mem_nhds hh)
  have hcost : ∀ᶠ t : ℝ in atTop,
      |passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u| < ε/4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (passageTime_real_lattice_ray_tendsto w μ hμ hray z M hM0) (ε/4) (by linarith)
  filter_upwards [hpC,hqC,hpq,hcost,
    real_scale_connections_normalized w hw A hA hc C hC (ε/4) (by linarith)] with t hpC hqC hpq hcost ht
  have he := ht _ _ hpC hqC
  have htri : |passageTime w 0 (latticeFloor (t • v))/t-μ v| ≤
      |passageTime w 0 (latticeFloor (t • v))/t-passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t|+
      |passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u|+|μ u-μ v| := by
    calc
      _ = |(passageTime w 0 (latticeFloor (t • v))/t-passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t)+
        (passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u)+(μ u-μ v)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [Real.dist_eq]
  have hmul := mul_lt_mul_of_pos_left huv hB
  nlinarith

end GammaFPP.RealDirectionBridge

namespace GammaFPP
open RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

/-- Almost-sure lattice-ray limits and the Gamma spatial modulus extend the
constructed mean norm to a time constant in every fixed real direction. -/
theorem GammaEnvironment.isTimeConstant_of_ae_lattice_limits
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
    {shape rate : ℝ} (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (hray : ∀ z : Vertex, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z) / n)
        atTop (𝓝 (directionalMeanConstant h hs hr z))) :
    IsTimeConstant P τ (gammaMeanNorm h hs hr) := by
  have hall := ae_all_iff.mpr hray
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        coordinateAllowance shape rate * (latticeDistance p q : ℝ) +
          (1 / (k + 1 : ℝ)) * n := by
    apply ae_all_iff.mpr
    intro k
    exact h.ae_eventually_passageTime_connections hs hr (by positivity)
  intro v
  filter_upwards [h.ae_positive_edges, hall, hc] with ω hp hω hcω
  apply RealDirectionBridge.real_direction_limits_of_lattice_limits
    (fun e => τ e ω) (fun e => (hp e).le)
    (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr)
    (gammaMeanNorm h hs hr) (gammaMeanNorm_laws h hs hr) ?_ hcω v
  intro z
  have he : gammaMeanNorm h hs hr (latticeEmbed z) =
      directionalMeanConstant h hs hr z := by
    change gammaMeanPairSeminorm h hs hr ((z.1 : ℝ), (z.2 : ℝ)) = _
    exact gammaMeanPairSeminorm_integerPair h hs hr z
  rw [he]
  exact hω z

end GammaFPP

end OAI
