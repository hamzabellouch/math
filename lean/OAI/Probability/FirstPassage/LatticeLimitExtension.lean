import OAI.Probability.FirstPassage.RealScaleConnections

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

lemma passageTime_real_lattice_ray_tendsto (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z)))) (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) atTop
      (𝓝 (μ ((1/M) • latticeEmbed z))) := by
  have hn : Tendsto (fun t : ℝ => ⌊t/M⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hM)
  have hh := ((hray z).comp hn).mul (floor_real_ratio_tendsto M hM)
  have he : (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) =ᶠ[atTop]
      (fun t : ℝ => (passageTime w 0 (⌊t/M⌋₊ • z)/(⌊t/M⌋₊ : ℝ))*((⌊t/M⌋₊ : ℝ)/t)) := by
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with t ht
    have hn0 : (⌊t/M⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊t/M⌋₊ ≠ 0 by omega)
    field_simp
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hM),mul_comm]
  exact hh.congr' he.symm

theorem real_direction_limits_of_lattice_limits (w : Edge → ℝ)
    (hw : ∀ e, 0 ≤ w e) (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z))))
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n) :
    ∀ v : Plane, Tendsto (fun t : ℝ => passageTime w 0 (latticeFloor (t • v))/t)
      atTop (𝓝 (μ v)) := by
  obtain ⟨B,hB,hLip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  intro v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (1/2 : ℝ) (ε/(8*(B+8)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (B+8)*δ ≤ ε/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*(B+8) by linarith)).mp (min_le_right (1/2 : ℝ) (ε/(8*(B+8))))
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
    real_scale_connections_normalized w hw hc C hC (ε/4) (by linarith)] with t hpC hqC hpq hcost ht
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

end PlanarFPP

end OAI
