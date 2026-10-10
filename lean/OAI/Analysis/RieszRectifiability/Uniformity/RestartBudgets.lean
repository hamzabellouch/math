import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartAreaLoss

namespace OAI

/-!
# Uniform budgets for bad cells and restarts

The class-uniform bad-beta packing constant controls multiplicity tails and the
total mass of restart roots. A relative loss tolerance and a finite bad-depth
budget are chosen before the measure, using only the fixed geometric and Riesz
bounds. Splitting the desired deficit into two halves pays separately for the
discarded high-multiplicity set and the remainders of selected restart regions.
These budgets feed the recursive chart assembly without changing its image or
Lipschitz conclusions.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_bad_beta_total_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G)
    (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular],
      ADRegularWithConstant (p + 1) C μ → GlobalUpperGrowth (p + 1) G μ →
      RieszL2BoundedWithConstant (p + 1) D μ →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : BadBetaDescendant (p + 1) μ R hR k z H ε,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_beta_total_mass hnd C G H ε D
    (zero_lt_one.trans_le hC) hG hH hε
  refine ⟨K, hK, ?_⟩
  intro μ _hreg hAD hg hRiesz
  exact hpack μ hg (fun x hx r hr => (hAD.2 x hx r hr).1) hRiesz

theorem quantitative_bad_beta_stopping {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      (∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
        μ {x | t ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
          (ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)) / t) ∧
      (∀ᵐ x ∂μ, {i : BadBetaDescendant (p + 1) μ R hR k z H ε | x ∈ i.val.cell}.Finite) := by
  obtain ⟨K, hK, hpack⟩ := quantitative_bad_beta_total_mass hnd C G D hC hG H ε hH hε
  refine ⟨K, hK, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hpack := hpack μ hAD hg hRiesz
  let := badBetaDescendant_countable (p + 1) μ R hR k z H ε
  let A (i : BadBetaDescendant (p + 1) μ R hR k z H ε) := i.val.cell
  have hA : ∀ i, MeasurableSet (A i) := fun i => cleanSupportCell_measurable
    μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hp := hpack R hR k z hcore
  constructor
  · intro t ht htt
    exact cellMultiplicity_tail_bound μ A hA _ t hp ht htt
  · have htop : μ (cleanSupportCell μ R hR k z) < ∞ :=
      (measure_mono (show cleanSupportCell μ R hR k z ⊆ supportLatticeCell μ R hR k z
        from fun _ hx => hx.1)).trans_lt (supportLatticeCell_compact μ R hR k z).measure_lt_top
    apply ae_finite_cell_incidence μ A hA
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop.ne) hp

theorem quantitative_bad_beta_restart_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i},
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := quantitative_bad_beta_total_mass hnd C G D hC hG H ε hH hε
  refine ⟨1 + K, by linarith, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hpack := hpack μ hAD hg hRiesz
  have h := restart_roots_total_mass_le μ R hR k z
    (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius))
    (ENNReal.ofReal K) (hpack R hR k z hcore)
  simpa only [ENNReal.ofReal_add zero_le_one hK.le, ENNReal.ofReal_one] using! h

theorem quantitative_restart_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ loss : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i} → ℝ≥0∞,
        (∀ i, loss i ≤ ENNReal.ofReal δ * μ i.val.cell) →
        (∑' i, loss i) ≤ ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := quantitative_bad_beta_restart_mass hnd C G D hC hG H ε hH hε
  refine ⟨ζ / K, div_pos hζ hK, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore loss hloss
  have hpack := hpack μ hAD hg hRiesz
  have h := relative_losses_sum_le_packed_mass (fun i => μ i.val.cell) loss
    (ENNReal.ofReal (ζ / K)) (ENNReal.ofReal K) (μ (cleanSupportCell μ R hR k z))
    hloss (hpack R hR k z hcore)
  have heq : ENNReal.ofReal (ζ / K) * ENNReal.ofReal K = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_mul (div_nonneg hζ.le hK.le), div_mul_cancel₀ ζ hK.ne']
  rwa [heq] at h

theorem quantitative_bad_depth_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      μ {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
        ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hstop⟩ := quantitative_bad_beta_stopping hnd C G D hC hG H ε hH hε
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (K / ζ))
  have hN1 : 1 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNratio : K / ζ ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNrpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hratio : K / (N : ℝ) ≤ ζ := by
    apply (div_le_iff₀ hNrpos).mpr
    have h := (div_le_iff₀ hζ).mp hNratio
    nlinarith
  have hcoef : ENNReal.ofReal K / (N : ℝ≥0∞) ≤ ENNReal.ofReal ζ := by
    have h := ENNReal.ofReal_le_ofReal hratio
    simpa only [ENNReal.ofReal_div_of_pos hNrpos, ENNReal.ofReal_natCast] using! h
  refine ⟨N, hNpos, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hstop := hstop μ hAD hg hRiesz
  have ht := (hstop R hR k z hcore).1 (N : ℝ≥0∞) (by exact_mod_cast hNpos.ne') (by simp)
  calc
    _ ≤ (ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)) / (N : ℝ≥0∞) := ht
    _ = (ENNReal.ofReal K / (N : ℝ≥0∞)) * μ (cleanSupportCell μ R hR k z) := by
      simp only [div_eq_mul_inv, mul_right_comm]
    _ ≤ _ := mul_le_mul_left hcoef _

theorem quantitative_cell_bad_count_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∃ A : Set (Ambient d), MeasurableSet A ∧ A ⊆ cleanSupportCell μ R hR k z ∧
        μ (cleanSupportCell μ R hR k z \ A) ≤ ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) ∧
        ∀ x ∈ A, ∀ q : SupportCellDescendant μ R hR k z,
          cellBadCountBound (fun i => ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)) q N x := by
  classical
  obtain ⟨N, hN, htail⟩ := quantitative_bad_depth_loss_budget hnd C G D hC hG H ε hH hε ζ hζ
  refine ⟨N, hN, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have htail := htail μ hAD hg hRiesz
  let A := {x ∈ cleanSupportCell μ R hR k z |
    badBetaMultiplicity (p + 1) μ R hR k z H ε x < (N : ℝ≥0∞)}
  have hAmeas : MeasurableSet A := (cleanSupportCell_measurable μ R hR k z).inter
    (measurableSet_lt (badBetaMultiplicity_measurable (p + 1) μ R hR k z H ε) measurable_const)
  have hsub : cleanSupportCell μ R hR k z \ A ⊆
      {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} := by
    intro x hx
    by_contra hn
    exact hx.2 ⟨hx.1, lt_of_not_ge hn⟩
  refine ⟨A, hAmeas, fun _ hx => hx.1, (measure_mono hsub).trans (htail R hR k z hcore), ?_⟩
  intro x hx q
  apply cellBadCountBound_of_subtype_incidence_bound _ q N x
  intro F hF
  have hcount : (F.card : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x := by
    calc
      _ = ∑ i ∈ F, i.val.cell.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        symm
        calc
          _ = ∑ _i ∈ F, (1 : ℝ≥0∞) :=
            Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (hF i hi) _)
          _ = _ := by simp
      _ ≤ _ := ENNReal.sum_le_tsum F
  exact_mod_cast hcount.trans hx.2.le

theorem quantitative_selected_restart_uniform_deficit {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Bad := fun i : SupportCellDescendant μ R hR k z =>
          ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
        ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
          (step : ℝ≥0 → ℝ≥0),
          HasSelectedRestartAssembly (p + 1) Bad E step →
          (∀ q, μ (selectedRestartRemainder Bad q.val (E q)) ≤ ENNReal.ofReal δ * μ q.val.cell) →
          ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
            LipschitzWith (badBudgetChartConstant step b) g ∧
            Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
            μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
              ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, hregions⟩ := quantitative_restart_loss_budget hnd C G D hC hG H ε hH hε
    (ζ / 2) (half_pos hζ)
  obtain ⟨b, hb, hcounts⟩ := quantitative_cell_bad_count_budget hnd C G D hC hG H ε hH hε
    (ζ / 2) (half_pos hζ)
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hregions := hregions μ hAD hg hRiesz
  have hcounts := hcounts μ hAD hg hRiesz
  dsimp only
  intro E step hassemble hloss
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
  let q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} :=
    ⟨supportCellRoot μ R hR k z, Or.inl rfl⟩
  obtain ⟨A, _, _, hAmass, hAcount⟩ := hcounts R hR k z hcore
  obtain ⟨g, hg, hgrange, _, hdeficit⟩ := exists_restart_chart_with_original_mass_deficit
    μ R hR k z Bad
    (fun r => selectedRestartRemainder Bad r.val (E r))
    (fun r => selectedRestartParent Bad r.val (E r))
    (fun r => selectedRestartNext Bad r.val (E r)) step
    (fun r w hw => selected_restart_next_consumes_bad_cell Bad r.val (E r) w hw)
    (fun r => selected_restart_partition Bad r.val (E r)) hassemble b q A
    (fun x hx => hAcount x hx.2 q.val)
  have hsum := hregions R hR k z hcore
    (fun r => μ (selectedRestartRemainder Bad r.val (E r))) hloss
  have hbound := hdeficit.trans (add_le_add hAmass hsum)
  have heq : ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_add (half_pos hζ).le (half_pos hζ).le, add_halves]
  refine ⟨g, hg, hgrange, ?_⟩
  simpa only [← add_mul, heq] using! hbound

theorem quantitative_recursive_chart_from_surface_pieces {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧ ∀ (N : ℕ) (P : ℝ≥0), ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      let Bad := fun i : SupportCellDescendant μ R hR k z =>
        ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
      ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
        (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
          ¬ Bad q.val → SelectedRestartSurfaceData (p + 1) Bad q.val (E q) ε N P),
        (∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant (p + 1) G) *
          (μH[((p + 1 : ℕ) : ℝ)] : Measure (Ambient d))
            ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
              ENNReal.ofReal δ * μ q.val.cell) →
        ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
          LipschitzWith (badBudgetChartConstant
            (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) b) g ∧
          Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
          μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
            ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, b, hb, hcharts⟩ := quantitative_selected_restart_uniform_deficit
    hnd C G D hC hG H ε hH hε ζ hζ
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro N P μ _hreg hAD hg hRiesz R hR k z hcore
  have hcharts := hcharts μ hAD hg hRiesz
  dsimp only
  intro E data hloss
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
  have hassemble := has_selected_restart_assembly_of_surface_data (Nat.succ_pos p)
    G hG hg Bad E ε hε hεfine hsmall N P data
  apply hcharts R hR k z hcore E _ hassemble
  intro q
  by_cases hq : Bad q.val
  · rw [selected_restart_remainder_of_bad_root Bad q.val hq (E q), measure_empty]
    exact zero_le
  · exact (selected_restart_remainder_mass_le_surface_loss μ G hG hg R hR k z
      Bad q.val hq (E q) ε hε hεfine hsmall N P (data q hq)).trans (hloss q hq)

end
end RieszRectifiability

end OAI
