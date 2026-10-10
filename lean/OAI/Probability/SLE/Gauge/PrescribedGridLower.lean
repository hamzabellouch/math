import OAI.Probability.SLE.Mass.LocalGridMass
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.HausdorffLimits

namespace OAI

/-! Eventual bounds on the exact prescribed grid imply an arbitrary-cover
Hausdorff lower bound. Finitely many early batches are restored uniformly. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma prescribed_grid_ball_bound
    (μ : Measure ℂ) [IsFiniteMeasure μ] (κ : ℝ) (W : Target.WienerLaw)
    (hm1 : 0 < Target.moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (n₀ : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hcell : ∀ e : Target.Entry, Target.ValidEntry κ W e → n₀ ≤ e.1 →
      ∀ i : ℤ×ℤ, μ (closedBall (coverGridCenter (Target.entryRadius κ W e) i)
        (2*Target.entryRadius κ W e)) ≤ ENNReal.ofReal
          (D*Target.entryValue e*(Target.entryRadius κ W e)^Target.d κ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, ∀ s : ℝ, 0 < s →
      μ (ball x s) ≤ ENNReal.ofReal (C*Target.gauge κ W s) := by
  let F : ℝ → ℝ := fun s => ⨆ x : ℂ, (μ (ball x s)).toReal
  have hμ (x : ℂ) (s : ℝ) : (μ (ball x s)).toReal ≤ (μ univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ _))
  have hbd (s : ℝ) : BddAbove (range (fun x : ℂ => (μ (ball x s)).toReal)) :=
    ⟨(μ univ).toReal,by rintro _ ⟨x,rfl⟩; exact hμ x s⟩
  have hbound (s : ℝ) (_hs : 0 < s) : F s ≤ (μ univ).toReal := ciSup_le (fun x => hμ x s)
  have htail (e : Target.Entry) (he : Target.ValidEntry κ W e) (hen : n₀ ≤ e.1)
      (s : ℝ) (hs : 0 < s) : F s ≤ (324*D)*Target.entryCost κ W e s := by
    apply ciSup_le
    intro x
    have hr : 0 < Target.entryRadius κ W e := Target.radii_pos κ W ⟨e,he⟩
    have hv : 0 < Target.entryValue e := Target.weights_pos κ W ⟨e,he⟩
    let H := D*Target.entryValue e*(Target.entryRadius κ W e)^Target.d κ
    have hH : 0 ≤ H := mul_nonneg (mul_nonneg hD hv.le) (Real.rpow_nonneg hr.le _)
    have hg := localGrid_mass_bound μ hr (show 0 ≤ 2*s by positivity) hH
      (hcell e he hen) (ball x s) (fun y hy z hz =>
        (dist_triangle_right y z x).trans (by
          have hy' : dist y x < s := hy
          have hz' : dist z x < s := hz
          linarith))
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    have hmax : max 1 ((2*s/Target.entryRadius κ W e)^2) ≤
        4*max 1 ((s/Target.entryRadius κ W e)^2) := by
      apply max_le
      · nlinarith [le_max_left (1:ℝ) ((s/Target.entryRadius κ W e)^2)]
      · have heq : (2*s/Target.entryRadius κ W e)^2=4*(s/Target.entryRadius κ W e)^2 := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    calc
      (μ (ball x s)).toReal ≤ 81*H*max 1 ((2*s/Target.entryRadius κ W e)^2) := ht
      _ ≤ 81*H*(4*max 1 ((s/Target.entryRadius κ W e)^2)) :=
        mul_le_mul_of_nonneg_left hmax (mul_nonneg (by norm_num) hH)
      _ = (324*D)*Target.entryCost κ W e s := by unfold H Target.entryCost; ring
  obtain ⟨C,hC,hCf⟩ := Target.gauge_restore_early_batches κ W hm1 hJ n₀ F
    ENNReal.toReal_nonneg hbound htail
  refine ⟨C,hC,?_⟩
  intro x s hs
  have ht : (μ (ball x s)).toReal ≤ C*Target.gauge κ W s :=
    (le_ciSup (hbd s) x).trans (hCf s hs)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (ball x s))]
  exact ENNReal.ofReal_le_ofReal ht

lemma Target.hausdorffGauge_le_hausdorff (h : ℝ → ℝ) :
    (hausdorffGauge h).toOuterMeasure ≤ Target.hausdorff h := by
  rw [hausdorffGauge,Measure.mkMetric_toOuterMeasure]
  apply OuterMeasure.mkMetric_mono
  filter_upwards [] with r
  dsimp only [extendedGauge]
  by_cases hr : r=∞
  · simp only [hr,ite_true,le_top]
  · simp only [hr,ite_false,le_refl]

lemma prescribed_grid_mass_distribution
    (μ : Measure ℂ) [IsFiniteMeasure μ] (κ : ℝ) (W : Target.WienerLaw)
    (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    (hm1 : 0 < Target.moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (n₀ : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hcell : ∀ e : Target.Entry, Target.ValidEntry κ W e → n₀ ≤ e.1 →
      ∀ i : ℤ×ℤ, μ (closedBall (coverGridCenter (Target.entryRadius κ W e) i)
        (2*Target.entryRadius κ W e)) ≤ ENNReal.ofReal
          (D*Target.entryValue e*(Target.entryRadius κ W e)^Target.d κ)) :
    ∃ C : ℝ, 0 < C ∧ μ.toOuterMeasure ≤ ENNReal.ofReal C • Target.hausdorff (Target.gauge κ W) := by
  obtain ⟨C,hC,hball⟩ := prescribed_grid_ball_bound μ κ W hm1 hJ n₀ D hD hcell
  let C' : ℝ≥0 := ⟨C,hC.le⟩
  have hC' : 0 < C' := hC
  have hg' : IsGauge (Target.gauge κ W) := ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2⟩
  have hc : (C':ℝ≥0∞)=ENNReal.ofReal C := ENNReal.ofReal_coe_nnreal.symm
  have hm := gauge_mass_distribution hg' μ C' hC' 1 (by norm_num)
    (fun x r hr _ => by simpa only [ENNReal.ofReal_mul hC.le,← hc] using hball x r hr)
  refine ⟨C,hC,?_⟩
  intro A
  have hm' := hm A
  change μ A ≤ (C':ℝ≥0∞)*hausdorffGauge (Target.gauge κ W) A at hm'
  change μ A ≤ ENNReal.ofReal C*Target.hausdorff (Target.gauge κ W) A
  rw [hc] at hm'
  exact hm'.trans (mul_le_mul' le_rfl (Target.hausdorffGauge_le_hausdorff _ A))

end SLEExactGauge

end

end OAI
