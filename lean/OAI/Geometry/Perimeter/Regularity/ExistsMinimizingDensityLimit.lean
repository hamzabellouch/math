import OAI.Geometry.Perimeter.Regularity.DilatedVolumeTest
import OAI.Geometry.Perimeter.Regularity.BlowupHomeomorph

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem exists_minimizing_density_limit {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E) (c : Euc n) :
    ∃ a : ℝ, 0 ≤ a ∧ Tendsto
      (fun r : ℝ ↦ (perimeterMeasure E).real (Metric.ball c r) / r^(n-1))
      (𝓝[>] 0) (𝓝 a) := by
  let f (r : ℝ) := (perimeterMeasure E).real (Metric.ball c r) / r^(n-1)
  let S : Set ℝ := f '' Ioi 0
  have hS : S.Nonempty := ⟨f 1, 1, (by norm_num : (1:ℝ) ∈ Ioi 0), rfl⟩
  have hnonneg : ∀ y ∈ S, 0 ≤ y := by
    rintro y ⟨r, hr, rfl⟩
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le _)
  have hb : BddBelow S := ⟨0, hnonneg⟩
  have hmono := minimizing_perimeter_density_monotone hn hE c
  refine ⟨sInf S, le_csInf hS hnonneg, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro b hb'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hb'.trans_le (csInf_le hb ⟨r, hr, rfl⟩)
  · intro b hb'
    obtain ⟨y, ⟨R, hR, rfl⟩, hy⟩ := exists_lt_of_csInf_lt hS hb'
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds hR : ∀ᶠ r in 𝓝 (0:ℝ), r < R).filter_mono nhdsWithin_le_nhds] with r hr hrR
    exact (hmono hr hR hrR.le).trans_lt hy

theorem minimizing_blowup_ball_real {n : ℕ} (hn : 0 < n)
    {E : Set (Euc n)} (hE : MeasurableSet E) (c : Euc n)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (perimeterMeasure (blownUpSet E c r)).real (Metric.ball 0 R) =
      ((perimeterMeasure E).real (Metric.ball c (r*R)) / (r*R)^(n-1)) * R^(n-1) := by
  have hs := blownUpSet_ball c (0:Euc n) hr R
  simp only [smul_zero, add_zero] at hs
  rw [measureReal_def, perimeterMeasure_open _ Metric.isOpen_ball,
    ← hs, perimeter_blownUpSet_eq hE c hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), measureReal_def,
    perimeterMeasure_open _ Metric.isOpen_ball]
  have hn' : n = (n-1)+1 := by omega
  have hpow : r^n = r^(n-1)*r := by conv_lhs => rw [hn', pow_succ]
  rw [hpow]
  field_simp [hr.ne', hR.ne']
  rw [mul_pow]
  ring

theorem minimizing_dense_null_spheres {n : ℕ} {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (c : Euc n) :
    Dense {r : ℝ | perimeterMeasure E (Metric.sphere c r) = 0} := by
  let := perimeterMeasure_locallyFinite E hE.2.1
  have hc := Measure.countable_meas_level_set_pos
    (μ := perimeterMeasure E) (g := fun x : Euc n ↦ dist x c)
    (continuous_id.dist continuous_const).measurable
  have hd := hc.dense_compl ℝ
  convert hd using 1
  ext r
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt, nonpos_iff_eq_zero, Metric.sphere]

theorem minimizing_density_eq_of_null_spheres {n : ℕ} {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (heq : ∀ r : ℝ, 0 < r → perimeterMeasure E (Metric.sphere 0 r) = 0 →
      (perimeterMeasure E).real (Metric.ball 0 r) = a*r^k) :
    ∀ r : ℝ, 0 < r → (perimeterMeasure E).real (Metric.ball 0 r) = a*r^k := by
  let := perimeterMeasure_finiteOnCompacts E hE.2.1
  have hd := minimizing_dense_null_spheres hE (0:Euc n)
  have hm : Monotone (fun r : ℝ ↦ (perimeterMeasure E).real (Metric.ball 0 r)) := by
    intro r R hrR
    exact measureReal_mono (Metric.ball_subset_ball hrR)
      (measure_ne_top_of_subset Metric.ball_subset_closedBall (isCompact_closedBall (0:Euc n) R).measure_ne_top)
  have ht (r : ℝ) : Tendsto (fun R : ℝ ↦ a*R^k) (𝓝 r) (𝓝 (a*r^k)) := (continuous_const.mul (continuous_id.pow k)).tendsto r
  intro r hr
  apply le_antisymm
  · apply ge_of_tendsto ((ht r).mono_left nhdsWithin_le_nhds :
      Tendsto (fun R : ℝ ↦ a*R^k) (𝓝[>] r) (𝓝 (a*r^k)))
    filter_upwards [self_mem_nhdsWithin] with R hR
    obtain ⟨s, hs, hrs, hsR⟩ := hd.exists_between hR
    have hs0 := hr.trans hrs
    calc
      (perimeterMeasure E).real (Metric.ball 0 r) ≤
          (perimeterMeasure E).real (Metric.ball 0 s) := hm hrs.le
      _ = a*s^k := heq s hs0 hs
      _ ≤ a*R^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le hsR.le k) ha
  · apply le_of_tendsto ((ht r).mono_left nhdsWithin_le_nhds :
      Tendsto (fun R : ℝ ↦ a*R^k) (𝓝[<] r) (𝓝 (a*r^k)))
    filter_upwards [self_mem_nhdsWithin,
      (lt_mem_nhds hr : ∀ᶠ R in 𝓝 r, 0 < R).filter_mono nhdsWithin_le_nhds] with R hR hR0
    obtain ⟨s, hs, hRs, hsr⟩ := hd.exists_between hR
    calc
      a*R^k ≤ a*s^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0.le hRs.le k) ha
      _ = (perimeterMeasure E).real (Metric.ball 0 s) := (heq s (hR0.trans hRs) hs).symm
      _ ≤ (perimeterMeasure E).real (Metric.ball 0 r) := hm hsr.le

theorem minimizing_density_limit_pos {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E)
    {c : Euc n} (hc : c ∈ perimeterSupport E) {a : ℝ}
    (ht : Tendsto (fun r : ℝ ↦ (perimeterMeasure E).real (Metric.ball c r) / r^(n-1))
      (𝓝[>] 0) (𝓝 a)) : 0 < a := by
  obtain ⟨b, hb, hbound⟩ := exists_minimizing_perimeter_lower_density n hn
  apply hb.trans_le
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with r hr
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  rw [measureReal_def, perimeterMeasure_open E Metric.isOpen_ball]
  exact (ENNReal.ofReal_le_iff_le_toReal (hE.2.1 c r hr).ne).mp (hbound E hE c hc r hr)

theorem minimizing_blowup_limit_constant_density {n : ℕ} (hn : 1 < n)
    {E F : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E)
    (hF : IsLocallyPerimeterMinimizing F) (c : Euc n)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0))
    (hconv : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r i)) F ∩ Metric.closedBall x R))
        atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a)
    (hden : Tendsto (fun R : ℝ ↦ (perimeterMeasure E).real (Metric.ball c R) / R^(n-1))
      (𝓝[>] 0) (𝓝 a)) :
    ∀ R : ℝ, 0 < R → (perimeterMeasure F).real (Metric.ball 0 R) = a*R^(n-1) := by
  apply minimizing_density_eq_of_null_spheres hF ha (n-1)
  intro R hR hnull
  have htR : Tendsto (fun i ↦ r i * R) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using htr.mul_const R,
      Eventually.of_forall fun i ↦ mul_pos (hr i) hR⟩
  have htden : Tendsto (fun i ↦ (perimeterMeasure (blownUpSet E c (r i))).real (Metric.ball 0 R))
      atTop (𝓝 (a*R^(n-1))) := by
    simpa only [minimizing_blowup_ball_real (by omega : 0 < n) hE.1 c (hr _) hR, Function.comp_def] using
      (hden.comp htR).mul_const (R^(n-1))
  have htp := tendsto_minimizing_perimeter_ball_of_local_L1 (by omega : 0 < n)
    (fun i ↦ locally_minimizing_blownUpSet hE c (hr i)) hF.1 hconv (0:Euc n) hR hnull
  have htF := (ENNReal.tendsto_toReal (hF.2.1 0 R hR).ne).comp htp
  have htF' : Tendsto (fun i ↦ (perimeterMeasure (blownUpSet E c (r i))).real (Metric.ball 0 R))
      atTop (𝓝 ((perimeterMeasure F).real (Metric.ball 0 R))) := by
    simpa only [measureReal_def, perimeterMeasure_open _ Metric.isOpen_ball, Function.comp_def] using htF
  exact tendsto_nhds_unique htF' htden

theorem minimizing_tangent_cone_subsequence {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E)
    {c : Euc n} (hc : c ∈ perimeterSupport E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0)) :
    ∃ K : Set (Euc n), IsClosed K ∧ IsLocallyPerimeterMinimizing K ∧ IsCone K ∧
      K = (volume.restrict K).support ∧ frontier K = perimeterSupport K ∧ (0:Euc n) ∈ perimeterSupport K ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ (x : Euc n) (R : ℝ), 0 < R →
          Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r (σ i))) K ∩ Metric.closedBall x R))
            atTop (𝓝 0)) ∧
        (∀ R : ℝ, 0 < R → perimeterMeasure K (Metric.sphere 0 R) = 0 →
          Tendsto (fun i ↦ perimeter (blownUpSet E c (r (σ i))) (Metric.ball 0 R)) atTop
            (𝓝 (perimeter K (Metric.ball 0 R)))) := by
  obtain ⟨F, hF, σ, hσ, hconv, hP⟩ := minimizing_global_compactness (by omega : 0 < n)
    (fun i ↦ blownUpSet E c (r i)) (fun i ↦ locally_minimizing_blownUpSet hE c (hr i))
  obtain ⟨a, ha, hden⟩ := exists_minimizing_density_limit hn hE c
  have ha0 := minimizing_density_limit_pos hn hE hc hden
  have hdensity := minimizing_blowup_limit_constant_density hn hE hF c
    (fun i ↦ r (σ i)) (fun i ↦ hr (σ i)) (htr.comp hσ.tendsto_atTop) hconv ha hden
  let K := (volume.restrict F).support
  obtain ⟨hK, hFK, hminK, hconeK, hfrontK⟩ :=
    minimizing_constant_density_conical_representative hn hF ha hdensity
  have hlocal : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r (σ i))) K ∩ Metric.closedBall x R))
        atTop (𝓝 0) := by
    intro x R hR
    convert hconv x R hR using 1
    funext i
    rw [measureReal_def, measureReal_def]
    congr 1
    apply measure_congr
    filter_upwards [hFK] with y hy
    simp only [mem_inter_iff, mem_symmDiff]
    change (y ∈ F) = (y ∈ K) at hy
    rw [hy]
  have hcanonical : K = (volume.restrict K).support := by
    change (volume.restrict F).support = (volume.restrict K).support
    rw [Measure.restrict_congr_set hFK]
  refine ⟨K, hK, hminK, hconeK, hcanonical, hfrontK.trans (perimeterSupport_eq_of_ae hFK), ?_,
    σ, hσ, hlocal, ?_⟩
  · intro R hR
    rw [← perimeter_eq_of_ae hFK]
    have hh : 0 < (perimeter F (Metric.ball 0 R)).toReal := by
      rw [← perimeterMeasure_open F Metric.isOpen_ball]
      change 0 < (perimeterMeasure F).real (Metric.ball 0 R)
      rw [hdensity R hR]
      positivity
    exact (ENNReal.toReal_pos_iff.mp hh).1
  · intro R hR hnull
    exact tendsto_minimizing_perimeter_ball_of_local_L1 (by omega : 0 < n)
      (fun i ↦ locally_minimizing_blownUpSet hE c (hr (σ i))) hminK.1 hlocal (0:Euc n) hR hnull

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem ae_subset_of_local_L1_limits {n : ℕ}
    (E F : ℕ → Set (Euc n)) (K L : Set (Euc n)) (hsub : ∀ i, E i ⊆ F i)
    (hE : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) K ∩ Metric.closedBall x R)) atTop (𝓝 0))
    (hF : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (F i) L ∩ Metric.closedBall x R)) atTop (𝓝 0)) :
    K ≤ᵐ[volume] L := by
  have hENN (A : ℕ → Set (Euc n)) (B : Set (Euc n)) (x : Euc n) (R : ℝ)
      (ht : Tendsto (fun i ↦ volume.real (symmDiff (A i) B ∩ Metric.closedBall x R)) atTop (𝓝 0)) :
      Tendsto (fun i ↦ volume (symmDiff (A i) B ∩ Metric.closedBall x R)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.tendsto (0:ℝ) |>.comp ht
    simp only [Function.comp_def, measureReal_def, ENNReal.ofReal_zero,
      ENNReal.ofReal_toReal (measure_ne_top_of_subset inter_subset_right
        (isCompact_closedBall x R).measure_ne_top)] at h
    exact h
  have hz (x : Euc n) (R : ℝ) (hR : 0 < R) : volume ((K \ L) ∩ Metric.closedBall x R) = 0 := by
    apply le_antisymm _ bot_le
    have ht := (hENN E K x R (hE x R hR)).add (hENN F L x R (hF x R hR))
    simp only [zero_add] at ht
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun i ↦ by
      apply (measure_mono (show (K \ L) ∩ Metric.closedBall x R ⊆
        (symmDiff (E i) K ∩ Metric.closedBall x R) ∪
          (symmDiff (F i) L ∩ Metric.closedBall x R) from ?_)).trans
          (measure_union_le _ _)
      intro y hy
      by_cases hyE : y ∈ E i
      · exact Or.inr ⟨Or.inl ⟨hsub i hyE, hy.1.2⟩, hy.2⟩
      · exact Or.inl ⟨Or.inr ⟨hy.1.1, hyE⟩, hy.2⟩
  apply ae_le_set.mpr
  have hs : K \ L ⊆ ⋃ m : ℕ, (K \ L) ∩ Metric.closedBall 0 ((m:ℝ)+1) := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_nat_gt (dist x (0:Euc n))
    exact mem_iUnion.mpr ⟨m, hx, Metric.mem_closedBall.mpr (by linarith)⟩
  exact le_antisymm ((measure_mono hs).trans (le_of_eq (measure_iUnion_null fun m ↦
    hz 0 ((m:ℝ)+1) (by positivity)))) bot_le

theorem canonical_subset_of_ae {n : ℕ} {K L : Set (Euc n)}
    (hK : K = (volume.restrict K).support) (hL : L = (volume.restrict L).support)
    (hKL : K ≤ᵐ[volume] L) : K ⊆ L := by
  rw [hK, hL]
  exact Measure.support_mono (Measure.restrict_mono_ae hKL)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem nested_minimizing_tangent_cones {n : ℕ} (hn : 1 < n)
    {E F : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E)
    (hF : IsLocallyPerimeterMinimizing F) (hEF : E ⊆ F)
    {c : Euc n} (hcE : c ∈ perimeterSupport E) (hcF : c ∈ perimeterSupport F)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0)) :
    ∃ K L : Set (Euc n),
      IsClosed K ∧ IsClosed L ∧ IsLocallyPerimeterMinimizing K ∧
      IsLocallyPerimeterMinimizing L ∧ IsCone K ∧ IsCone L ∧ K ⊆ L ∧
      K = (volume.restrict K).support ∧ L = (volume.restrict L).support ∧
      frontier K = perimeterSupport K ∧ frontier L = perimeterSupport L ∧
      (0:Euc n) ∈ perimeterSupport K ∧ (0:Euc n) ∈ perimeterSupport L ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ (x : Euc n) (R : ℝ), 0 < R →
          Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r (σ i))) K ∩ Metric.closedBall x R))
            atTop (𝓝 0)) ∧
        (∀ (x : Euc n) (R : ℝ), 0 < R →
          Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet F c (r (σ i))) L ∩ Metric.closedBall x R))
            atTop (𝓝 0)) ∧
        (∀ R : ℝ, 0 < R → perimeterMeasure K (Metric.sphere 0 R) = 0 →
          Tendsto (fun i ↦ perimeter (blownUpSet E c (r (σ i))) (Metric.ball 0 R)) atTop
            (𝓝 (perimeter K (Metric.ball 0 R)))) ∧
        (∀ R : ℝ, 0 < R → perimeterMeasure L (Metric.sphere 0 R) = 0 →
          Tendsto (fun i ↦ perimeter (blownUpSet F c (r (σ i))) (Metric.ball 0 R)) atTop
            (𝓝 (perimeter L (Metric.ball 0 R)))) := by
  obtain ⟨K, hKc, hKm, hKcone, hKcan, hKf, hK0, σ, hσ, hEK, hPK⟩ :=
    minimizing_tangent_cone_subsequence hn hE hcE r hr htr
  obtain ⟨L, hLc, hLm, hLcone, hLcan, hLf, hL0, τ, hτ, hFL, hPL⟩ :=
    minimizing_tangent_cone_subsequence hn hF hcF (fun i ↦ r (σ i))
      (fun i ↦ hr (σ i)) (htr.comp hσ.tendsto_atTop)
  have hEK' : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r (σ (τ i)))) K ∩ Metric.closedBall x R))
        atTop (𝓝 0) := by
    intro x R hR
    exact (hEK x R hR).comp hτ.tendsto_atTop
  have hKL : K ⊆ L := canonical_subset_of_ae hKcan hLcan
    (ae_subset_of_local_L1_limits
      (fun i ↦ blownUpSet E c (r (σ (τ i))))
      (fun i ↦ blownUpSet F c (r (σ (τ i)))) K L
      (fun i x hx ↦ hEF hx) hEK' hFL)
  refine ⟨K, L, hKc, hLc, hKm, hLm, hKcone, hLcone, hKL, hKcan, hLcan,
    hKf, hLf, hK0, hL0, σ ∘ τ, hσ.comp hτ, hEK', hFL, ?_, hPL⟩
  intro R hR hnull
  exact (hPK R hR hnull).comp hτ.tendsto_atTop

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem minimizing_support_limit_of_local_L1 {n : ℕ} (hn : 1 < n)
    (E : ℕ → Set (Euc n)) {F : Set (Euc n)}
    (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) (hF : IsLocallyPerimeterMinimizing F)
    (hconv : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall x R)) atTop (𝓝 0))
    (x : ℕ → Euc n) {y : Euc n} (hx : ∀ i, x i ∈ perimeterSupport (E i))
    (htx : Tendsto x atTop (𝓝 y)) : y ∈ perimeterSupport F := by
  by_contra hy
  change ¬ ∀ R : ℝ, 0 < R → 0 < perimeter F (Metric.ball y R) at hy
  push Not at hy
  obtain ⟨R, hR, hzero⟩ := hy
  have hzero' : perimeter F (Metric.ball y R) = 0 := bot_unique hzero
  obtain ⟨s, hs, hs0, hsR⟩ := (minimizing_dense_null_spheres hF y).exists_between hR
  have hsP : perimeter F (Metric.ball y s) = 0 := by
    apply bot_unique
    exact (perimeter_mono_region F (Metric.ball_subset_ball hsR.le)).trans hzero
  have htP := tendsto_minimizing_perimeter_ball_of_local_L1 (by omega : 0 < n)
    hE hF.1 hconv y hs0 hs
  rw [hsP] at htP
  obtain ⟨b, hb, hbound⟩ := exists_minimizing_perimeter_lower_density n hn
  have hevent : ∀ᶠ i in atTop, ENNReal.ofReal (b * (s/2)^(n-1)) ≤ perimeter (E i) (Metric.ball y s) := by
    filter_upwards [htx.eventually (Metric.ball_mem_nhds y (by positivity : 0 < s/2))] with i hi
    apply (hbound (E i) (hE i) (x i) (hx i) (s/2) (by positivity)).trans
    apply perimeter_mono_region
    intro z hz
    apply Metric.mem_ball.mpr
    have htri := dist_triangle z (x i) y
    have hz' := Metric.mem_ball.mp hz
    have hi' := Metric.mem_ball.mp hi
    linarith
  have hle := ge_of_tendsto htP hevent
  have hpos : 0 < ENNReal.ofReal (b * (s/2)^(n-1)) := ENNReal.ofReal_pos.mpr (by positivity)
  exact (not_le_of_gt hpos) hle

theorem minimizing_support_eventually_hits_of_local_L1 {n : ℕ} (hn : 0 < n)
    (E : ℕ → Set (Euc n)) {F : Set (Euc n)}
    (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) (hF : IsLocallyPerimeterMinimizing F)
    (hconv : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall x R)) atTop (𝓝 0))
    {x : Euc n} (hx : x ∈ perimeterSupport F) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ y ∈ perimeterSupport (E i), dist y x < ε := by
  obtain ⟨s, hs, hs0, hsε⟩ := (minimizing_dense_null_spheres hF x).exists_between hε
  have htP := tendsto_minimizing_perimeter_ball_of_local_L1 hn hE hF.1 hconv x hs0 hs
  filter_upwards [htP.eventually (lt_mem_nhds (hx s hs0))] with i hi
  have hi' : perimeterMeasure (E i) (Metric.ball x s) ≠ 0 := by
    rw [perimeterMeasure_open _ Metric.isOpen_ball]
    exact hi.ne'
  have hsupport : ∀ᵐ y ∂perimeterMeasure (E i), y ∈ perimeterSupport (E i) := by
    rw [← perimeterMeasure_support]; exact (perimeterMeasure (E i)).support_mem_ae
  obtain ⟨y, hy, hyS⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hi' (ae_restrict_of_ae hsupport)
  exact ⟨y, hyS, (Metric.mem_ball.mp hy).trans hsε⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem minimizing_supports_locally_converge {n : ℕ} (hn : 1 < n)
    (E : ℕ → Set (Euc n)) {F : Set (Euc n)}
    (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) (hF : IsLocallyPerimeterMinimizing F)
    (hconv : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall x R)) atTop (𝓝 0))
    {C : Set (Euc n)} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop,
      (∀ x ∈ perimeterSupport (E i) ∩ C, ∃ y ∈ perimeterSupport F, dist x y < ε) ∧
      (∀ y ∈ perimeterSupport F ∩ C, ∃ x ∈ perimeterSupport (E i), dist x y < ε) := by
  classical
  have hupper : ∀ᶠ i in atTop,
      ∀ x ∈ perimeterSupport (E i) ∩ C, ∃ y ∈ perimeterSupport F, dist x y < ε := by
    by_contra h
    have hf : ∃ᶠ i in atTop, ∃ x ∈ perimeterSupport (E i) ∩ C,
        ∀ y ∈ perimeterSupport F, ε ≤ dist x y := by
      simpa only [not_eventually, not_forall, not_exists, not_and, not_lt, exists_prop] using h
    obtain ⟨σ, hσ, hσbad⟩ := extraction_of_frequently_atTop hf
    choose x hx hbad using hσbad
    obtain ⟨y, hyC, τ, hτ, hy⟩ := hC.tendsto_subseq (fun i ↦ (hx i).2)
    have hyS : y ∈ perimeterSupport F := minimizing_support_limit_of_local_L1 hn
      (fun i ↦ E (σ (τ i))) (fun i ↦ hE (σ (τ i))) hF
      (fun z R hR ↦ (hconv z R hR).comp (hσ.comp hτ).tendsto_atTop)
      (fun i ↦ x (τ i)) (fun i ↦ (hx (τ i)).1) hy
    have ht : ∀ᶠ i in atTop, dist (x (τ i)) y < ε :=
      hy.eventually (Metric.ball_mem_nhds y hε)
    obtain ⟨i, hi⟩ := ht.exists
    exact (not_lt_of_ge (hbad (τ i) y hyS)) hi
  have hlower : ∀ᶠ i in atTop,
      ∀ y ∈ perimeterSupport F ∩ C, ∃ x ∈ perimeterSupport (E i), dist x y < ε := by
    by_contra h
    have hf : ∃ᶠ i in atTop, ∃ y ∈ perimeterSupport F ∩ C,
        ∀ x ∈ perimeterSupport (E i), ε ≤ dist x y := by
      simpa only [not_eventually, not_forall, not_exists, not_and, not_lt, exists_prop] using h
    obtain ⟨σ, hσ, hσbad⟩ := extraction_of_frequently_atTop hf
    choose y hy hbad using hσbad
    obtain ⟨z, hzC, τ, hτ, hz⟩ := hC.tendsto_subseq (fun i ↦ (hy i).2)
    have hzS : z ∈ perimeterSupport F := (isClosed_perimeterSupport F).mem_of_tendsto hz
      (Eventually.of_forall fun i ↦ (hy (τ i)).1)
    have hhits := minimizing_support_eventually_hits_of_local_L1 (by omega : 0 < n)
      (fun i ↦ E (σ (τ i))) (fun i ↦ hE (σ (τ i))) hF
      (fun x R hR ↦ (hconv x R hR).comp (hσ.comp hτ).tendsto_atTop) hzS (by positivity : 0 < ε/2)
    have hnear : ∀ᶠ i in atTop, dist (y (τ i)) z < ε/2 :=
      hz.eventually (Metric.ball_mem_nhds z (by positivity))
    obtain ⟨i, hi, hni⟩ := (hhits.and hnear).exists
    obtain ⟨x, hxS, hxz⟩ := hi
    have htri := dist_triangle x z (y (τ i))
    rw [dist_comm z (y (τ i))] at htri
    have hb := hbad (τ i) x hxS
    linarith
  exact hupper.and hlower

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem perimeterSupport_blownUpSet {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {r : ℝ} (hr : 0 < r) (x : Euc n) :
    x ∈ perimeterSupport (blownUpSet E c r) ↔ c + r • x ∈ perimeterSupport E := by
  have hpos : 0 < ENNReal.ofReal (r * (r^n)⁻¹) := ENNReal.ofReal_pos.mpr (by positivity)
  constructor
  · intro hx R hR
    have h := hx (R/r) (div_pos hR hr)
    rw [← blownUpSet_ball c x hr, perimeter_blownUpSet_eq hE c hr] at h
    simp only [mul_div_cancel₀ _ hr.ne'] at h
    exact (ENNReal.mul_pos_iff.mp h).2
  · intro hx R hR
    rw [← blownUpSet_ball c x hr, perimeter_blownUpSet_eq hE c hr]
    exact ENNReal.mul_pos hpos.ne' (hx (r*R) (mul_pos hr hR)).ne'

theorem cone_blowup_support_affine_mem {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hcone : IsCone E) (c : Euc n) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < 1+r*t) {x : Euc n}
    (hx : x ∈ perimeterSupport (blownUpSet E c r)) :
    (1+r*t) • x + t • c ∈ perimeterSupport (blownUpSet E c r) := by
  rw [perimeterSupport_blownUpSet hE c hr] at hx ⊢
  have h := (isCone_perimeterSupport hE hcone (1+r*t) ht (c+r • x)).mpr hx
  convert h using 1
  module

theorem minimizing_cone_tangent_support_line_invariant {n : ℕ} (hn : 1 < n)
    {E F : Set (Euc n)} (hE : IsLocallyPerimeterMinimizing E)
    (hcone : IsCone E) (hF : IsLocallyPerimeterMinimizing F) (c : Euc n)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (htr : Tendsto r atTop (𝓝 0))
    (hconv : ∀ (x : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (blownUpSet E c (r i)) F ∩ Metric.closedBall x R))
        atTop (𝓝 0)) :
    ∀ (t : ℝ) (x : Euc n), x ∈ perimeterSupport F → x + t • c ∈ perimeterSupport F := by
  intro t x hx
  have hmin (i : ℕ) := locally_minimizing_blownUpSet hE c (hr i)
  have hpositive : ∀ᶠ i in atTop, 0 < 1+r i*t := by
    have ht : Tendsto (fun i ↦ 1+r i*t) atTop (𝓝 (1:ℝ)) := by
      simpa using tendsto_const_nhds.add (htr.mul_const t)
    exact ht.eventually (lt_mem_nhds zero_lt_one)
  have hhits (j : ℕ) : ∀ᶠ i in atTop,
      (∃ y ∈ perimeterSupport (blownUpSet E c (r i)), dist y x < (1/2:ℝ)^j) ∧ 0 < 1+r i*t :=
    (minimizing_support_eventually_hits_of_local_L1 (by omega : 0 < n)
      (fun i ↦ blownUpSet E c (r i)) hmin hF hconv hx (by positivity)).and hpositive
  obtain ⟨σ, hσ, hσhit⟩ := extraction_forall_of_eventually hhits
  choose y hyS hynear using fun i ↦ (hσhit i).1
  have hty : Tendsto y atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ (hynear i).le)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htr' : Tendsto (fun i ↦ 1+r (σ i)*t) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.add ((htr.comp hσ.tendsto_atTop).mul_const t)
  have hty' : Tendsto (fun i ↦ (1+r (σ i)*t) • y i + t • c) atTop (𝓝 (x+t • c)) := by
    simpa using (htr'.smul hty).add_const (t • c)
  exact minimizing_support_limit_of_local_L1 hn (fun i ↦ blownUpSet E c (r (σ i)))
    (fun i ↦ hmin (σ i)) hF (fun z R hR ↦ (hconv z R hR).comp hσ.tendsto_atTop)
    (fun i ↦ (1+r (σ i)*t) • y i + t • c)
    (fun i ↦ cone_blowup_support_affine_mem hE.1 hcone c (hr (σ i)) (hσhit i).2 (hyS i)) hty'

end RPISingularHarnack

end

end OAI
