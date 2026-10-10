import OAI.Geometry.Perimeter.Regularity.VectorEnergy
import OAI.Geometry.Perimeter.Regularity.ExistsCompactTraceOnBounded

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI

section Covers
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_diameter_cover_of_hausdorff_zero (S : Set X) (m : ℕ) (hm : 0 < m)
    (hS : Measure.hausdorffMeasure (m : ℝ) S = 0)
    {δ ε : ℝ≥0∞} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ t : ℕ → Set X, S ⊆ ⋃ j, t j ∧ (∀ j, Metric.ediam (t j) ≤ δ) ∧
      (∑' j, Metric.ediam (t j) ^ m) < ε := by
  have hi : (⨅ (t : ℕ → Set X) (_ : S ⊆ ⋃ j, t j)
      (_ : ∀ j, Metric.ediam (t j) ≤ δ),
      ∑' j, ⨆ _ : (t j).Nonempty, Metric.ediam (t j) ^ (m : ℝ)) < ε := by
    apply lt_of_le_of_lt _ (show Measure.hausdorffMeasure (m : ℝ) S < ε by simpa [hS])
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)
  obtain ⟨t, ht⟩ := iInf_lt_iff.mp hi
  obtain ⟨hcover, ht⟩ := iInf_lt_iff.mp ht
  obtain ⟨hdiam, ht⟩ := iInf_lt_iff.mp ht
  refine ⟨t, hcover, hdiam, ?_⟩
  convert ht using 1
  congr 1
  funext j
  by_cases hj : (t j).Nonempty
  · simp only [ENNReal.rpow_natCast, iSup_pos hj]
  · have he : t j = ∅ := Set.not_nonempty_iff_eq_empty.mp hj
    simp [he, hm.ne', ENNReal.zero_rpow_of_pos (show 0 < (m : ℝ) by exact_mod_cast hm)]

theorem exists_finite_ball_cover_of_hausdorff_zero [Nonempty X] (S : Set X) (hcompact : IsCompact S)
    (m : ℕ) (hm : 0 < m) (hS : Measure.hausdorffMeasure (m : ℝ) S = 0)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (c : ℕ → X) (r : ℕ → ℝ),
      (∀ j ∈ s, c j ∈ S ∧ 0 < r j ∧ r j < δ) ∧
      S ⊆ ⋃ j ∈ s, Metric.ball (c j) (r j) ∧
      ∑ j ∈ s, (r j) ^ m < ε := by
  classical
  by_cases hSne : S.Nonempty
  · let K : ℝ := 2 ^ (m - 1)
    have hK : 0 < K := by dsimp [K]; positivity
    let ε' : ℝ := ε / (4 * K)
    have hε' : 0 < ε' := by dsimp [ε']; positivity
    let a : ℝ := min (δ / 4) (min 1 (ε / (8 * K)))
    have ha : 0 < a := by dsimp [a]; positivity
    have haδ : a ≤ δ / 4 := min_le_left _ _
    have ha1 : a ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have haε : a ≤ ε / (8 * K) := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨t, hcover, hdiam, hcost⟩ := exists_diameter_cover_of_hausdorff_zero S m hm hS
      (δ := ENNReal.ofReal (δ / 4)) (ε := ENNReal.ofReal ε')
      (ENNReal.ofReal_pos.mpr (by positivity)) (ENNReal.ofReal_pos.mpr hε')
    have htfin : ∀ j, Metric.ediam (t j) ≠ ⊤ := fun j ↦
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam j)
    let d : ℕ → ℝ := fun j ↦ (Metric.ediam (t j)).toReal
    have hd0 : ∀ j, 0 ≤ d j := fun _ ↦ ENNReal.toReal_nonneg
    have hdδ : ∀ j, d j ≤ δ / 4 := fun j ↦ by
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam j)).trans_eq
        (ENNReal.toReal_ofReal (by positivity))
    let b : ℕ → ℝ := fun j ↦ a * (1 / 2 : ℝ) ^ j
    have hbpos : ∀ j, 0 < b j := fun j ↦ by dsimp [b]; positivity
    have hble : ∀ j, b j ≤ a := fun j ↦ by
      dsimp [b]
      have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hbs : Summable b := (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left a
    have hbtsum : ∑' j, b j = 2 * a := by
      dsimp [b]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    have hc : ∀ j, ∃ x ∈ S, (S ∩ t j).Nonempty → x ∈ t j := by
      intro j
      by_cases hj : (S ∩ t j).Nonempty
      · obtain ⟨x, hx⟩ := hj
        exact ⟨x, hx.1, fun _ ↦ hx.2⟩
      · obtain ⟨x, hx⟩ := hSne
        exact ⟨x, hx, fun hn ↦ (hj hn).elim⟩
    choose c hcS hct using hc
    let r : ℕ → ℝ := fun j ↦ d j + b j
    have hrpos : ∀ j, 0 < r j := fun j ↦ by dsimp [r]; linarith [hd0 j, hbpos j]
    have hrδ : ∀ j, r j < δ := fun j ↦ by
      dsimp [r]
      linarith [hdδ j, (hble j).trans haδ]
    have hballcover : S ⊆ ⋃ j, Metric.ball (c j) (r j) := by
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hx)
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      have hdxc : dist x (c j) ≤ d j :=
        Metric.dist_le_diam_of_mem' (htfin j) hj (hct j ⟨x, hx, hj⟩)
      change dist x (c j) < d j + b j
      linarith [hbpos j]
    obtain ⟨s, hscover⟩ := hcompact.elim_finite_subcover
      (fun j ↦ Metric.ball (c j) (r j)) (fun _ ↦ Metric.isOpen_ball) hballcover
    refine ⟨s, c, r, fun j _ ↦ ⟨hcS j, hrpos j, hrδ j⟩, hscover, ?_⟩
    have hdscost : ∑ j ∈ s, d j ^ m < ε' := by
      have hst := (ENNReal.sum_le_tsum s).trans_lt hcost
      have heq : (∑ j ∈ s, Metric.ediam (t j) ^ m).toReal = ∑ j ∈ s, d j ^ m := by
        rw [ENNReal.toReal_sum (fun j hj ↦ ENNReal.pow_ne_top (htfin j))]
        simp only [ENNReal.toReal_pow, d]
      have hh := ENNReal.toReal_lt_toReal
        (ne_top_of_lt hst) ENNReal.ofReal_ne_top |>.mpr hst
      simpa only [heq, ENNReal.toReal_ofReal hε'.le] using hh
    have hbspow : ∑ j ∈ s, b j ^ m ≤ 2 * a := by
      calc
        _ ≤ ∑ j ∈ s, b j := by
          apply Finset.sum_le_sum
          intro j hj
          exact pow_le_of_le_one (hbpos j).le ((hble j).trans ha1) hm.ne'
        _ ≤ ∑' j, b j := hbs.sum_le_tsum s (fun _ _ ↦ (hbpos _).le)
        _ = _ := hbtsum
    calc
      _ ≤ ∑ j ∈ s, K * (d j ^ m + b j ^ m) := by
        apply Finset.sum_le_sum
        intro j hj
        exact add_pow_le (hd0 j) (hbpos j).le m
      _ = K * ((∑ j ∈ s, d j ^ m) + ∑ j ∈ s, b j ^ m) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ < K * (ε' + 2 * a) :=
        mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le hdscost hbspow) hK
      _ < ε := by
        dsimp [ε']
        have haux : a * (8 * K) ≤ ε := (le_div_iff₀ (by positivity)).mp haε
        field_simp
        nlinarith
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    exact ⟨∅, fun _ ↦ Classical.choice (inferInstance : Nonempty X), fun _ ↦ 0,
      by simp, by simp [hSe], by simpa using hε⟩

end Covers
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI
section CapacityConstruction
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem innerCapacityBump_energy_le_radius_power (μ : Measure V)
    {C A : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hbound : ∀ (c : V) (r : ℝ), 0 < r → ∀ x : V,
      ‖gradient (ballCapacityCutoff V c r) x‖ ≤ C / r)
    (m : ℕ) (c : V) (r : ℝ) (hr : 0 < r)
    (hgrowth : μ (Metric.ball c (2 * r)) ≤ ENNReal.ofReal (A * (2 * r) ^ (m + 2))) :
    smoothDirichletEnergy μ (innerCapacityBump c r) ≤
      ENNReal.ofReal (C ^ 2 * A * 2 ^ (m + 2) * r ^ m) := by
  calc
    _ ≤ ENNReal.ofReal ((C / r) ^ 2) * μ (Metric.ball c (2 * r)) :=
      innerCapacityBump_energy_le μ hC hbound c r hr
    _ ≤ ENNReal.ofReal ((C / r) ^ 2) * ENNReal.ofReal (A * (2 * r) ^ (m + 2)) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      rw [mul_pow, pow_add r m 2]
      field_simp

theorem exists_smooth_capacity_cutoff (μ : Measure V) (S : Set V)
    (hcompact : IsCompact S) (m : ℕ) (hm : 0 < m)
    (hS : Measure.hausdorffMeasure (m : ℝ) S = 0)
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ S, ∀ r : ℝ, 0 < r → r < r₀ →
      μ (Metric.ball c r) ≤ ENNReal.ofReal (A * r ^ (m + 2)))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ χ : V → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∃ U : Set V, IsOpen U ∧ S ⊆ U ∧ ∀ x ∈ U, χ x = 0) ∧
      (∀ x, (∀ c ∈ S, 2 * δ ≤ dist x c) → χ x = 1) ∧
      smoothDirichletEnergy μ χ < ENNReal.ofReal ε := by
  classical
  obtain ⟨C, hC, hCbound⟩ := exists_ballCapacityCutoff_gradient_bound V
  obtain ⟨B, hB, hBbound⟩ := exists_smoothCutoffAggregate_gradient_bound (ι := ℕ) (V := V)
  let D : ℝ := C ^ 2 * A * 2 ^ (m + 2)
  have hD : 0 < D := by dsimp [D]; positivity
  let E : ℝ := B * D
  have hE : 0 < E := mul_pos hB hD
  let δ' : ℝ := min δ (r₀ / 4)
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  obtain ⟨s, c, r, hcsr, hcover, hcost⟩ :=
    exists_finite_ball_cover_of_hausdorff_zero S hcompact m hm hS
      (δ := δ') (ε := ε / E) hδ' (by positivity)
  let b : ℕ → V → ℝ := fun j ↦ innerCapacityBump (c j) (r j)
  have hb : ∀ j, ContDiff ℝ ∞ (b j) := fun j ↦ innerCapacityBump_contDiff (c j) (r j)
  have hb₁ : ∀ j ∈ s, ContDiff ℝ 1 (b j) := fun j _ ↦ (hb j).of_le (by norm_num)
  let χ : V → ℝ := smoothCutoffAggregate s b
  refine ⟨χ, smoothCutoffAggregate_contDiff s b (fun j _ ↦ hb j),
    smoothCutoffAggregate_mem_Icc s b, ?_, ?_, ?_⟩
  · refine ⟨⋃ j ∈ s, Metric.ball (c j) (r j), isOpen_iUnion (fun _ ↦ isOpen_iUnion
        (fun _ ↦ Metric.isOpen_ball)), hcover, ?_⟩
    intro x hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxj
    apply smoothCutoffAggregate_zero_of_one hj
    exact innerCapacityBump_one (hcsr j hj).2.1 (Metric.mem_ball.mp hxj).le
  · intro x hx
    apply smoothCutoffAggregate_one
    intro j hj
    apply innerCapacityBump_zero (hcsr j hj).2.1
    have hrδ := (hcsr j hj).2.2.trans_le (min_le_left δ (r₀ / 4))
    linarith [hx (c j) (hcsr j hj).1]
  · have hej : ∀ j ∈ s, smoothDirichletEnergy μ (b j) ≤ ENNReal.ofReal (D * (r j) ^ m) := by
      intro j hj
      apply innerCapacityBump_energy_le_radius_power μ hC hA hCbound m (c j) (r j) (hcsr j hj).2.1
      apply hgrowth (c j) (hcsr j hj).1 (2 * r j)
        (mul_pos (by norm_num) (hcsr j hj).2.1)
      have hrr := (hcsr j hj).2.2.trans_le (min_le_right δ (r₀ / 4))
      linarith
    have hagg := smoothCutoffAggregate_energy_le μ hB.le s b hb₁ (hBbound s b hb₁)
    have hsum0 : 0 ≤ ∑ j ∈ s, r j ^ m :=
      Finset.sum_nonneg (fun j hj ↦ pow_nonneg (hcsr j hj).2.1.le _)
    calc
      _ ≤ ENNReal.ofReal B * ∑ j ∈ s, smoothDirichletEnergy μ (b j) := hagg
      _ ≤ ENNReal.ofReal B * ∑ j ∈ s, ENNReal.ofReal (D * (r j) ^ m) := by
        gcongr with j hj
        exact hej j hj
      _ = ENNReal.ofReal (E * ∑ j ∈ s, r j ^ m) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (s := s) (f := fun j ↦ D * r j ^ m)
          (fun j hj ↦ mul_nonneg hD.le (pow_nonneg (hcsr j hj).2.1.le _)),
          ← ENNReal.ofReal_mul hB.le, ← Finset.mul_sum]
        congr 1
        dsimp [E, D]
        ring
      _ < ENNReal.ofReal ε := by
        apply ENNReal.ofReal_lt_ofReal_iff hε |>.mpr
        have h := (lt_div_iff₀ hE).mp hcost
        simpa only [mul_comm] using h

theorem exists_smooth_capacity_sequence (μ : Measure V) (S : Set V)
    (hcompact : IsCompact S) (m : ℕ) (hm : 0 < m)
    (hS : Measure.hausdorffMeasure (m : ℝ) S = 0)
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ S, ∀ r : ℝ, 0 < r → r < r₀ →
      μ (Metric.ball c r) ≤ ENNReal.ofReal (A * r ^ (m + 2))) :
    ∃ χ : ℕ → V → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ (∀ x, χ i x ∈ Icc (0 : ℝ) 1) ∧
        ∃ U : Set V, IsOpen U ∧ S ⊆ U ∧ ∀ x ∈ U, χ i x = 0) ∧
      (∀ x ∉ S, ∀ᶠ i in atTop, χ i x = 1) ∧
      Tendsto (fun i ↦ smoothDirichletEnergy μ (χ i)) atTop (𝓝 0) := by
  classical
  let a : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ) + 1)
  have ha : ∀ i, 0 < a i := fun i ↦ by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hχ : ∀ i : ℕ, ∃ χ : V → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∃ U : Set V, IsOpen U ∧ S ⊆ U ∧ ∀ x ∈ U, χ x = 0) ∧
      (∀ x, (∀ c ∈ S, 2 * a i ≤ dist x c) → χ x = 1) ∧
      smoothDirichletEnergy μ χ < ENNReal.ofReal (a i) := fun i ↦
    exists_smooth_capacity_cutoff μ S hcompact m hm hS hA hr₀ hgrowth (ha i) (ha i)
  choose χ hχsmooth hχbound hχzero hχone hχenergy using hχ
  refine ⟨χ, fun i ↦ ⟨hχsmooth i, hχbound i, hχzero i⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl x hx
    have hfar : ∀ c ∈ S, d ≤ dist x c := by
      intro c hc
      by_contra hcclose
      have hmem : c ∈ Metric.ball x d := by
        simpa only [Metric.mem_ball, dist_comm] using lt_of_not_ge hcclose
      exact hball hmem hc
    have h2a : Tendsto (fun i ↦ 2 * a i) atTop (𝓝 0) := by
      simpa only [mul_zero] using ha0.const_mul 2
    filter_upwards [h2a.eventually (gt_mem_nhds hd)] with i hi
    exact hχone i x (fun c hc ↦ hi.le.trans (hfar c hc))
  · have hea : Tendsto (fun i ↦ ENNReal.ofReal (a i)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ha0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hea
      (fun _ ↦ zero_le) (fun i ↦ (hχenergy i).le)

omit [BorelSpace V] in
theorem projected_smooth_energy_le (μ : Measure V) (P : V → Submodule ℝ V) (f : V → ℝ) :
    (∫⁻ x, ENNReal.ofReal
      (‖((P x).orthogonalProjectionOnto (gradient f x) : V)‖ ^ 2) ∂μ) ≤
        smoothDirichletEnergy μ f := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hp : ‖((P x).orthogonalProjectionOnto (gradient f x) : V)‖ ≤ ‖gradient f x‖ := by
    calc
      _ ≤ ‖(P x).orthogonalProjectionOnto‖ * ‖gradient f x‖ :=
        (P x).orthogonalProjectionOnto.le_opNorm _
      _ ≤ 1 * ‖gradient f x‖ := mul_le_mul_of_nonneg_right
        (P x).orthogonalProjectionOnto_norm_le (norm_nonneg _)
      _ = _ := one_mul _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp

omit [BorelSpace V] in
theorem projected_smooth_energy_tendsto_zero (μ : Measure V) (P : V → Submodule ℝ V)
    (χ : ℕ → V → ℝ)
    (hχ : Tendsto (fun i ↦ smoothDirichletEnergy μ (χ i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x, ENNReal.ofReal
      (‖((P x).orthogonalProjectionOnto (gradient (χ i) x) : V)‖ ^ 2) ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hχ
    (fun _ ↦ zero_le) (fun i ↦ projected_smooth_energy_le μ P (χ i))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem hausdorff_capacity_dimension {n : ℕ} (hn : 8 ≤ n) (S : Set V)
    (hdim : dimH S ≤ (n - 8 : ℕ)) :
    0 < n - 3 ∧ Measure.hausdorffMeasure ((n - 3 : ℕ) : ℝ) S = 0 := by
  refine ⟨by omega, ?_⟩
  have hlt : dimH S < (n - 3 : ℕ) := hdim.trans_lt (by
    exact_mod_cast (show n - 8 < n - 3 by omega))
  simpa only [NNReal.coe_natCast] using hausdorffMeasure_of_dimH_lt (d := (n - 3 : ℕ)) hlt

end CapacityConstruction
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem exists_memLp_capacity_sequence {n : ℕ} (hn : 8 ≤ n)
    (S V Z : Set (Space n)) (hZc : IsCompact Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) ((surfaceMeasure S).restrict V))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z, ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict V (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ (∀ x, χ i x ∈ Icc (0 : ℝ) 1) ∧
        (∃ U : Set (Space n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ i x = 0) ∧
        MemLp (surfaceGradient S (χ i)) 2 ((surfaceMeasure S).restrict V)) ∧
      (∀ᵐ x ∂(surfaceMeasure S).restrict V,
        Tendsto (fun i ↦ χ i x) atTop (𝓝 1)) ∧
      Tendsto (fun i ↦ vectorEnergy ((surfaceMeasure S).restrict V)
        (surfaceGradient S (χ i))) atTop (𝓝 0) := by
  obtain ⟨hm, hZd'⟩ := hausdorff_capacity_dimension hn Z hZd
  have hpow : n - 3 + 2 = n - 1 := by omega
  obtain ⟨χ, hχ, hχone, hχenergy⟩ := exists_smooth_capacity_sequence
    ((surfaceMeasure S).restrict V) Z hZc (n - 3) hm hZd' hA hr₀
    (by simpa only [hpow] using hgrowth)
  have hE : Tendsto (fun i ↦ vectorEnergy ((surfaceMeasure S).restrict V)
      (surfaceGradient S (χ i))) atTop (𝓝 0) := by
    exact projected_smooth_energy_tendsto_zero ((surfaceMeasure S).restrict V)
      (tangentPlane S) χ hχenergy
  have hfinite : ∀ᶠ i in atTop, vectorEnergy ((surfaceMeasure S).restrict V)
      (surfaceGradient S (χ i)) < 1 :=
    hE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinite
  have hshift : Tendsto (fun i : ℕ ↦ i + N) atTop atTop := tendsto_add_atTop_nat N
  refine ⟨fun i ↦ χ (i + N), ?_, ?_, hE.comp hshift⟩
  · intro i
    refine ⟨(hχ (i + N)).1, (hχ (i + N)).2.1, (hχ (i + N)).2.2, ?_⟩
    apply (memLp_two_iff_vectorEnergy (hgrad _ (hχ (i + N)).1)).mpr
    exact (hN (i + N) (Nat.le_add_left N i)).trans (by norm_num)
  · have hnull : (surfaceMeasure S).restrict V Z = 0 :=
      le_antisymm ((Measure.restrict_apply_le V Z).trans_eq
        (surfaceMeasure_zero_of_singular_dim hn S Z hZd)) zero_le
    have hae : ∀ᵐ x ∂(surfaceMeasure S).restrict V, x ∉ Z := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
    filter_upwards [hae] with x hx
    exact ((tendsto_congr' (hχone x hx)).2 tendsto_const_nhds).comp hshift

theorem hausdorff_trace_mem_sobolevGraph {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (V : Set (Space n))
    (hZc : IsCompact Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S h G x)
    (hh : MemLp h 2 ((surfaceMeasure S).restrict V))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict V))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(surfaceMeasure S).restrict V, ‖h x‖ ≤ M)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) ((surfaceMeasure S).restrict V))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z, ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict V (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V) := by
  obtain ⟨χ, hχ, hχlim, hχE⟩ := exists_memLp_capacity_sequence hn S V Z hZc hZd
    hgrad hA hr₀ hgrowth
  exact capacity_trace_mem_sobolevGraph hS V hreg hh hG hM hbound χ
    (fun i ↦ (hχ i).1) (fun i ↦ (hχ i).2.2.1)
    (fun i ↦ ae_of_all _ (hχ i).2.1) hχlim (fun i ↦ (hχ i).2.2.2) hχE

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem tangentPlane_eq_ker_of_local_level {n : ℕ} {S : Set (Space n)}
    {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 1 f x) (hdf : fderiv ℝ f x ≠ 0)
    (hlevel : ∀ᶠ y in 𝓝 x, y ∈ S ↔ f y = f x) :
    tangentPlane S x = (fderiv ℝ f x).ker := by
  have hder := hf.hasStrictFDerivAt (by norm_num)
  have hrange : (fderiv ℝ f x).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    have hv : ∃ v, fderiv ℝ f x v ≠ 0 := by
      by_contra! hv
      apply hdf
      ext v
      exact hv v
    obtain ⟨v, hv⟩ := hv
    intro a
    refine ⟨(a / fderiv ℝ f x v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ a hv
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨γ, hγx, hγd, hγS⟩
    have ht : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := hγx ▸ hγd.continuousAt
    have heq : (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ f x := by
      filter_upwards [ht.eventually hlevel, hγS] with t he ht
      exact he.mp ht
    have hd : HasDerivAt (f ∘ γ) (fderiv ℝ f x v) 0 := by
      exact (show HasFDerivAt f (fderiv ℝ f x) (γ 0) by
        simpa only [hγx] using hder.hasFDerivAt).comp_hasDerivAt 0 hγd
    exact hd.unique ((hasDerivAt_const 0 (f x)).congr_of_eventuallyEq heq)
  · intro v hv
    let v' : (fderiv ℝ f x).ker := ⟨v, hv⟩
    let γ : ℝ → Space n := fun t ↦ hder.implicitFunction f (fderiv ℝ f x)
      hrange (f x) (t • v')
    have hγx : γ 0 = x := by simp [γ]
    have hline : HasDerivAt (fun t : ℝ ↦ t • v') v' 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v'
    have hγd : HasDerivAt γ v 0 := by
      have hd' : HasFDerivAt (hder.implicitFunction f (fderiv ℝ f x)
          hrange (f x)) (fderiv ℝ f x).ker.subtypeL ((0 : ℝ) • v') := by
        simpa only [zero_smul] using (hder.to_implicitFunction hrange).hasFDerivAt
      exact hd'.comp_hasDerivAt 0 hline
    have ht : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := hγx ▸ hγd.continuousAt
    have hparam : Tendsto (fun t : ℝ ↦ (f x, t • v')) (𝓝 0)
        (𝓝 (f x, 0)) := by
      apply tendsto_const_nhds.prodMk_nhds
      simpa only [ContinuousAt, zero_smul] using hline.continuousAt
    have hγS : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S := by
      filter_upwards [ht.eventually hlevel,
        hparam.eventually (hder.map_implicitFunction_eq hrange)] with t he hval
      exact he.mpr hval
    exact Submodule.subset_span ⟨γ, hγx, hγd, hγS⟩

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem surfaceGradient_eq_level_formula {n : ℕ} {S : Set (Space n)}
    {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 1 f x) (hdf : fderiv ℝ f x ≠ 0)
    (hlevel : ∀ᶠ y in 𝓝 x, y ∈ S ↔ f y = f x) :
    surfaceGradient S g x = gradient g x -
      (inner ℝ (gradient f x) (gradient g x) / ‖gradient f x‖ ^ 2) • gradient f x := by
  have hgn : gradient f x ≠ 0 := by
    intro he
    apply hdf
    rw [← toDual_gradient, he, map_zero]
  have hnorm : ‖gradient f x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hgn)
  have htan := tangentPlane_eq_ker_of_local_level hf hdf hlevel
  change (tangentPlane S x).starProjection (gradient g x) = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [htan]
    change fderiv ℝ f x (_ - _) = 0
    rw [map_sub, map_smul]
    rw [← inner_gradient_left, ← inner_gradient_left, real_inner_self_eq_norm_sq]
    simp only [smul_eq_mul]
    rw [div_mul_cancel₀ _ hnorm, sub_self]
  · intro w hw
    rw [htan] at hw
    rw [sub_sub_cancel, real_inner_smul_left, inner_gradient_left]
    change fderiv ℝ f x w = 0 at hw
    simp only [inner_gradient_left, hw, mul_zero]

theorem continuousAt_gradient_of_contDiffAt {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 1 f x) : ContinuousAt (gradient f) x := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.continuousAt.comp
    (hf.continuousAt_fderiv (by norm_num))

end RPI.Boundary

end

end OAI
