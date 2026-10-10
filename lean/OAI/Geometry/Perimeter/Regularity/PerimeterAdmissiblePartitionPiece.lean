import OAI.Geometry.Perimeter.Regularity.IndicatorConvolutionVariationLocalLe

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open scoped Manifold

theorem perimeterAdmissible_partition_piece {n : ℕ} {ι : Type*}
    {E U : Set (Euc n)} {V : Euc n → Euc n}
    (hV : PerimeterAdmissible U V)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Euc n) (Euc n) E)
    (W : ι → Set (Euc n)) (hρ : ρ.IsSubordinate W) (i : ι) :
    PerimeterAdmissible (W i) (fun x ↦ ρ i x • V x) := by
  refine ⟨(ρ i).contMDiff.contDiff.smul hV.1,
    (hV.2.1.smul_left (f := fun x ↦ ρ i x)), ?_, ?_⟩
  · exact (tsupport_smul_subset_left _ _).trans (hρ i)
  · intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i x)]
    calc
      ρ i x * ‖V x‖ ≤ 1 * ‖V x‖ :=
        mul_le_mul_of_nonneg_right (ρ.le_one i x) (norm_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using hV.2.2.2 x

theorem divergence_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (V : ι → Euc n → Euc n) (hV : ∀ i ∈ s, Differentiable ℝ (V i)) :
    divergence (∑ i ∈ s, V i) = ∑ i ∈ s, divergence (V i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext x
    simp [divergence]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      divergence_add (hV i (by simp))
        (Differentiable.sum (fun j hj ↦ hV j (by simp [hj]))),
      ih (fun j hj ↦ hV j (by simp [hj]))]

theorem perimeter_iUnion_open_le {n : ℕ} (E : Set (Euc n))
    {ι : Type*} (U : ι → Set (Euc n)) (hU : ∀ i, IsOpen (U i)) :
    perimeter E (⋃ i, U i) ≤ ∑' i, perimeter E (U i) := by
  classical
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  obtain ⟨s, hs⟩ := hV.2.1.elim_finite_subcover U hU hV.2.2.1
  have hs' : tsupport V ⊆ ⋃ i : s, U i := by
    simpa only [iUnion_subtype, iUnion_coe_set] using hs
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Euc n) (isClosed_tsupport V) (fun i : s ↦ U i) (fun i ↦ hU i) hs'
  let W : s → Euc n → Euc n := fun i x ↦ ρ i x • V x
  have hW : ∀ i : s, PerimeterAdmissible (U i) (W i) :=
    fun i ↦ perimeterAdmissible_partition_piece hV ρ _ hρ i
  have hsum : V = ∑ i : s, W i := by
    funext x
    simp only [Finset.sum_apply, W, ← Finset.sum_smul]
    by_cases hx : x ∈ tsupport V
    · have ht := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at ht
      rw [ht, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  calc
    ENNReal.ofReal (∫ x in E, divergence V x) =
        ENNReal.ofReal (∑ i : s, ∫ x in E, divergence (W i) x) := by
      rw [hsum, divergence_finset_sum _ W (fun i _ ↦ (hW i).1.differentiable (by simp))]
      simp only [Finset.sum_apply]
      rw [integral_finsetSum _ (fun i _ ↦
        (integrable_divergence (hW i).1 (hW i).2.1).integrableOn)]
    _ ≤ ∑ i : s, ENNReal.ofReal (∫ x in E, divergence (W i) x) :=
      by
      have h (m : Finset s) :
          ENNReal.ofReal (∑ i ∈ m, ∫ x in E, divergence (W i) x) ≤
          ∑ i ∈ m, ENNReal.ofReal (∫ x in E, divergence (W i) x) := by
        induction m using Finset.induction_on with
        | empty => simp
        | @insert i m hi ih =>
          simp only [Finset.sum_insert hi]
          exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)
      exact h Finset.univ
    _ ≤ ∑ i : s, perimeter E (U i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [perimeter_eq_iSup_tests]
      exact le_iSup_of_le (W i) (le_iSup_of_le (hW i) le_rfl)
    _ ≤ ∑' i, perimeter E (U i) := by
      exact (Finset.sum_coe_sort s (fun i ↦ perimeter E (U i))).le.trans
        (ENNReal.sum_le_tsum s)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

@[simp] theorem raw_perimeter_empty_region {n : ℕ} (E : Set (Euc n)) :
    perimeter E ∅ = 0 := by
  apply le_antisymm _ zero_le
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  have hzero : V = 0 := by
    funext x
    exact image_eq_zero_of_notMem_tsupport (fun hx ↦ hV.2.2.1 hx)
  simp [hzero, divergence]

noncomputable def openPerimeterCost {n : ℕ} (E U : Set (Euc n)) : ℝ≥0∞ :=
  by classical exact if IsOpen U then perimeter E U else ⊤

@[simp] theorem openPerimeterCost_empty {n : ℕ} (E : Set (Euc n)) :
    openPerimeterCost E ∅ = 0 := by
  simp [openPerimeterCost]

noncomputable def perimeterOuterMeasure {n : ℕ} (E : Set (Euc n)) :
    OuterMeasure (Euc n) :=
  OuterMeasure.ofFunction (openPerimeterCost E) (openPerimeterCost_empty E)

theorem perimeterOuterMeasure_le_open {n : ℕ} (E : Set (Euc n))
    {A U : Set (Euc n)} (hU : IsOpen U) (hAU : A ⊆ U) :
    perimeterOuterMeasure E A ≤ perimeter E U := by
  exact ((perimeterOuterMeasure E).mono hAU).trans
    ((OuterMeasure.ofFunction_le _).trans_eq (by simp [openPerimeterCost, hU]))

theorem perimeterOuterMeasure_eq_iInf_open {n : ℕ} (E A : Set (Euc n)) :
    perimeterOuterMeasure E A =
      ⨅ (U : Set (Euc n)) (_ : IsOpen U) (_ : A ⊆ U), perimeter E U := by
  apply le_antisymm
  · exact le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hAU ↦
      perimeterOuterMeasure_le_open E hU hAU
  · unfold perimeterOuterMeasure
    rw [OuterMeasure.ofFunction_eq_iInf_mem (openPerimeterCost E)
      (openPerimeterCost_empty E) (P := IsOpen)
      (fun U hU ↦ by simp [openPerimeterCost, hU])]
    refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hAU ↦ ?_
    calc
      _ ≤ perimeter E (⋃ i, U i) :=
        iInf_le_of_le (⋃ i, U i) (iInf_le_of_le (isOpen_iUnion hU)
          (iInf_le_of_le hAU le_rfl))
      _ ≤ ∑' i, perimeter E (U i) := perimeter_iUnion_open_le E U hU
      _ = ∑' i, openPerimeterCost E (U i) := by
        congr 1
        funext i
        simp [openPerimeterCost, hU i]

theorem perimeterOuterMeasure_open {n : ℕ} (E : Set (Euc n))
    {U : Set (Euc n)} (hU : IsOpen U) :
    perimeterOuterMeasure E U = perimeter E U := by
  apply le_antisymm (perimeterOuterMeasure_le_open E hU Subset.rfl)
  rw [perimeterOuterMeasure_eq_iInf_open]
  exact le_iInf fun W ↦ le_iInf fun _ ↦ le_iInf fun hUW ↦ raw_perimeter_mono_region E hUW

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem separated_open_neighborhoods {n : ℕ} {A B : Set (Euc n)}
    (hsep : Metric.AreSeparated A B) :
    ∃ U V : Set (Euc n), IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V := by
  obtain ⟨r, hr, hsep⟩ := hsep
  have hc : IsClosed {p : Euc n × Euc n | r ≤ edist p.1 p.2} :=
    isClosed_le continuous_const continuous_edist
  have hcl : closure (A ×ˢ B) ⊆ {p : Euc n × Euc n | r ≤ edist p.1 p.2} :=
    hc.closure_subset_iff.mpr (fun p hp ↦ hsep p.1 hp.1 p.2 hp.2)
  rw [closure_prod_eq] at hcl
  have hd : Disjoint (closure A) (closure B) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hr (le_antisymm (by simpa using hcl (show (x, x) ∈ closure A ×ˢ closure B from ⟨hx, hy⟩)) zero_le)
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    normal_separation isClosed_closure isClosed_closure hd
  exact ⟨U, V, hU, hV, subset_closure.trans hAU, subset_closure.trans hBV, hUV⟩

theorem perimeterOuterMeasure_isMetric {n : ℕ} (E : Set (Euc n)) :
    (perimeterOuterMeasure E).IsMetric := by
  intro A B hsep
  apply le_antisymm (measure_union_le (μ := perimeterOuterMeasure E) A B)
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := separated_open_neighborhoods hsep
  rw [perimeterOuterMeasure_eq_iInf_open E (A ∪ B)]
  refine le_iInf fun O ↦ le_iInf fun hO ↦ le_iInf fun hABO ↦ ?_
  calc
    _ ≤ perimeter E (O ∩ U) + perimeter E (O ∩ V) := by
      apply add_le_add
      · exact perimeterOuterMeasure_le_open E (hO.inter hU)
          (fun x hx ↦ ⟨hABO (Or.inl hx), hAU hx⟩)
      · exact perimeterOuterMeasure_le_open E (hO.inter hV)
          (fun x hx ↦ ⟨hABO (Or.inr hx), hBV hx⟩)
    _ ≤ perimeter E O := perimeter_disjoint_superadditive E
      inter_subset_left inter_subset_left (hUV.mono inter_subset_right inter_subset_right)

noncomputable def perimeterMeasure {n : ℕ} (E : Set (Euc n)) : Measure (Euc n) :=
  (perimeterOuterMeasure E).toMeasure (perimeterOuterMeasure_isMetric E).le_caratheodory

@[simp] theorem perimeterMeasure_open {n : ℕ} (E : Set (Euc n))
    {U : Set (Euc n)} (hU : IsOpen U) : perimeterMeasure E U = perimeter E U := by
  rw [perimeterMeasure, toMeasure_apply _ _ hU.measurableSet,
    perimeterOuterMeasure_open E hU]

theorem perimeterMeasure_support {n : ℕ} (E : Set (Euc n)) :
    (perimeterMeasure E).support = perimeterSupport E := by
  ext x
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro hx r hr
    rw [← perimeterMeasure_open E Metric.isOpen_ball]
    exact hx _ (Metric.ball_mem_nhds x hr)
  · intro hx U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
    have hm : 0 < perimeterMeasure E (Metric.ball x r) := by
      rw [perimeterMeasure_open E Metric.isOpen_ball]
      exact hx r hr
    exact hm.trans_le ((perimeterMeasure E).mono hrU)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem perimeterMeasure_locallyFinite {n : ℕ} (E : Set (Euc n))
    (hfin : ∀ x (r : ℝ), 0 < r → perimeter E (Metric.ball x r) < ⊤) :
    IsLocallyFiniteMeasure (perimeterMeasure E) := by
  constructor
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  rw [perimeterMeasure_open E Metric.isOpen_ball]
  exact hfin x 1 zero_lt_one

theorem perimeterMeasure_finiteOnCompacts {n : ℕ} (E : Set (Euc n))
    (hfin : ∀ x (r : ℝ), 0 < r → perimeter E (Metric.ball x r) < ⊤) :
    IsFiniteMeasureOnCompacts (perimeterMeasure E) := by
  let := perimeterMeasure_locallyFinite E hfin
  infer_instance

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem measure_le_hausdorff_of_ball_growth {n k : ℕ} (μ : Measure (Euc n))
    {C : ℝ} (hC : 0 < C)
    (hg : ∀ x (r : ℝ), 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ k)) :
    μ ≤ ENNReal.ofReal C • Measure.hausdorffMeasure (k : ℝ) := by
  have hbound : ∀ s : Set (Euc n), Metric.ediam s ≤ 1 →
      μ s ≤ ENNReal.ofReal C * Metric.ediam s ^ k := by
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hst : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top (by simp) hs
    have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (C * (Metric.diam s + r) ^ k))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (C * Metric.diam s ^ k))) := by
      have hc : Continuous (fun r : ℝ ↦ ENNReal.ofReal (C * (Metric.diam s + r) ^ k)) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul
          ((continuous_const.add continuous_id).pow k))
      simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh : μ s ≤ ENNReal.ofReal (C * Metric.diam s ^ k) := by
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hsub : s ⊆ Metric.ball x (Metric.diam s + r) := by
        intro y hy
        exact (Metric.dist_le_diam_of_mem' hst hy hx).trans_lt (lt_add_of_pos_right _ hr)
      exact (measure_mono hsub).trans (hg x _ (add_pos_of_nonneg_of_pos Metric.diam_nonneg hr))
    rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_pow Metric.diam_nonneg] at hh
    simpa only [Metric.diam, ENNReal.ofReal_toReal hst] using hh
  have hm : (ENNReal.ofReal C)⁻¹ • μ ≤ Measure.hausdorffMeasure (k : ℝ) := by
    apply Measure.le_hausdorffMeasure _ _ 1 zero_lt_one
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
    calc
      _ ≤ (ENNReal.ofReal C)⁻¹ * (ENNReal.ofReal C * Metric.ediam s ^ k) :=
        mul_le_mul le_rfl (hbound s hs) zero_le zero_le
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel
        (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top, one_mul]
  calc
    μ = ENNReal.ofReal C • ((ENNReal.ofReal C)⁻¹ • μ) := by
      rw [smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hC)
        ENNReal.ofReal_ne_top, one_smul]
    _ ≤ ENNReal.ofReal C • Measure.hausdorffMeasure (k : ℝ) := by
      apply Measure.le_iff.mpr
      intro s hs
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul le_rfl (Measure.le_iff.mp hm s hs) zero_le zero_le

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_perimeter_vitali_cover_open {n : ℕ} (E S U : Set (Euc n))
    (hU : IsOpen U) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdensity : ∀ x ∈ S, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (u : Set (Euc n)) (r : Euc n → ℝ), u.Countable ∧
      (∀ x ∈ u, 0 < r x ∧ r x ≤ δ) ∧
      (S ∩ U ⊆ ⋃ x ∈ u, Metric.ball x (4 * r x)) ∧
      (∑' x : u, (ENNReal.ofReal (r x)) ^ (n - 1)) ≤
        (ENNReal.ofReal c₀)⁻¹ * perimeter E U := by
  classical
  let t := S ∩ U
  have hchoose : ∀ x ∈ t, ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      Metric.ball x r ⊆ U ∧
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r) := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx.2)
    have hev := hdensity x hx.1
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < min δ ε :=
      (eventually_lt_nhds (lt_min hδ hε)).filter_mono nhdsWithin_le_nhds
    obtain ⟨r, hr, hden, hsm⟩ :=
      ((show ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r from self_mem_nhdsWithin).and
        (hev.and hsmall)).exists
    exact ⟨r, hr, hsm.le.trans (min_le_left _ _),
      (Metric.ball_subset_ball (hsm.le.trans (min_le_right _ _))).trans hεU, hden⟩
  have htotal : ∀ x : Euc n, ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      (x ∈ t → Metric.ball x r ⊆ U ∧
        ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r)) := by
    intro x
    by_cases hx : x ∈ t
    · obtain ⟨r, hr, hrδ, hrU, hden⟩ := hchoose x hx
      exact ⟨r, hr, hrδ, fun _ ↦ ⟨hrU, hden⟩⟩
    · refine ⟨δ / 2, half_pos hδ, (half_lt_self hδ).le, fun h ↦ ?_⟩
      exact (hx h).elim
  choose r hr using htotal
  obtain ⟨u, hut, hud, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball t id r δ
      (fun x hx ↦ (hr x).2.1) 4 (by norm_num)
  have huc : u.Countable := hud.countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ ⟨x, Metric.mem_ball_self (hr x).1⟩)
  refine ⟨u, r, huc, fun x hx ↦ ⟨(hr x).1, (hr x).2.1⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy (Metric.mem_ball_self (hr x).1)⟩⟩
  · have hsum := perimeter_tsum_disjoint_le E
      (fun x : u ↦ Metric.ball (x : Euc n) (r x)) U
      (fun x y h ↦ hud x.property y.property (fun hxy ↦ h (Subtype.ext hxy)))
      (fun x ↦ ((hr x).2.2 (hut x.property)).1)
    have hweigh : ENNReal.ofReal c₀ * ∑' x : u, ENNReal.ofReal (r x) ^ (n - 1) ≤
        perimeter E U := by
      rw [← ENNReal.tsum_mul_left]
      apply le_trans (ENNReal.tsum_le_tsum (fun x : u ↦ ?_)) hsum
      rw [← ENNReal.ofReal_pow (hr x).1.le, ← ENNReal.ofReal_mul hc₀.le]
      exact ((hr x).2.2 (hut x.property)).2
    calc
      _ = (ENNReal.ofReal c₀)⁻¹ *
          (ENNReal.ofReal c₀ * ∑' x : u, ENNReal.ofReal (r x) ^ (n - 1)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc₀)
          ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := mul_le_mul le_rfl hweigh zero_le zero_le

theorem hausdorffMeasure_inter_open_le_perimeter {n : ℕ} (E S U : Set (Euc n))
    (hU : IsOpen U) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdensity : ∀ x ∈ S, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r)) :
    Measure.hausdorffMeasure (n - 1 : ℕ) (S ∩ U) ≤
      (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ * perimeter E U := by
  classical
  let δ : ℕ → ℝ := fun j ↦ 1 / (j + 1)
  have hδ : ∀ j, 0 < δ j := fun j ↦ by dsimp [δ]; positivity
  choose u r hcount hr hcover hsum using fun j ↦
    exists_perimeter_vitali_cover_open E S U hU hc₀ hdensity (hδ j)
  let : ∀ j, Countable (u j) := fun j ↦ (hcount j).to_subtype
  have hediam : ∀ j (x : u j),
      Metric.ediam (Metric.ball (x : Euc n) (4 * r j x)) ≤
        ENNReal.ofReal (8 * r j x) := by
    intro j x
    apply Metric.ediam_le
    intro y hy z hz
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simp only [Metric.mem_ball] at hy hz
    calc dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
      _ ≤ 8 * r j x := by linarith
  have hδlim : Tendsto (fun j ↦ ENNReal.ofReal (8 * δ j)) atTop (𝓝 0) := by
    have hh : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hh.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum ((n - 1 : ℕ) : ℝ)
    (S ∩ U) (fun j ↦ ENNReal.ofReal (8 * δ j)) hδlim
    (fun j (x : u j) ↦ Metric.ball (x : Euc n) (4 * r j x))
    (Filter.Eventually.of_forall (fun j x ↦
      (hediam j x).trans (ENNReal.ofReal_le_ofReal (by
        have h := (hr j x x.property).2; linarith))))
    (Filter.Eventually.of_forall (fun j ↦ by simpa only [iUnion_subtype] using hcover j))
  apply hh.trans
  refine Filter.liminf_le_of_frequently_le ?_ (by isBoundedDefault)
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro j
  calc
    _ ≤ ∑' x : u j, (8 : ℝ≥0∞) ^ (n - 1) *
        ENNReal.ofReal (r j x) ^ (n - 1) := by
      apply ENNReal.tsum_le_tsum
      intro x
      rw [ENNReal.rpow_natCast]
      calc
        _ ≤ (ENNReal.ofReal (8 * r j x)) ^ (n - 1) := pow_le_pow_left' (hediam j x) _
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), mul_pow]; norm_num
    _ = (8 : ℝ≥0∞) ^ (n - 1) * ∑' x : u j, ENNReal.ofReal (r j x) ^ (n - 1) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul le_rfl (hsum j) zero_le zero_le

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem hausdorff_restrict_le_perimeterMeasure {n : ℕ} (E S : Set (Euc n))
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdensity : ∀ x ∈ S, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r)) :
    (Measure.hausdorffMeasure (n - 1 : ℕ)).restrict S ≤
      ((8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹) • perimeterMeasure E := by
  let K : ℝ≥0∞ := 8 ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹
  have hc0 : ENNReal.ofReal c₀ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc₀
  have hK0 : K ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (8 : ℝ≥0∞) ≠ 0))
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  have hKt : K ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top (by norm_num)
    · exact ENNReal.inv_ne_top.mpr hc0
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
  change Measure.hausdorffMeasure (n - 1 : ℕ) (A ∩ S) ≤ K * perimeterMeasure E A
  rw [perimeterMeasure, toMeasure_apply _ _ hA, perimeterOuterMeasure_eq_iInf_open,
    ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun U ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun hU ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun hAU ↦ ?_
  calc
    _ ≤ Measure.hausdorffMeasure (n - 1 : ℕ) (S ∩ U) :=
      (Measure.hausdorffMeasure _).mono (fun x hx ↦ ⟨hx.2, hAU hx.1⟩)
    _ ≤ _ := hausdorffMeasure_inter_open_le_perimeter E S U hU hc₀ hdensity

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem minimizing_perimeter_hausdorff_comparison {n : ℕ} (hn : 1 < n) :
    ∃ C D : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ D ≠ 0 ∧ D ≠ ⊤ ∧
      ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
        perimeterMeasure E ≤ C • ((Measure.hausdorffMeasure (n - 1 : ℕ)).restrict
          (perimeterSupport E)) ∧
        (Measure.hausdorffMeasure (n - 1 : ℕ)).restrict (perimeterSupport E) ≤
          D • perimeterMeasure E := by
  obtain ⟨C, hC, hg⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  obtain ⟨c₀, hc₀, hd⟩ := exists_minimizing_perimeter_lower_density n hn
  let D : ℝ≥0∞ := 8 ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹
  have hD0 : D ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hc₀))
  refine ⟨ENNReal.ofReal C, D, ENNReal.ofReal_ne_zero_iff.mpr hC,
    ENNReal.ofReal_ne_top, hD0, hDt, ?_⟩
  intro E hmin
  constructor
  · have hh := measure_le_hausdorff_of_ball_growth (perimeterMeasure E) (k := n - 1) hC
      (fun x r hr ↦ by rw [perimeterMeasure_open E Metric.isOpen_ball]; exact hg E hmin x r hr)
    have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
      rw [← perimeterMeasure_support]
      exact (perimeterMeasure E).support_mem_ae
    have hres := Measure.restrict_mono_measure hh (perimeterSupport E)
    rwa [Measure.restrict_eq_self_of_ae_mem hs, Measure.restrict_smul] at hres
  · apply hausdorff_restrict_le_perimeterMeasure E (perimeterSupport E) hc₀
    intro x hx
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hd E hmin x hx r hr

theorem minimizing_perimeter_hausdorff_mutuallyAC {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) :
    perimeterMeasure E ≪ (Measure.hausdorffMeasure (n - 1 : ℕ)).restrict (perimeterSupport E) ∧
    (Measure.hausdorffMeasure (n - 1 : ℕ)).restrict (perimeterSupport E) ≪ perimeterMeasure E := by
  obtain ⟨C, D, _, _, _, _, hb⟩ := minimizing_perimeter_hausdorff_comparison hn
  exact ⟨Measure.absolutelyContinuous_of_le_smul (hb E hmin).1,
    Measure.absolutelyContinuous_of_le_smul (hb E hmin).2⟩

end RPISingularHarnack

end

end OAI
