import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridOscillation

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma floor_scaled_close {s t u : ℝ} (hs : 0 ≤ s) (_ht : 0 ≤ t)
    (hu : 4 ≤ u) (hst : |s-t| ≤ u/2) : ⌊s⌋₊ ≤ ⌊t⌋₊+⌊u⌋₊ := by
  have h1 := Nat.floor_le hs
  have h2 := Nat.lt_floor_add_one t
  have h3 := Nat.lt_floor_add_one u
  have hb := (abs_le.mp hst).2
  have he : (⌊s⌋₊:ℝ) ≤ (⌊t⌋₊:ℝ)+(⌊u⌋₊:ℝ) := by linarith
  exact_mod_cast he

lemma scaledPolygon_oscillation_subset {Ω : Type*} (X : ℕ → Ω → ℝ)
    {r n T ε δ : ℝ} (hr : 0 < r) (hn : 2 ≤ n) (hT : 0 ≤ T)
    (_hδ : 0 < δ) (hδn : 4 ≤ δ*n) :
    {ω | scaledPolygon (fun k => X k ω) r n T ∈ ContinuousOscillation (3*ε)
      (δ/(2*(T+1)))} ⊆ GridOscillation X ⌊(T+1)*n⌋₊ ⌊δ*n⌋₊ (ε*r) := by
  intro ω hω
  by_contra hg
  rcases hω with ⟨s,t,hst,hbig⟩
  have hn0 : 0 ≤ n := by linarith
  have hTn : 0 ≤ T*n := mul_nonneg hT hn0
  have hs : 0 ≤ T*n*(s:ℝ) := mul_nonneg hTn s.2.1
  have ht : 0 ≤ T*n*(t:ℝ) := mul_nonneg hTn t.2.1
  have hsle : T*n*(s:ℝ) ≤ T*n := mul_le_of_le_one_right hTn s.2.2
  have htle : T*n*(t:ℝ) ≤ T*n := mul_le_of_le_one_right hTn t.2.2
  have hsP : ⌊T*n*(s:ℝ)⌋₊ < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono hsle)
  have htP : ⌊T*n*(t:ℝ)⌋₊ < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono htle)
  have hP : ⌊T*n⌋₊+1 ≤ ⌊(T+1)*n⌋₊ := by
    apply Nat.le_floor
    have hf := Nat.floor_le hTn
    push_cast
    nlinarith
  have hH : 1 ≤ ⌊δ*n⌋₊ := by apply Nat.le_floor; norm_num; linarith
  have hst' : |(s:ℝ)-(t:ℝ)| ≤ δ/(2*(T+1)) := hst
  have hclose : |T*n*(s:ℝ)-T*n*(t:ℝ)| ≤ (δ*n)/2 := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hTn]
    have h1 := mul_le_mul_of_nonneg_left hst' hTn
    have hden : 0 < 2*(T+1) := by positivity
    have he : T*n*(δ/(2*(T+1))) ≤ δ*n/2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg _hδ.le hn0]
    exact h1.trans he
  have hb := linearPolygon_oscillation_le X hg hH hP hs ht hsP htP
    (floor_scaled_close hs ht hδn hclose)
    (floor_scaled_close ht hs hδn (by simpa [abs_sub_comm] using hclose))
  simp only [scaledPolygon_apply] at hbig
  rw [← sub_div,abs_div,abs_of_pos hr] at hbig
  have hlarge := (lt_div_iff₀ hr).mp hbig
  rw [abs_sub_comm] at hb
  nlinarith

theorem gaussian_continuous_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T ε β : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real {ω | scaledPolygon (fun k => X k ω) (r i)
        (fluctuationScale μ (X 0) (r i)) T ∈ ContinuousOscillation ε δ} ≤ β := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  obtain ⟨δ,hδ,hb⟩ := gaussian_grid_modulus μ X hX hind hident hsym hI hne r hr
    (T := T+1) (ε := ε/3) (by linarith) (by positivity) hβ
  refine ⟨δ/(2*(T+1)),by positivity,?_⟩
  have hδn : Tendsto (fun i => δ*n i) atTop atTop := hn.const_mul_atTop hδ
  filter_upwards [hb,hr.1.eventually (eventually_gt_atTop (0:ℝ)),
    hn.eventually (eventually_ge_atTop (2:ℝ)),hδn.eventually (eventually_ge_atTop (4:ℝ))]
    with i hi hri hni hdni
  have hs := scaledPolygon_oscillation_subset X hri hni hT hδ hdni (ε := ε/3)
  have he : 3*(ε/3)=ε := by ring
  rw [he] at hs
  exact (measureReal_mono hs (measure_ne_top _ _)).trans hi

lemma linearPolygon_abs_le_max (x : ℕ → ℝ) {N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) : |linearPolygon x N t| ≤ partialSumMax x N := by
  let j := ⌊t⌋₊
  have hj : (j:ℝ) ≤ t := Nat.floor_le ht
  have hj1 : t < j+1 := Nat.lt_floor_add_one t
  have h1 := (abs_partialSum_le_max x j).trans (partialSumMax_mono x hN.le)
  have h2 := (abs_partialSum_le_max x (j+1)).trans (partialSumMax_mono x hN)
  rw [linearPolygon_formula x N ht hN]
  have he : realPartialSum x j+(t-j)*x j =
      (1-(t-j))*realPartialSum x j+(t-j)*realPartialSum x (j+1) := by
    rw [realPartialSum_succ]
    ring
  change |realPartialSum x j+(t-j)*x j| ≤ _
  rw [he]
  calc
    _ ≤ |(1-(t-j))*realPartialSum x j|+|(t-j)*realPartialSum x (j+1)| := abs_add_le _ _
    _ = (1-(t-j))*|realPartialSum x j|+(t-j)*|realPartialSum x (j+1)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ 1-(t-j) by linarith),
        abs_of_nonneg (show 0 ≤ t-j by linarith)]
    _ ≤ (1-(t-j))*partialSumMax x N+(t-j)*partialSumMax x N := by gcongr; linarith
    _ = _ := by ring

lemma norm_scaledPolygon_le_max (x : ℕ → ℝ) {r n T : ℝ}
    (hr : 0 < r) (hn : 0 ≤ n) (hT : 0 ≤ T) :
    ‖scaledPolygon x r n T‖ ≤ partialSumMax x (⌊T*n⌋₊+1)/r := by
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  rw [Real.norm_eq_abs,scaledPolygon_apply,abs_div,abs_of_pos hr]
  apply (div_le_div_iff_of_pos_right hr).2
  apply linearPolygon_abs_le_max
  · exact mul_nonneg (mul_nonneg hT hn) t.2.1
  · exact Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right (mul_nonneg hT hn) t.2.2))

lemma gaussian_max_horizon_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ (X 0) r) {α ε β : ℝ}
    (hα : 0 ≤ α) (hε : 0 < ε) (hβ : 0 < β)
    (H : ℕ → ℕ) (hH : ∀ᶠ i in atTop, (H i : ℝ) ≤ α*fluctuationScale μ (X 0) (r i)) :
    ∀ᶠ i in atTop, μ.real {ω | ε*r i < partialSumMax (fun k => X k ω) (H i)} ≤
      (32*α+96*α^2)/ε^4+β := by
  have he := (hr.2 1 zero_lt_one).const_mul α
  have hb := (tendsto_order.mp he).2 β (by simpa using hβ)
  filter_upwards [hb,hH,hr.1.eventually (eventually_gt_atTop (0:ℝ))] with i hi hHi hri
  have h := measureReal_max_scaled_fourth_le μ X hX hind hident hsym hne hri
    (η := 1) zero_le_one le_rfl hε hα (H i) 0 hHi
  simp only [Nat.zero_add,one_mul,one_pow,mul_one] at h hi
  linarith

lemma gaussian_continuous_norm_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T β : ℝ} (hT : 0 ≤ T) (hβ : 0 < β) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ i in atTop,
      μ.real {ω | R < ‖scaledPolygon (fun k => X k ω) (r i)
        (fluctuationScale μ (X 0) (r i)) T‖} ≤ β := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  let C := 32*(T+1)+96*(T+1)^2
  have hC : 0 < C := by dsimp [C]; positivity
  let R := max 1 (2*C/β)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hRβ : 2*C ≤ R*β := (div_le_iff₀ hβ).mp (le_max_right _ _)
  have hR4 : R ≤ R^4 := by nlinarith [sq_nonneg (R-1),sq_nonneg (R^2-1)]
  have hsmall : C/R^4 ≤ β/2 := by
    rw [div_le_iff₀ (pow_pos hR 4)]
    nlinarith
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hH : ∀ᶠ i in atTop, (⌊T*n i⌋₊+1 : ℝ) ≤ (T+1)*n i := by
    filter_upwards [hn.eventually (eventually_ge_atTop (1:ℝ))] with i hi
    have hf := Nat.floor_le (mul_nonneg hT (by linarith : 0 ≤ n i))
    nlinarith
  have hH' : ∀ᶠ i in atTop, ((⌊T*n i⌋₊+1:ℕ):ℝ) ≤ (T+1)*n i := by simpa using hH
  have hb := gaussian_max_horizon_eventually μ X hX hind hident hsym hne r hr
    (by linarith : 0 ≤ T+1) hR (by linarith : 0 < β/2) (fun i => ⌊T*n i⌋₊+1) hH'
  refine ⟨R,hR,?_⟩
  filter_upwards [hb,hn.eventually (eventually_ge_atTop (0:ℝ)),
    hr.1.eventually (eventually_gt_atTop (0:ℝ))] with i hi hni hri
  have hs : {ω | R < ‖scaledPolygon (fun k => X k ω) (r i) (n i) T‖} ⊆
      {ω | R*r i < partialSumMax (fun k => X k ω) (⌊T*n i⌋₊+1)} := by
    intro ω hω
    exact (lt_div_iff₀ hri).mp (hω.trans_le (norm_scaledPolygon_le_max _ hri hni hT))
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans hi).trans (by linarith)

lemma continuousOscillation_mono {ε δ δ' : ℝ} (hδ : δ ≤ δ') :
    ContinuousOscillation ε δ ⊆ ContinuousOscillation ε δ' := by
  rintro f ⟨s,t,hst,h⟩
  exact ⟨s,t,hst.trans hδ,h⟩

lemma continuousOscillation_iInter_empty {ε : ℝ} (hε : 0 < ε) :
    (⋂ m : ℕ, ContinuousOscillation ε (1/(m+1))) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro f hf
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hm := (tendsto_order.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 δ hδ
  obtain ⟨m,hm⟩ := hm.exists
  rcases Set.mem_iInter.mp hf m with ⟨s,t,hst,hbig⟩
  have hc := hfδ (hst.trans_lt hm)
  exact (not_lt_of_ge hbig.le) (by simpa [Real.dist_eq] using hc)

lemma tendsto_measure_continuousOscillation (μ : Measure C(unitInterval,ℝ))
    [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => μ (ContinuousOscillation ε (1/(m+1)))) atTop (𝓝 0) := by
  have ha : Antitone (fun m : ℕ => ContinuousOscillation ε (1/(m+1))) := by
    intro j k hjk
    apply continuousOscillation_mono
    gcongr
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun m : ℕ => (isOpen_continuousOscillation ε (1/(m+1))).measurableSet.nullMeasurableSet)
    ha ⟨0,measure_ne_top _ _⟩
  rw [continuousOscillation_iInter_empty hε,measure_empty] at h
  exact h

lemma continuous_modulus_uniform_of_eventual
    (μ : ℕ → Measure C(unitInterval,ℝ)) [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ ε β : ℝ, 0 < ε → 0 < β → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ i in atTop, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β) :
    ∀ ε β : ℝ, 0 < ε → 0 < β → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β := by
  intro ε β hε hβ
  obtain ⟨δ,hδ,hb⟩ := h ε β hε hβ
  obtain ⟨N,hN⟩ := eventually_atTop.1 hb
  have he : ∀ᶠ m : ℕ in atTop, ∀ j : Fin N,
      μ j (ContinuousOscillation ε (1/(m+1))) ≤ ENNReal.ofReal β := by
    apply eventually_all.2
    intro j
    exact ((tendsto_order.mp (tendsto_measure_continuousOscillation (μ j) hε)).2
      _ (ENNReal.ofReal_pos.mpr hβ)).mono (fun _ hm => hm.le)
  obtain ⟨m,hm⟩ := he.exists
  refine ⟨min δ (1/(m+1)),lt_min hδ (by positivity),?_⟩
  intro i
  by_cases hi : N ≤ i
  · exact (measure_mono (continuousOscillation_mono (min_le_left _ _))).trans (hN i hi)
  · exact (measure_mono (continuousOscillation_mono (min_le_right _ _))).trans
      (hm ⟨i,by omega⟩)

lemma continuous_norm_uniform_of_eventual
    (μ : ℕ → Measure C(unitInterval,ℝ)) [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ β : ℝ, 0 < β → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ i in atTop, μ i {f | R < ‖f‖} ≤ ENNReal.ofReal β) :
    ∀ β : ℝ, 0 < β → ∃ R : ℝ, 0 < R ∧
      ∀ i, μ i {f | R < ‖f‖} ≤ ENNReal.ofReal β := by
  intro β hβ
  obtain ⟨R,hR,hb⟩ := h β hβ
  obtain ⟨N,hN⟩ := eventually_atTop.1 hb
  have he : ∀ᶠ r : ℝ in atTop, ∀ j : Fin N,
      μ j {f | r < ‖f‖} ≤ ENNReal.ofReal β := by
    apply eventually_all.2
    intro j
    have ht := tendsto_measure_norm_gt_of_isTightMeasureSet
      (isTightMeasureSet_singleton (μ := μ j))
    simp only [Set.mem_singleton_iff,iSup_iSup_eq_left] at ht
    exact ((tendsto_order.mp ht).2 _ (ENNReal.ofReal_pos.mpr hβ)).mono (fun _ hm => hm.le)
  obtain ⟨r,hr⟩ := he.exists
  refine ⟨max R r, hR.trans_le (le_max_left _ _),?_⟩
  intro i
  by_cases hi : N ≤ i
  · exact (measure_mono (μ := μ i) (show {f : C(unitInterval,ℝ) | max R r < ‖f‖} ⊆ {f | R < ‖f‖} from fun _ hf => (le_max_left R r).trans_lt hf)).trans (hN i hi)
  · exact (measure_mono (μ := μ i) (show {f : C(unitInterval,ℝ) | max R r < ‖f‖} ⊆ {f | r < ‖f‖} from fun _ hf => (le_max_right R r).trans_lt hf)).trans
      (hr ⟨i,by omega⟩)

noncomputable def pathCompact (R : ℝ) (δ : ℕ → ℝ) : Set C(unitInterval,ℝ) :=
  {f | ‖f‖ ≤ R} ∩ ⋂ m : ℕ, (ContinuousOscillation (1/(m+1)) (δ m))ᶜ

lemma isClosed_pathCompact (R : ℝ) (δ : ℕ → ℝ) : IsClosed (pathCompact R δ) := by
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_iInter (fun m => (isOpen_continuousOscillation _ _).isClosed_compl))

lemma isCompact_pathCompact (R : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    IsCompact (pathCompact R δ) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ
  have hc : IsCompact (e.symm ⁻¹' pathCompact R δ) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-R) R) isCompact_Icc
      (e.symm ⁻¹' pathCompact R δ) ((isClosed_pathCompact R δ).preimage e.symm.continuous)
    · intro f t hf
      have hnorm : ‖e.symm f‖ ≤ R := hf.1
      have hval := ContinuousMap.norm_coe_le_norm (e.symm f) t
      have habs : |f t| ≤ R := hval.trans hnorm
      exact abs_le.mp habs
    · intro t
      apply Metric.equicontinuousAt_iff.2
      intro ε hε
      have hm := (tendsto_order.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 ε hε
      obtain ⟨m,hm⟩ := hm.exists
      refine ⟨δ m,hδ m,?_⟩
      intro s hst f
      have hf := Set.mem_iInter.mp f.2.2 m
      have hb : |f.1 t-f.1 s| ≤ 1/(m+1) := by
        by_contra! hb
        exact hf ⟨t,s,by simpa [dist_comm] using hst.le,hb⟩
      simpa [Real.dist_eq] using hb.trans_lt hm
  have he : e.symm '' (e.symm ⁻¹' pathCompact R δ) = pathCompact R δ :=
    Set.image_preimage_eq _ e.symm.surjective
  rw [← he]
  exact hc.image e.symm.continuous

lemma isTightMeasureSet_of_continuous_modulus
    (μ : ℕ → Measure C(unitInterval,ℝ)) [∀ i, IsFiniteMeasure (μ i)]
    (hnorm : ∀ β : ℝ, 0 < β → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ i in atTop, μ i {f | R < ‖f‖} ≤ ENNReal.ofReal β)
    (hmod : ∀ ε β : ℝ, 0 < ε → 0 < β → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ i in atTop, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β) :
    IsTightMeasureSet (Set.range μ) := by
  have hn := continuous_norm_uniform_of_eventual μ hnorm
  have hm := continuous_modulus_uniform_of_eventual μ hmod
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2
  intro ε hε
  obtain ⟨b,hb,hbs⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  obtain ⟨R,hR,hRb⟩ := hn (b 0) (by exact_mod_cast hb 0)
  have hd : ∀ m : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      μ i (ContinuousOscillation (1/(m+1)) δ) ≤ (b (m+1) : ℝ≥0∞) := by
    intro m
    simpa only [ENNReal.ofReal_coe_nnreal] using
      hm (1/(m+1)) (b (m+1)) (by positivity) (by exact_mod_cast hb (m+1))
  choose δ hδ hd using hd
  refine ⟨pathCompact R δ,isCompact_pathCompact R δ hδ,?_⟩
  rintro _ ⟨i,rfl⟩
  have he : (pathCompact R δ)ᶜ = {f | R < ‖f‖} ∪
      ⋃ m : ℕ, ContinuousOscillation (1/(m+1)) (δ m) := by
    ext f
    simp [pathCompact,imp_iff_not_or]
  rw [he]
  calc
    _ ≤ μ i {f | R < ‖f‖}+μ i (⋃ m : ℕ, ContinuousOscillation (1/(m+1)) (δ m)) := measure_union_le _ _
    _ ≤ (b 0 : ℝ≥0∞) + ∑' m : ℕ, (b (m+1) : ℝ≥0∞) := by
      gcongr
      · simpa only [ENNReal.ofReal_coe_nnreal] using hRb i
      · exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun m => hd m i))
    _ = ∑' m : ℕ, (b m : ℝ≥0∞) := (tsum_eq_zero_add' (f := fun m : ℕ => (b m : ℝ≥0∞)) ENNReal.summable).symm
    _ ≤ ε := hbs.le

theorem gaussian_iid_path_tight {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    IsTightMeasureSet (Set.range (fun i => μ.map (fun ω =>
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T))) := by
  let P := fun i ω => scaledPolygon (fun k => X k ω) (r i)
    (fluctuationScale μ (X 0) (r i)) T
  have hP : ∀ i, Measurable (P i) := fun i => measurable_scaledPolygon X hX _ _ _
  have : ∀ i, IsProbabilityMeasure (μ.map (P i)) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (hP i).aemeasurable).mpr inferInstance
  apply isTightMeasureSet_of_continuous_modulus
  · intro β hβ
    obtain ⟨R,hR,hb⟩ := gaussian_continuous_norm_bound μ X hX hind hident hsym hI hne r hr hT hβ
    refine ⟨R,hR,hb.mono (fun i hi => ?_)⟩
    rw [Measure.map_apply (hP i) (isOpen_lt continuous_const continuous_norm).measurableSet]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hβ.le).2 hi
  · intro ε β hε hβ
    obtain ⟨δ,hδ,hb⟩ := gaussian_continuous_modulus μ X hX hind hident hsym hI hne r hr hT hε hβ
    refine ⟨δ,hδ,hb.mono (fun i hi => ?_)⟩
    rw [Measure.map_apply (hP i) (isOpen_continuousOscillation ε δ).measurableSet]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hβ.le).2 hi

lemma tendstoInMeasure_pi {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : ℕ → Ω → ι → ℝ)
    (h : ∀ j, TendstoInMeasure μ (fun n ω => F n ω j) atTop 0) :
    TendstoInMeasure μ F atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have ht : Tendsto (fun n => ∑ j, μ.real {ω | ε ≤ |F n ω j|}) atTop (𝓝 0) := by
    convert tendsto_finsetSum Finset.univ (fun j _ =>
      (tendstoInMeasure_iff_measureReal_norm.1 (h j)) ε hε) using 1 <;>
      simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs,Finset.sum_const_zero]
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  have hs : {ω | ε ≤ ‖F n ω-(0 : Ω → ι → ℝ) ω‖} ⊆ ⋃ j, {ω | ε ≤ |F n ω j|} := by
    intro ω hω
    by_contra! hc
    have hl : ‖F n ω‖ < ε := (pi_norm_lt_iff hε).2 (by simpa [Real.norm_eq_abs] using hc)
    exact (not_lt_of_ge (show ε ≤ ‖F n ω‖ by simpa using hω)) hl
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_iUnion_fintype_le _)

lemma tendstoInMeasure_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : ℕ → Ω → ℝ)
    (hG : TendstoInMeasure μ G atTop 0)
    (hb : ∀ᶠ n in atTop, ∀ ω, |F n ω| ≤ |G n ω|) :
    TendstoInMeasure μ F atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hg := (tendstoInMeasure_iff_measureReal_norm.1 hG) ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hg ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hg
  filter_upwards [hb] with n hn
  exact measureReal_mono (fun ω hω => hω.trans (hn ω)) (measure_ne_top _ _)

lemma selected_iid_div_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (k : ℕ → ℕ) :
    TendstoInMeasure μ (fun n ω => X (k n) ω/r n) atTop 0 := by
  have h0 : TendstoInMeasure μ (fun n ω => X 0 ω/r n) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hX.div_const _).aestronglyMeasurable)
    filter_upwards [] with ω
    exact tendsto_const_nhds.div_atTop hr
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have he n : μ.real {ω | ε ≤ ‖X (k n) ω/r n-(0 : Ω → ℝ) ω‖} =
      μ.real {ω | ε ≤ ‖X 0 ω/r n-(0 : Ω → ℝ) ω‖} := by
    simp only [Pi.zero_apply,sub_zero]
    unfold Measure.real
    apply congrArg ENNReal.toReal
    exact ((hident (k n)).comp (show Measurable (fun x : ℝ => x/r n) by fun_prop)).measure_mem_eq
      (s := {x : ℝ | ε ≤ ‖x‖}) (isClosed_le continuous_const continuous_norm).measurableSet
  simp_rw [he]
  exact (tendstoInMeasure_iff_measureReal_norm.1 h0) ε hε

lemma polygon_eval_error_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : ∀ᶠ i in atTop, 0 ≤ n i)
    {T : ℝ} (hT : 0 ≤ T) (s : unitInterval) :
    TendstoInMeasure μ (fun i ω => scaledPolygon (fun k => X k ω) (r i) (n i) T s -
      realPartialSum (fun k => X k ω) ⌊(T*s)*n i⌋₊/r i) atTop 0 := by
  have hsel := selected_iid_div_tendstoInMeasure μ X hX hident r hr (fun i => ⌊(T*s)*n i⌋₊)
  apply tendstoInMeasure_of_abs_le μ _ _ hsel
  filter_upwards [hn,hr.eventually (eventually_gt_atTop (0:ℝ))] with i hni hri
  intro ω
  rw [scaledPolygon_apply]
  have he : T*n i*s = (T*s)*n i := by ring
  rw [he,← sub_div,abs_div,abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  apply linearPolygon_near_partialSum
  · exact mul_nonneg (mul_nonneg hT s.2.1) hni
  · apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    calc
      (T*s)*n i = (T*n i)*s := by ring
      _ ≤ T*n i := mul_le_of_le_one_right (mul_nonneg hT hni) s.2.2
  · exact le_rfl

end DirectionalTransience
end
end

end OAI
