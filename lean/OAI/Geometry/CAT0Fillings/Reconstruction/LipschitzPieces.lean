import Mathlib
import OAI.Geometry.CAT0Fillings.BV.Oscillation

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

lemma measurable_real_closedBall (ν : Measure E) [SFinite ν] (r : ℝ) :
    Measurable (fun x : E => ν.real (closedBall x r)) := by
  have hs : MeasurableSet {p : E × E | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact (measurable_measure_prodMk_left hs).ennreal_toReal

def DensityPiece (ν : Measure E) (N j : ℕ) : Set E :=
  {x | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 / (j+1 : ℝ) →
    ν.real (closedBall x q) ≤ (N : ℝ) * μ.real (closedBall x q)}

lemma measurableSet_densityPiece (ν : Measure E) [SFinite ν] (N j : ℕ) :
    MeasurableSet (DensityPiece (μ := μ) ν N j) := by
  simp only [DensityPiece, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (measurable_real_closedBall ν q)
    ((measurable_real_closedBall μ q).const_mul (N : ℝ))

lemma ae_mem_iUnion_densityPiece (ν : Measure E) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂μ, ∃ N j : ℕ, x ∈ DensityPiece (μ := μ) ν N j := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_rnDeriv ν,
    Measure.rnDeriv_lt_top ν μ] with x hx hfin
  have hlim := (ENNReal.tendsto_toReal hfin.ne).comp
    (hx.comp (Besicovitch.tendsto_filterAt μ x))
  simp only [Function.comp_def, ENNReal.toReal_div] at hlim
  obtain ⟨N, hN⟩ := exists_nat_gt ((ν.rnDeriv μ x).toReal)
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ν.real (closedBall x r) / μ.real (closedBall x r) < (N : ℝ) :=
    (tendsto_order.1 hlim).2 _ hN
  obtain ⟨s, hs, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, j, ?_⟩
  intro q hq hjq
  have hqδ : (q : ℝ) < δ := hjq.trans_lt hj
  have hqs : (q : ℝ) ∈ s := hball (by
    simp only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hq]
    exact hqδ)
  have hh := hsub ⟨hqs, hq⟩
  exact (div_lt_iff₀ (haar_closedBall_pos (μ := μ) hq)).mp hh |>.le

lemma measure_ball_bound_of_densityPiece (ν : Measure E) [IsLocallyFiniteMeasure ν]
    {N j : ℕ} {x : E} (hx : x ∈ DensityPiece (μ := μ) ν N j)
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrj : 2 * κ * r ≤ 1 / (j+1 : ℝ)) :
    ν.real (closedBall x (κ*r)) ≤
      (N : ℝ) * (2 * κ)^Module.finrank ℝ E * μ.real (closedBall x r) := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show κ*r < 2*κ*r by nlinarith [mul_pos hκ hr])
  have hq : 0 < (q : ℝ) := (mul_pos hκ hr).trans hq1
  have hsmall : ν.real (closedBall x (κ*r)) ≤ ν.real (closedBall x q) :=
    measureReal_mono (closedBall_subset_closedBall hq1.le) measure_closedBall_lt_top.ne
  have hlarge : μ.real (closedBall x q) ≤ μ.real (closedBall x (2*κ*r)) :=
    measureReal_mono (closedBall_subset_closedBall hq2.le) measure_closedBall_lt_top.ne
  calc
    _ ≤ (N : ℝ) * μ.real (closedBall x q) := hsmall.trans (hx q hq (hq2.le.trans hrj))
    _ ≤ (N : ℝ) * μ.real (closedBall x (2*κ*r)) :=
      mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg _)
    _ = _ := by
      rw [haar_closedBall_scale (μ := μ) x x hr (2*κ) (by positivity)]
      ring

lemma localMeanBound_of_densityPiece {f : E → ℝ} {ν : Measure E}
    [IsLocallyFiniteMeasure ν] {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ x : E, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall x r, |f z - (⨍ w in closedBall x r, f w ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall x (κ*r)))
    {N j : ℕ} {x : E} (hx : x ∈ DensityPiece (μ := μ) ν N j) :
    LocalMeanBound (μ := μ) f (C * N * (2*κ)^Module.finrank ℝ E)
      x ((1 / (j+1 : ℝ)) / (2*κ)) := by
  intro r hr hrR
  have hd := measure_ball_bound_of_densityPiece ν hx hκ hr
    (by nlinarith [(le_div_iff₀ (show 0 < 2*κ by positivity)).mp hrR])
  calc
    _ ≤ C*r*ν.real (closedBall x (κ*r)) := hP x r hr
    _ ≤ C*r*((N : ℝ)*(2*κ)^Module.finrank ℝ E*μ.real (closedBall x r)) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg hC hr.le)
    _ = _ := by ring

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

lemma exists_compact_cover_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [Measure.IsAddHaarMeasure μ] {F : Set E} (hF : MeasurableSet F) (hfin : μ F ≠ ∞) :
    ∃ K : ℕ → Set E, (∀ i, K i ⊆ F ∧ IsCompact (K i)) ∧
      ∀ᵐ x ∂μ, x ∈ F → x ∈ ⋃ i, K i := by
  choose K hKF hK hsmall using fun n : ℕ =>
    hF.exists_isCompact_sdiff_lt hfin (show (1/2 : ℝ≥0∞)^n ≠ 0 by exact pow_ne_zero _ (by norm_num))
  refine ⟨K, fun i => ⟨hKF i, hK i⟩, ?_⟩
  have hbound (n : ℕ) : μ (F \ ⋃ i, K i) ≤ (1/2 : ℝ≥0∞)^n :=
    (measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))).trans (hsmall n).le
  have hz : μ (F \ ⋃ i, K i) = 0 := by
    apply le_antisymm _ bot_le
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1/2 : ℝ≥0∞) < 1)) (Eventually.of_forall hbound)
  apply ae_iff.mpr
  have he : {a | ¬(a ∈ F → a ∈ ⋃ i, K i)} = F \ ⋃ i, K i := by
    ext x
    exact Classical.not_imp
  rwa [he]

theorem common_compact_lipschitz_pieces {ι : Type*} [Countable ι]
    (f : ι → E → ℝ) (hf : ∀ a, LocallyIntegrable (f a) μ)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ a x, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall x r, |f a z - (⨍ w in closedBall x r, f a w ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall x (κ*r)))
    (G : Set E) (hG : ∀ᵐ x ∂μ, x ∈ G) :
    ∃ (K : (ℕ × ℕ × ℕ × ℕ) → Set E) (L : (ℕ × ℕ × ℕ × ℕ) → ℝ≥0),
      (∀ i, IsCompact (K i) ∧ K i ⊆ G) ∧
      (∀ i a, LipschitzOnWith (L i) (f a) (K i)) ∧
      (∀ᵐ x ∂μ, x ∈ ⋃ i, K i) := by
  classical
  let F : Set E := {x | x ∈ G ∧ ∀ a, Tendsto
    (fun r : ℝ => ⨍ z in closedBall x r, f a z ∂μ) (𝓝[>] 0) (𝓝 (f a x))}
  have hF : ∀ᵐ x ∂μ, x ∈ F := by
    filter_upwards [hG, ae_all_iff.mpr (fun a => ae_ballAverage_tendsto (hf a))] with x hx hy
    exact ⟨hx,hy⟩
  have hFn : NullMeasurableSet F μ := by
    apply (MeasurableSet.univ : MeasurableSet (univ : Set E)).nullMeasurableSet.congr
    filter_upwards [hF] with x hx
    apply propext
    exact ⟨fun _ => hx, fun _ => mem_univ x⟩
  obtain ⟨F₀, hF₀F, hF₀m, hF₀eq⟩ := hFn.exists_measurable_subset_ae_eq
  have hF₀ : ∀ᵐ x ∂μ, x ∈ F₀ := by
    filter_upwards [hF,hF₀eq] with x hx he
    exact he.mpr hx
  let R (j : ℕ) : ℝ := (1 / (j+1 : ℝ)) / (2*κ)
  have hR (j : ℕ) : 0 < R j := by dsimp [R]; positivity
  let H (i : ℕ × ℕ × ℕ) : Set E :=
    F₀ ∩ DensityPiece (μ := μ) ν i.1 i.2.1 ∩
      closedBall (denseSeq E i.2.2) (R i.2.1 / 4)
  have hHm (i : ℕ × ℕ × ℕ) : MeasurableSet (H i) :=
    (hF₀m.inter (measurableSet_densityPiece ν i.1 i.2.1)).inter isClosed_closedBall.measurableSet
  have hHfin (i : ℕ × ℕ × ℕ) : μ (H i) ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top)
  choose K hK hKcover using fun i : ℕ × ℕ × ℕ => exists_compact_cover_ae (hHm i) (hHfin i)
  let A (N : ℕ) : ℝ := C * N * (2*κ)^Module.finrank ℝ E
  have hA (N : ℕ) : 0 ≤ A N := by dsimp [A]; positivity
  let L (i : ℕ × ℕ × ℕ × ℕ) : ℝ≥0 :=
    ⟨8 * (2 : ℝ)^Module.finrank ℝ E * A i.1, by positivity⟩
  refine ⟨fun i => K (i.1,i.2.1,i.2.2.1) i.2.2.2, L, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hK _ _).2,?_⟩
    intro x hx
    exact (hF₀F ((hK _ _).1 hx).1.1).1
  · intro i a
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxH := (hK _ _).1 hx
    have hyH := (hK _ _).1 hy
    have hxF := hF₀F hxH.1.1
    have hyF := hF₀F hyH.1.1
    have hxM := localMeanBound_of_densityPiece hC hκ (hP a) hxH.1.2
    have hyM := localMeanBound_of_densityPiece hC hκ (hP a) hyH.1.2
    have hxy : 2 * dist x y ≤ R i.2.1 := by
      have htri := dist_triangle x (denseSeq E i.2.2.1) y
      have hx' : dist x (denseSeq E i.2.2.1) ≤ R i.2.1 / 4 := hxH.2
      have hy' : dist (denseSeq E i.2.2.1) y ≤ R i.2.1 / 4 := by
        simpa only [mem_closedBall, dist_comm] using hyH.2
      linarith
    exact abs_sub_le_of_localMeanBound (hf a) hxM hyM (hxF.2 a) (hyF.2 a) hxy
  · filter_upwards [hF₀, ae_mem_iUnion_densityPiece (μ := μ) ν,
      ae_all_iff.mpr hKcover] with x hx hD hcov
    obtain ⟨N,j,hNj⟩ := hD
    obtain ⟨l,hl⟩ := (denseRange_denseSeq E).exists_dist_lt x (show 0 < R j / 4 by positivity)
    have hxH : x ∈ H (N,j,l) := ⟨⟨hx,hNj⟩,hl.le⟩
    obtain ⟨m,hm⟩ := mem_iUnion.mp (hcov (N,j,l) hxH)
    exact mem_iUnion.mpr ⟨(N,j,l,m),hm⟩

end CAT0Fillings.JointBV
end

end OAI
