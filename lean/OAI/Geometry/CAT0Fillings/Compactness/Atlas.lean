import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Compactness.ChartDensity
import OAI.Geometry.CAT0Fillings.Compactness.Tails
import OAI.Geometry.CAT0Fillings.Compactness.Borel

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace CAT0Fillings.JointBV
variable {β : Type*} [MeasurableSpace β] (σ : ℕ → Measure β)
  (μ : Measure (ℕ × β)) [IsFiniteMeasure μ]
  (hμ : μ = Measure.sum (fun i => (σ i).map (Prod.mk i)))

include hμ
omit [IsFiniteMeasure μ] in
lemma integral_prefix [IsFiniteMeasure μ] {f : ℕ × β → ℝ} (hf : Integrable f μ) (N : ℕ) :
    (∫ w, (if w.1 < N then f w else 0) ∂μ) =
      ∑ i ∈ Finset.range N, ∫ z, f (i,z) ∂σ i := by
  have hs : MeasurableSet {w : ℕ × β | w.1 < N} := measurableSet_lt measurable_fst measurable_const
  have hi : Integrable (fun w : ℕ × β => if w.1 < N then f w else 0) μ := by
    apply (hf.indicator hs).congr
    filter_upwards [] with w
    by_cases hw : w.1 < N <;> simp [hw]
  rw [hμ] at hi ⊢
  rw [integral_sum_measure hi]
  have he (i : ℕ) : (∫ w : ℕ × β, (if w.1 < N then f w else 0) ∂(σ i).map (Prod.mk i)) =
      if i < N then ∫ z, f (i,z) ∂σ i else 0 := by
    rw [(measurableEmbedding_prodMk_left i).integral_map]
    by_cases hi : i < N <;> simp [hi]
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [ite_eq_left hi]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [ite_eq_right hi]

lemma integral_abs_le_finite_parts_add_tail {f : ℕ × β → ℝ}
    (hf : MemLp f 2 μ) (N : ℕ) :
    (∫ w, |f w| ∂μ) ≤ (∑ i ∈ Finset.range N, ∫ z, |f (i,z)| ∂σ i) +
      lpNorm f 2 μ*lpNorm (indexTail Prod.fst N) 2 μ := by
  have hi := (hf.integrable (by norm_num)).abs
  have hs : MeasurableSet {w : ℕ × β | w.1 < N} := measurableSet_lt measurable_fst measurable_const
  have hp : Integrable (fun w : ℕ × β => if w.1 < N then |f w| else 0) μ := by
    apply (hi.indicator hs).congr
    filter_upwards [] with w
    by_cases hw : w.1 < N <;> simp [hw]
  have ht : Integrable (fun w : ℕ × β => |f w| *|indexTail Prod.fst N w|) μ := by
    apply hi.mul_bdd (c := 1) (measurable_indexTail Prod.fst measurable_fst N).abs.aestronglyMeasurable
    exact Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs,abs_abs] using indexTail_bound Prod.fst N w
  have he : (fun w => |f w|) = fun w => (if w.1 < N then |f w| else 0)+|f w| *|indexTail Prod.fst N w| := by
    ext w
    by_cases hw : w.1 < N
    · simp [indexTail,hw,Nat.not_le.mpr hw]
    · simp [indexTail,hw,Nat.le_of_not_gt hw]
  calc
    _ = (∫ w, (if w.1 < N then |f w| else 0) ∂μ)+(∫ w, |f w| *|indexTail Prod.fst N w| ∂μ) := by
      rw [←integral_add hp ht,←he]
    _ ≤ (∑ i ∈ Finset.range N, ∫ z, |f (i,z)| ∂σ i) +lpNorm f 2 μ*lpNorm (indexTail Prod.fst N) 2 μ := by
      rw [integral_prefix σ μ hμ hi N]
      exact add_le_add le_rfl (integral_abs_mul_le_lpNorm_two hf (memLp_indexTail μ Prod.fst measurable_fst N))

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def value1 {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Lp ℝ 1 (MassMeasure.currentMassMeasure hT) :=
  ((boundedLip_of_lipschitz hu).memLp 1).toLp u

omit [Nonempty X] in
lemma dist_value1 [Nonempty X] {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    dist (value1 (hT := hT) hu) (value1 hv) =
      ∫ x, |u x-v x| ∂MassMeasure.currentMassMeasure hT := by
  rw [dist_eq_norm,L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (value1 (hT := hT) hu) (value1 hv),
    ((boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 1).coeFn_toLp,
    ((boundedLip_of_lipschitz hv).memLp (μ := MassMeasure.currentMassMeasure hT) 1).coeFn_toLp] with x hx hux hvx
  rw [hx]
  change ‖(((boundedLip_of_lipschitz hu).memLp 1).toLp u) x-
    (((boundedLip_of_lipschitz hv).memLp 1).toLp v) x‖ = _
  rw [hux,hvx,Real.norm_eq_abs]

lemma dist_coordinateL1_eq (i : ℕ) {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.coordinateL1 i hu U hU) (q.coordinateL1 i hv V hV) =
      ∫ z, |u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)| ∂q.coordinateMeasure i := by
  rw [q.dist_coordinateL1,coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul]

lemma dist_value1_le_prefix {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) (N : ℕ) :
    dist (value1 (hT := hT) hu) (value1 hv) ≤
      (∑ i ∈ Finset.range N, dist (q.coordinateL1 i hu.continuous.measurable U hU)
        (q.coordinateL1 i hv.continuous.measurable V hV)) +
      (‖value (hT := hT) hu‖+‖value (hT := hT) hv‖)*lpNorm (indexTail Prod.fst N) 2 q.atlasMeasure := by
  let μ := MassMeasure.currentMassMeasure hT
  have hmp : MeasurePreserving q.atlasParam q.atlasMeasure μ := ⟨q.measurable_atlasParam,q.map_atlasMeasure⟩
  have hmem : MemLp (fun x => u x-v x) 2 μ := ((boundedLip_of_lipschitz hu).memLp 2).sub ((boundedLip_of_lipschitz hv).memLp 2)
  have hma := hmem.comp_measurePreserving hmp
  have hh := integral_abs_le_finite_parts_add_tail q.coordinateMeasure q.atlasMeasure rfl hma N
  have hleft : (∫ w, |u (q.atlasParam w)-v (q.atlasParam w)| ∂q.atlasMeasure) =
      dist (value1 (hT := hT) hu) (value1 hv) := by
    rw [dist_value1,←q.map_atlasMeasure]
    symm
    simpa only [Pi.sub_apply] using integral_map q.measurable_atlasParam.aemeasurable
      (hu.continuous.sub hv.continuous).abs.aestronglyMeasurable
  change (∫ w, |u (q.atlasParam w)-v (q.atlasParam w)| ∂q.atlasMeasure) ≤ _ at hh
  rw [hleft] at hh
  have hnorm : lpNorm ((fun x => u x-v x) ∘ q.atlasParam) 2 q.atlasMeasure ≤
      ‖value (hT := hT) hu‖+‖value (hT := hT) hv‖ := by
    rw [←toReal_eLpNorm,eLpNorm_comp_measurePreserving hmem.aestronglyMeasurable hmp]
    have he : hmem.toLp _ = value (hT := hT) hu-value hv :=
      MemLp.toLp_sub ((boundedLip_of_lipschitz hu).memLp 2) ((boundedLip_of_lipschitz hv).memLp 2)
    rw [←Lp.norm_toLp (fun x => u x-v x) hmem,he]
    exact norm_sub_le _ _
  apply hh.trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro index _
    rw [q.dist_coordinateL1_eq]
    rfl
  · exact mul_le_mul_of_nonneg_right hnorm lpNorm_nonneg

theorem totallyBounded_value1 {ι : Type*}
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (hU : ∀ j x, |u j x| ≤ U j)
    (M : ℝ≥0) (hMv : ∀ j, ‖value (hT := hT) (hu j)‖ ≤ M)
    (hMg : ∀ j, ‖q.gradient (hu j)‖ ≤ M) :
    TotallyBounded (range fun j => value1 (hT := hT) (hu j)) := by
  apply totallyBounded_range_of_finite_coordinate_control
    (q.totallyBounded_coordinate h hz hX u L U hu hU M hMv hMg)
  intro ε hε
  have ht := (tendsto_lpNorm_indexTail q.atlasMeasure Prod.fst measurable_fst).const_mul (2*(M:ℝ))
  rw [mul_zero] at ht
  obtain ⟨N,hN⟩ := ((tendsto_order.1 ht).2 (ε/2) (half_pos hε)).exists
  refine ⟨N,ε/(2*((N:ℝ)+1)),div_pos hε (by positivity),?_⟩
  intro a b hab
  have hh := q.dist_value1_le_prefix (hu a) (hu b) (U a) (U b) (hU a) (hU b) N
  have hs : (∑ i ∈ Finset.range N, dist (q.coordinateL1 i (hu a).continuous.measurable (U a) (hU a))
      (q.coordinateL1 i (hu b).continuous.measurable (U b) (hU b))) ≤ (N:ℝ)*(ε/(2*((N:ℝ)+1))) := by
    calc _ ≤ ∑ _i ∈ Finset.range N, ε/(2*((N:ℝ)+1)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact (hab ⟨i,Finset.mem_range.mp hi⟩).le
      _ = _ := by simp
  have hp := mul_le_mul_of_nonneg_right (add_le_add (hMv a) (hMv b))
    (show 0 ≤ lpNorm (indexTail Prod.fst N) 2 q.atlasMeasure from lpNorm_nonneg)
  have hd : (N:ℝ)*(ε/(2*((N:ℝ)+1))) < ε/2 := by
    have he : (N:ℝ)*(ε/(2*((N:ℝ)+1))) = (ε/2)*((N:ℝ)/((N:ℝ)+1)) := by field_simp
    rw [he]
    apply mul_lt_of_lt_one_right (half_pos hε)
    exact (div_lt_one (by positivity)).2 (by linarith)
  have : (M:ℝ)+(M:ℝ) = 2*(M:ℝ) := by ring
  rw [this] at hp
  linarith

end CAT0Fillings.ChartGeometry
end

end OAI
