import OAI.MeasureTheory.SelfSimilar.Main

namespace OAI

universe uι

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

/-- The actual coding attractor, including every address, not merely an a.e. carrier. -/
def attractor (S : System ι) : Set ℝ := Set.range (Coding.point S)

theorem point_continuous [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] (S : System ι) :
    Continuous (Coding.point S) := by
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  change Continuous (fun ω : ℕ → ι => ∑' n, Coding.term S ω n)
  apply continuous_tsum (u := fun n => c ^ n * T)
  · intro n
    change Continuous (fun ω : ℕ → ι => (∏ j ∈ Finset.range n, S.ratio (ω j)) * S.offset (ω n))
    apply Continuous.mul
    · apply continuous_finsetProd
      intro j hj
      exact (continuous_of_discreteTopology : Continuous S.ratio).comp (continuous_apply j)
    · exact (continuous_of_discreteTopology : Continuous S.offset).comp (continuous_apply n)
  · exact (summable_geometric_of_lt_one hc.le hc1).mul_right T
  · intro n ω
    simpa only [Real.norm_eq_abs] using Coding.abs_term_le S ω hc.le hT hr ht n

theorem attractor_compact [Nonempty ι] (S : System ι) : IsCompact (attractor S) := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  exact isCompact_range (point_continuous S)

theorem attractor_nonempty [Nonempty ι] (S : System ι) : (attractor S).Nonempty :=
  Set.range_nonempty _

def cylinderRatio (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ≥0 :=
  ∏ j, ‖S.ratio (w j)‖₊

theorem affine_lipschitz [Nonempty ι] (S : System ι) (i : ι) :
    LipschitzWith ‖S.ratio i‖₊ (S.affine i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [System.affine, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  rw [show S.ratio i * x + S.offset i - (S.ratio i * y + S.offset i) =
    S.ratio i * (x-y) by ring, abs_mul]

theorem wordMap_lipschitz [Nonempty ι] (S : System ι) {n : ℕ} (w : Fin n → ι) :
    LipschitzWith (cylinderRatio S w) (S.wordMap w) := by
  induction n with
  | zero =>
    have he : S.wordMap w = (id : ℝ → ℝ) := by
      funext x
      simp [System.wordMap, System.completeMap, System.wordAffine]
    rw [he]
    simpa [cylinderRatio]
      using (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
  | succ n ih =>
    have hw : w = Fin.cons (w 0) (fun j => w j.succ) := by
      ext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [hw, System.wordMap_cons]
    simpa only [cylinderRatio, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      using (affine_lipschitz S (w 0)).comp (ih (fun j => w j.succ))

theorem cylinderRatio_le [Nonempty ι] (S : System ι) {c : ℝ} (hc : 0 ≤ c)
    (hr : ∀ i, |S.ratio i| ≤ c) {n : ℕ} (w : Fin n → ι) :
    (cylinderRatio S w : ℝ) ≤ c ^ n := by
  simp only [cylinderRatio, NNReal.coe_prod, coe_nnnorm, Real.norm_eq_abs]
  calc
    (∏ index : Fin n, |S.ratio (w index)|) ≤ ∏ _index : Fin n, |c| :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun index _ => (hr (w index)).trans (le_abs_self c))
    _ = c ^ n := by simp [abs_of_nonneg hc]

/-- Exact finite-word partition function, valid whether or not cylinders overlap. -/
theorem cylinderRatio_power_sum [Nonempty ι] (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hroot : ∑ i, |S.ratio i| ^ s = 1) (n : ℕ) :
    ∑ w : Fin n → ι, (cylinderRatio S w : ℝ≥0∞) ^ s = 1 := by
  classical
  have hletters : ∑ i, (‖S.ratio i‖₊ : ℝ≥0∞) ^ s = 1 := by
    have he : ∀ i, (‖S.ratio i‖₊ : ℝ≥0∞) ^ s =
        ENNReal.ofReal (|S.ratio i| ^ s) := by
      intro i
      rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs]
      simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    simp_rw [he]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _), hroot]
    simp
  have he : ∀ w : Fin n → ι, (cylinderRatio S w : ℝ≥0∞) ^ s =
      ∏ j, (‖S.ratio (w j)‖₊ : ℝ≥0∞) ^ s := by
    intro w
    simp only [cylinderRatio, ENNReal.ofNNReal_finsetProd, ENNReal.prod_rpow_of_nonneg hs]
  simp_rw [he]
  simpa [hletters] using
    (Fintype.prod_sum (fun (_ : Fin n) (i : ι) => (‖S.ratio i‖₊ : ℝ≥0∞) ^ s)).symm

/-- At every depth the genuine finite-word cylinders cover every coding limit. -/
theorem attractor_subset_cylinders [Nonempty ι] (S : System ι) (n : ℕ) :
    attractor S ⊆ ⋃ w : Fin n → ι, S.wordMap w '' attractor S := by
  rintro x ⟨ω, rfl⟩
  suffices ∀ n (ω : ℕ → ι), ∃ w : Fin n → ι,
      Coding.point S ω ∈ S.wordMap w '' attractor S by
    obtain ⟨w, hw⟩ := this n ω
    exact Set.mem_iUnion.mpr ⟨w, hw⟩
  intro n
  induction n with
  | zero =>
    intro ω
    refine ⟨Fin.elim0, Coding.point S ω, ⟨ω, rfl⟩, ?_⟩
    simp [System.wordMap, System.completeMap, System.wordAffine]
  | succ n ih =>
    intro ω
    obtain ⟨w, y, hy, he⟩ := ih (Coding.shift ω)
    refine ⟨Fin.cons (ω 0) w, y, hy, ?_⟩
    rw [System.wordMap_cons, Function.comp_apply, he, ← Coding.point_shift]

/-- The cylinder cover proves finite Hausdorff measure at the similarity exponent.
No separation hypothesis and no assumed covering estimate enter this theorem. -/
theorem attractor_hausdorffMeasure_le [Nonempty ι] (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    Measure.hausdorffMeasure s (attractor S) ≤ Metric.ediam (attractor S) ^ s := by
  classical
  let D := Metric.ediam (attractor S)
  have hD : D ≠ ∞ := (attractor_compact S).isBounded.ediam_ne_top
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  let mesh : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (c ^ n * D.toReal)
  have hmesh : Tendsto mesh atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).mul_const D.toReal
    simpa only [mesh, Function.comp_def, zero_mul, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hdiam (n : ℕ) (w : Fin n → ι) :
      Metric.ediam (S.wordMap w '' attractor S) ≤ (cylinderRatio S w : ℝ≥0∞) * D :=
    (wordMap_lipschitz S w).ediam_image_le _
  have hbound (n : ℕ) (w : Fin n → ι) :
      Metric.ediam (S.wordMap w '' attractor S) ≤ mesh n := by
    apply (hdiam n w).trans
    have hf : (cylinderRatio S w : ℝ≥0∞) ≤ ENNReal.ofReal (c ^ n) := by
      rw [ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_le_ofReal (cylinderRatio_le S hc.le hr w)
    have hh := mul_le_mul' hf (le_refl D)
    simpa only [mesh, ENNReal.ofReal_mul (pow_nonneg hc.le n), ENNReal.ofReal_toReal hD] using hh
  have hsum (n : ℕ) :
      (∑ w : Fin n → ι, Metric.ediam (S.wordMap w '' attractor S) ^ s) ≤ D ^ s := by
    calc
      _ ≤ ∑ w : Fin n → ι, ((cylinderRatio S w : ℝ≥0∞) * D) ^ s :=
        Finset.sum_le_sum (fun w _ => ENNReal.rpow_le_rpow (hdiam n w) hs)
      _ = (∑ w : Fin n → ι, (cylinderRatio S w : ℝ≥0∞) ^ s) * D ^ s := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hs, Finset.sum_mul]
      _ = D ^ s := by rw [cylinderRatio_power_sum S hs hroot, one_mul]
  apply (Measure.hausdorffMeasure_le_liminf_sum s (attractor S) mesh hmesh
    (fun n w => S.wordMap w '' attractor S)
    (Eventually.of_forall hbound)
    (Eventually.of_forall (attractor_subset_cylinders S))).trans
  calc
    _ ≤ liminf (fun _n : ℕ => D ^ s) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hsum)
    _ = D ^ s := by simp

theorem attractor_dim_le_similarity [Nonempty ι] (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    dimH (attractor S) ≤ ENNReal.ofReal s := by
  have hfinite : Measure.hausdorffMeasure s (attractor S) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hs (attractor_compact S).isBounded.ediam_ne_top)
      (attractor_hausdorffMeasure_le S hs hroot)
  rw [ENNReal.ofReal_eq_coe_nnreal hs]
  exact dimH_le_of_hausdorffMeasure_ne_top (d := ⟨s, hs⟩) hfinite

theorem attractor_dim_le_one [Nonempty ι] (S : System ι) : dimH (attractor S) ≤ 1 := by
  exact (dimH_mono (Set.subset_univ _)).trans_eq Real.dimH_univ

/-- The single-symbol boundary genuinely has a singleton coding image. -/
theorem attractor_dim_single_symbol [Nonempty ι] [Subsingleton ι] (S : System ι) :
    dimH (attractor S) = 0 := by
  apply dimH_subsingleton
  rintro x ⟨ω, rfl⟩ y ⟨ν, rfl⟩
  congr 1
  exact Subsingleton.elim _ _

end EntropyRateDimension.Extensions

end OAI
