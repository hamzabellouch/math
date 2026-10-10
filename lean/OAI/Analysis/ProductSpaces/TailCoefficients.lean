import OAI.Analysis.ProductSpaces.ClosedTails

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma pathVector_ae (v : Vertex) :
    ((pathVector μ h₂ v).val : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v := pathL1_ae μ h₂ v

omit hμprob in
lemma representative_sum [IsProbabilityMeasure μ] {ι : Type uι} [Fintype ι]
    (x : ι → productSpan μ)
    (f : ι → Sample → ℝ) (hf : ∀ i, (x i).val =ᵐ[productMeasure μ] f i) (a : ι → ℝ) :
    ((∑ i, a i • x i).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => ∑ i, a i * f i ω := by
  have hs : (∑ i, a i • x i).val = ∑ i, a i • (x i).val := by simp
  rw [hs]
  have ha : ∀ i, (a i • (x i).val : Lp ℝ 1 (productMeasure μ)) =ᵐ[productMeasure μ]
      fun ω => a i * f i ω := by
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (x i).val, hf i] with ω hω hi
    simpa only [Pi.smul_apply, smul_eq_mul, hi] using hω
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • (x i).val),
    ae_all_iff.mpr ha] with ω hsum hall
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => hall i)

omit hμprob in
lemma representative_sub [IsProbabilityMeasure μ] (x y : productSpan μ) (f g : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) (hg : y.val =ᵐ[productMeasure μ] g) :
    ((x - y).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => f ω - g ω := by
  change (↑(x.val - y.val) : Sample → ℝ) =ᵐ[productMeasure μ] _
  filter_upwards [Lp.coeFn_sub x.val y.val, hf, hg] with ω he hx hy
  simpa only [Pi.sub_apply, hx, hy] using he

omit hμprob in
lemma norm_eq_integral_abs_rep [IsProbabilityMeasure μ] (x : productSpan μ) (f : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) : ‖x‖ = ∫ ω, |f ω| ∂productMeasure μ := by
  change ‖x.val‖ = _
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  simp only [hω, Real.norm_eq_abs]

lemma integrable_rep (x : productSpan μ) (f : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) : Integrable f (productMeasure μ) :=
  ((Lp.memLp x.val).integrable le_rfl).congr hf

namespace FiniteHead
variable (T : FiniteHead)

lemma relativeVector_ae (v : Vertex) :
    ((T.relativeVector μ h₂ v).val : Sample → ℝ) =ᵐ[productMeasure μ]
      fun ω => pathProduct v ω - pathProduct (T.ancestor v) ω :=
  representative_sub μ _ _ _ _ (pathVector_ae μ h₂ v) (pathVector_ae μ h₂ (T.ancestor v))

lemma head_representative (x : productSpan μ) (hx : x ∈ T.headSpan μ h₂) :
    ∃ a : T.vertices → ℝ, x = ∑ v : T.vertices, a v • pathVector μ h₂ v := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun ℝ).mp hx
  exact ⟨a, ha.symm⟩

lemma tail_representative (y : productSpan μ) (hy : y ∈ T.tailAlgebraic μ h₂) :
    ∃ s : Finset Vertex, (∀ v ∈ s, v ∉ T.vertices) ∧
      ∃ a : s → ℝ, y = ∑ v : s, a v • T.relativeVector μ h₂ v := by
  obtain ⟨s, hs, a, ha⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ).mp hy
  exact ⟨s, fun v hv => hs hv, a, ha.symm⟩

end FiniteHead
end FiniteRepresentatives

/-- Descendant-only factor after the first exit. -/
def residualProduct (v : Vertex) (e : Edge) (ω : Sample) : ℝ :=
  ∏ d ∈ pathEdges v \ pathEdges e.val, ω d

lemma measurable_residualProduct (v : Vertex) (e : Edge) : Measurable (residualProduct v e) := by
  unfold residualProduct
  fun_prop

lemma integrable_residualProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (v : Vertex) (e : Edge) :
    Integrable (residualProduct v e) (productMeasure μ) :=
  integrable_finset_coordinates_prod μ _ _ (fun _ _ => hw)

lemma integral_residualProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) (e : Edge) :
    ∫ ω, residualProduct v e ω ∂productMeasure μ = 1 := by
  change (∫ ω : Sample, ∏ d ∈ pathEdges v \ pathEdges e.val, ω d ∂productMeasure μ) = 1
  rw [integral_finset_coordinates_prod μ _ (fun _ w => w) (by fun_prop)]
  simp only [hm, Finset.prod_const_one]

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

/-- Coefficients conditionally independent below the exit forest. -/
noncomputable def tailCoefficient (old : Sample) (i : ι) (desc : Sample) : ℝ :=
  ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old *
    residualProduct (v k) (e i).val desc else 0

lemma measurable_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (i : ι) :
    Measurable (fun z : Sample × Sample => T.tailCoefficient e v j a z.1 i z.2) := by
  classical
  unfold tailCoefficient
  apply Finset.measurable_sum
  intro k hk
  split_ifs
  · exact ((measurable_const.mul ((measurable_pathProduct _).comp measurable_fst)).mul
      ((measurable_residualProduct _ _).comp measurable_snd))
  · fun_prop

lemma integrable_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (old : Sample) (i : ι) :
    Integrable (T.tailCoefficient e v j a old i) (productMeasure μ) := by
  classical
  apply integrable_finsetSum
  intro k hk
  split_ifs
  · exact (integrable_residualProduct μ hw _ _).const_mul _
  · exact integrable_zero _ _ _

lemma integral_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (hm : ∫ w : ℝ, w ∂μ = 1)
    (old : Sample) (i : ι) :
    ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ =
      ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old else 0 := by
  classical
  unfold tailCoefficient
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · rw [integral_const_mul, integral_residualProduct μ hm, mul_one]
    · simp
  · intro k hk
    split_ifs
    · exact (integrable_residualProduct μ hw _ _).const_mul _
    · exact integrable_zero _ _ _

lemma sum_tailCoefficient (z : ((ι → Sample) × Sample) × Sample)
    (he : Function.Injective e) (hv : ∀ k, (e (j k)).val.val <+: v k) :
    ∑ k, a k * pathProduct (v k) (T.stitched e z) =
      ∑ i, T.tailCoefficient e v j a z.2 i (z.1.1 i) * z.1.2 (e i).val := by
  classical
  simp only [tailCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.stitched_path e he z (v k) (j k) (hv k)]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, residualProduct]
  ring

lemma sum_tailCoefficient_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (hm : ∫ w : ℝ, w ∂μ = 1)
    (old : Sample) :
    ∑ i, ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ =
      ∑ k, a k * pathProduct (e (j k)).val.val.dropLast old := by
  classical
  simp_rw [T.integral_tailCoefficient e v j a μ hw hm old]
  rw [Finset.sum_comm]
  congr 1
  ext k
  simp

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI
