import OAI.Analysis.ProductSpaces.PathMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uH uα

namespace IndependentProducts
section HilbertTools

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weaklyNull_of_orthogonal_fixed_norm (u : ℕ → H) (c : ℝ) (hc : 0 < c)
    (hn : ∀ n, ‖u n‖ = c) (hi : Pairwise (fun n m => inner ℝ (u n) (u m) = 0)) :
    WeaklyNull u := by
  let w : ℕ → H := fun n => c⁻¹ • u n
  have hw : Orthonormal ℝ w := by
    constructor
    · intro n
      simp [w, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hc, hc.ne']
    · intro n m hnm
      simp [w, inner_smul_left, inner_smul_right, hi hnm]
  intro f
  let y := (InnerProductSpace.toDual ℝ H).symm f
  have hs := (hw.inner_products_summable y).tendsto_atTop_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hnorm : Tendsto (fun n => ‖f (w n)‖) atTop (𝓝 0) := by
    have he : ∀ n, inner ℝ (w n) y = f (w n) := fun n => by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, he] using hsqrt
  have hfw := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have heq : (fun n => f (u n)) = (fun n => c * f (w n)) := by
    funext n
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [heq]
  simpa using hfw.const_mul c

variable {α : Type uα} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]

/-- The canonical continuous inclusion L2 -> L1 on a probability space. -/
def l2ToL1 : Lp ℝ 2 ν →L[ℝ] Lp ℝ 1 ν :=
  ({ toFun := fun f => ⟨f.val, (Lp.antitone (by norm_num : (1 : ℝ≥0∞) ≤ 2)) f.property⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 1 ν).mkContinuous 1 (by
    intro f
    simp only [one_mul, Lp.norm_def]
    apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

lemma l2ToL1_coe (f : Lp ℝ 2 ν) : (l2ToL1 ν f : α → ℝ) = f := rfl

lemma norm_l2ToL1_le (f : Lp ℝ 2 ν) : ‖l2ToL1 ν f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def, l2ToL1_coe]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

end HilbertTools

section ChildL2
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (h₂ : MemLp (fun w : ℝ => w) 2 μ)

/-- The child jump in the Hilbert space L2. -/
def childIncrementL2 (v : Vertex) (n : ℕ) : Lp ℝ 2 (productMeasure μ) :=
  (pathProduct_memLp μ h₂ (child v n)).toLp (pathProduct (child v n)) -
    (pathProduct_memLp μ h₂ v).toLp (pathProduct v)

lemma childIncrementL2_ae (v : Vertex) (n : ℕ) :
    (childIncrementL2 μ h₂ v n : Sample → ℝ) =ᵐ[productMeasure μ]
      fun ω => pathProduct v ω * (ω (childEdge v n) - 1) := by
  filter_upwards [Lp.coeFn_sub ((pathProduct_memLp μ h₂ (child v n)).toLp _)
    ((pathProduct_memLp μ h₂ v).toLp _), (pathProduct_memLp μ h₂ (child v n)).coeFn_toLp,
    (pathProduct_memLp μ h₂ v).coeFn_toLp] with ω hs hc hp
  unfold childIncrementL2
  rw [hs]
  change ((pathProduct_memLp μ h₂ (child v n)).toLp _) ω -
    ((pathProduct_memLp μ h₂ v).toLp _) ω = _
  rw [hc, hp, pathProduct_child]
  ring

lemma l2ToL1_childIncrement (v : Vertex) (n : ℕ) :
    l2ToL1 (productMeasure μ) (childIncrementL2 μ h₂ v n) =
      pathL1 μ h₂ (child v n) - pathL1 μ h₂ v := by
  apply Lp.ext
  filter_upwards [childIncrementL2_ae μ h₂ v n,
    Lp.coeFn_sub (pathL1 μ h₂ (child v n)) (pathL1 μ h₂ v),
    pathL1_ae μ h₂ (child v n), pathL1_ae μ h₂ v] with ω hi hs hc hp
  rw [l2ToL1_coe, hi, hs]
  change _ = pathL1 μ h₂ (child v n) ω - pathL1 μ h₂ v ω
  rw [hc, hp, pathProduct_child]
  ring

lemma childIncrementL2_norm_constant (v : Vertex) (n : ℕ) :
    ‖childIncrementL2 μ h₂ v n‖ = ‖childIncrementL2 μ h₂ v 0‖ := by
  have hi : ∀ k, inner ℝ (childIncrementL2 μ h₂ v k) (childIncrementL2 μ h₂ v k) =
      (∫ ω, pathProduct v ω ^ 2 ∂productMeasure μ) * ∫ w : ℝ, (w - 1) ^ 2 ∂μ := by
    intro k
    rw [L2.inner_def]
    calc
      (∫ ω, inner ℝ (childIncrementL2 μ h₂ v k ω) (childIncrementL2 μ h₂ v k ω) ∂productMeasure μ) =
          ∫ ω, pathProduct v ω ^ 2 * (ω (childEdge v k) - 1) ^ 2 ∂productMeasure μ := by
        apply integral_congr_ae
        filter_upwards [childIncrementL2_ae μ h₂ v k] with ω hω
        rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
        ring
      _ = _ := integral_path_mul_coordinate μ v _ (childEdge_not_mem_pathEdges v k)
        (fun x => x ^ 2) (fun x => (x - 1) ^ 2) (measurable_id.pow_const 2)
        ((measurable_id.sub_const 1).pow_const 2)
  have he := (hi n).trans (hi 0).symm
  simp only [real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (childIncrementL2 μ h₂ v n), norm_nonneg (childIncrementL2 μ h₂ v 0)]

lemma indepFun_pathSquare_mul_child (v : Vertex) {n m : ℕ} (hnm : n ≠ m) :
    IndepFun (fun ω : Sample => pathProduct v ω ^ 2 * (ω (childEdge v n) - 1))
      (fun ω : Sample => ω (childEdge v m)) (productMeasure μ) := by
  classical
  let f : Edge → ℝ → ℝ := fun e w => if e = childEdge v n then w - 1 else w ^ 2
  have hf : ∀ e, Measurable (f e) := fun e => by
    dsimp [f]
    split_ifs
    · exact measurable_id.sub_const 1
    · exact measurable_id.pow_const 2
  have hnot : childEdge v m ∉ insert (childEdge v n) (pathEdges v) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun he => hnm ((childEdge_injective v he).symm), childEdge_not_mem_pathEdges v m⟩
  have hi := indepFun_finset_coordinates μ (insert (childEdge v n) (pathEdges v)) f hf
    (childEdge v m) hnot
  have he : (fun ω : Sample => ∏ i ∈ insert (childEdge v n) (pathEdges v), f i (ω i)) =
      (fun ω => pathProduct v ω ^ 2 * (ω (childEdge v n) - 1)) := by
    funext ω
    rw [Finset.prod_insert (childEdge_not_mem_pathEdges v n)]
    have hp : (∏ i ∈ pathEdges v, f i (ω i)) = pathProduct v ω ^ 2 := by
      rw [pathProduct_eq_prod_pathEdges, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ childEdge v n := fun h => childEdge_not_mem_pathEdges v n (h ▸ hi)
      simp [f, hne]
    simp only [f, ite_eq_left rfl, hp]
    ring
  rwa [he] at hi

lemma childIncrementL2_orthogonal (hmean : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) :
    Pairwise (fun n m => inner ℝ (childIncrementL2 μ h₂ v n) (childIncrementL2 μ h₂ v m) = 0) := by
  intro n m hnm
  rw [L2.inner_def]
  calc
    (∫ ω, inner ℝ (childIncrementL2 μ h₂ v n ω) (childIncrementL2 μ h₂ v m ω) ∂productMeasure μ) =
        ∫ ω, (pathProduct v ω ^ 2 * (ω (childEdge v n) - 1)) *
          (ω (childEdge v m) - 1) ∂productMeasure μ := by
      apply integral_congr_ae
      filter_upwards [childIncrementL2_ae μ h₂ v n, childIncrementL2_ae μ h₂ v m] with ω hn hm
      rw [hn, hm, real_inner_eq_re_inner, RCLike.inner_apply]
      simp only [conj_trivial, RCLike.re_to_real]
      ring
    _ = _ := by
      have hi := (indepFun_pathSquare_mul_child μ v hnm).integral_fun_comp_mul_comp
        (((measurable_pathProduct v).pow_const 2).mul ((measurable_pi_apply _).sub_const 1)).aemeasurable
        (measurable_pi_apply _).aemeasurable (f := id) (g := fun w : ℝ => w - 1)
        measurable_id.aestronglyMeasurable (measurable_id.sub_const 1).aestronglyMeasurable
      dsimp at hi
      rw [hi, integral_coordinate μ _ (fun w : ℝ => w - 1) (measurable_id.sub_const 1),
        integral_sub (h₂.integrable (by norm_num)) (integrable_const 1), hmean]
      simp

end ChildL2
end IndependentProducts

namespace IndependentProducts

lemma weaklyNull_child_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : MemLp (fun w : ℝ => w) 2 μ) (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w)
    (hmean : ∫ w : ℝ, w ∂μ = 1) (hnot : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)) (v : Vertex) :
    WeaklyNull (fun n => pathVector μ h₂ (child v n) - pathVector μ h₂ v) := by
  have hsize : ‖l2ToL1 (productMeasure μ) (childIncrementL2 μ h₂ v 0)‖ = ∫ w : ℝ, |w - 1| ∂μ := by
    rw [l2ToL1_childIncrement]
    exact norm_child_difference μ h₂ hpos hmean v 0
  have hnorm : 0 < ‖childIncrementL2 μ h₂ v 0‖ := by
    have hh := norm_l2ToL1_le (productMeasure μ) (childIncrementL2 μ h₂ v 0)
    rw [hsize] at hh
    exact (mean_abs_deviation_pos μ h₂ hnot).trans_le hh
  have hw : WeaklyNull (childIncrementL2 μ h₂ v) :=
    weaklyNull_of_orthogonal_fixed_norm _ _ hnorm
      (childIncrementL2_norm_constant μ h₂ v) (childIncrementL2_orthogonal μ h₂ hmean v)
  intro f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (productSpan μ) f
  have hh := hw (g.comp (l2ToL1 (productMeasure μ)))
  have he : (fun n => f (pathVector μ h₂ (child v n) - pathVector μ h₂ v)) =
      (fun n => (g.comp (l2ToL1 (productMeasure μ))) (childIncrementL2 μ h₂ v n)) := by
    funext n
    rw [ContinuousLinearMap.comp_apply, l2ToL1_childIncrement]
    exact (hg (pathVector μ h₂ (child v n) - pathVector μ h₂ v)).symm
  rwa [he]

/-- The closed L1 product span is infinite dimensional and admits no equivalent AUC norm. -/
theorem main_general (μ : Measure ℝ) (hμ : MultiplierHypotheses μ) :
    ¬ FiniteDimensional ℝ (productSpan μ) ∧
    ∀ N : Seminorm ℝ (productSpan μ),
      IsEquivalentNorm (productSpan μ) N → ¬ IsAUC (productSpan μ) N := by
  let := hμ.probability
  have hweak := weaklyNull_child_difference μ hμ.second_moment hμ.positive hμ.mean_one hμ.nonconstant
  have hsize := norm_child_difference μ hμ.second_moment hμ.positive hμ.mean_one
  have hρ := mean_abs_deviation_pos μ hμ.second_moment hμ.nonconstant
  constructor
  · exact not_finiteDimensional_of_weaklyNull_fixed_norm (hweak []) hρ (hsize [])
  · exact bounded_tree_no_equivalent_auc (pathVector μ hμ.second_moment)
      (norm_pathVector μ hμ.second_moment hμ.positive hμ.mean_one) hρ hsize hweak

end IndependentProducts

end

end OAI
