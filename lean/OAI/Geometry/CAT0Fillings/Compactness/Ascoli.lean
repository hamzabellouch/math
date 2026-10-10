import Mathlib

namespace OAI

section

open Set Filter Metric

namespace CAT0Fillings.JointBV
universe u
variable {ι : Type*} {α β : Type u} [PseudoMetricSpace α] [PseudoMetricSpace β]

lemma totallyBounded_range_of_control {f : ι → α} {g : ι → β}
    (hg : TotallyBounded (range g))
    (hcontrol : ∀ ε > 0, ∃ δ > 0, ∀ i j, dist (g i) (g j) < δ → dist (f i) (f j) < ε) :
    TotallyBounded (range f) := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨δ,hδ,hc⟩ := hcontrol ε hε
  obtain ⟨s,hs,hfin,hcover⟩ := Metric.finite_approx_of_totallyBounded hg (δ/2) (half_pos hδ)
  have : Fintype s := hfin.fintype
  have hnear (i : ι) : ∃ y : s, dist (g i) y < δ/2 := by
    have := hcover (mem_range_self i)
    simp only [mem_iUnion,mem_ball] at this
    obtain ⟨y,hy,hiy⟩ := this
    exact ⟨⟨y,hy⟩,hiy⟩
  choose c hc' using hnear
  let pick (x : range f) : ι := x.property.choose
  have hp (x : range f) : f (pick x) = x := x.property.choose_spec
  refine ⟨s,inferInstance,fun x => c (pick x),?_⟩
  intro x y he
  change c (pick x) = c (pick y) at he
  rw [←hp x,←hp y]
  apply hc
  calc dist (g (pick x)) (g (pick y)) ≤
      dist (g (pick x)) (c (pick x)) + dist (g (pick y)) (c (pick x)) := dist_triangle_right _ _ _
    _ < δ/2+δ/2 := add_lt_add (hc' _) (by rw [he]; exact hc' _)
    _ = δ := add_halves _

lemma totallyBounded_range_of_uniform_approx {f : ι → α}
    (happrox : ∀ ε > 0, ∃ g : ι → α, TotallyBounded (range g) ∧ ∀ i, dist (f i) (g i) < ε) :
    TotallyBounded (range f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g,hg,hd⟩ := happrox (ε/2) (half_pos hε)
  obtain ⟨s,hfin,hs⟩ := Metric.totallyBounded_iff.mp hg (ε/2) (half_pos hε)
  refine ⟨s,hfin,?_⟩
  rintro _ ⟨i,rfl⟩
  have := hs (mem_range_self i)
  simp only [mem_iUnion,mem_ball] at this ⊢
  obtain ⟨y,hy,hiy⟩ := this
  exact ⟨y,hy,(dist_triangle (f i) (g i) y).trans_lt
    ((add_lt_add (hd i) hiy).trans_eq (add_halves ε))⟩

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma dist_toL1_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f g : E → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, |f x-g x| ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1,hg.coeFn_toL1] with x hx hy
  rw [hx,hy,Real.dist_eq]

lemma totallyBounded_L1_of_compact_lipschitz_family {ι : Type*}
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (K : ℝ≥0) (hl : ∀ i, LipschitzWith K (f i))
    (B R : ℝ) (hb : ∀ i x, |f i x| ≤ B)
    (hs : ∀ i, Function.support (f i) ⊆ closedBall (0:E) R) :
    TotallyBounded (range fun i => (hf i).toL1 (f i)) := by
  let Q := closedBall (0:E) R
  have : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E) R)
  let F (i : ι) : BoundedContinuousFunction Q ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f i x,(hl i).continuous.comp continuous_subtype_val⟩
  have hK : ∀ g : range F, LipschitzWith K (fun x : Q => g.val x) := by
    rintro ⟨g,⟨i,rfl⟩⟩
    change LipschitzWith K (f i ∘ Subtype.val)
    simpa only [mul_one] using (hl i).comp (LipschitzWith.subtype_val Q)
  have heq : Equicontinuous (fun g : range F => fun x : Q => g.val x) :=
    (LipschitzWith.uniformEquicontinuous _ K hK).equicontinuous
  have hc : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc (range F)
      (by rintro _ x ⟨i,rfl⟩; exact abs_le.mp (hb i x)) heq
  apply totallyBounded_range_of_control (g := F) (hc.totallyBounded.subset subset_closure)
  intro ε hε
  let C := μ.real Q + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε/C,div_pos hε hC,?_⟩
  intro i j hij
  rw [dist_toL1_eq_integral]
  have he : (∫ x, |f i x-f j x| ∂μ) = ∫ x in Q, |f i x-f j x| ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hi : f i x = 0 := Function.notMem_support.mp (fun h => hx (hs i h))
    have hj : f j x = 0 := Function.notMem_support.mp (fun h => hx (hs j h))
    simp only [hi,hj,sub_self,abs_zero]
  rw [he]
  have hb' : (∫ x in Q, |f i x-f j x| ∂μ) ≤ dist (F i) (F j)*μ.real Q := by
    have hic : IntegrableOn (fun _ : E => dist (F i) (F j)) Q μ :=
      integrableOn_const (by dsimp [Q]; exact measure_closedBall_lt_top.ne)
    have hm := setIntegral_mono_on ((hf i).sub (hf j)).abs.integrableOn hic
      (show MeasurableSet Q from measurableSet_closedBall) (fun x hx =>
        show |(f i-f j) x| ≤ dist (F i) (F j) from
          BoundedContinuousFunction.dist_coe_le_dist (f := F i) (g := F j) ⟨x,hx⟩)
    exact hm.trans_eq (by simp only [integral_const,smul_eq_mul,measureReal_def,mul_comm,
      Measure.restrict_apply_univ])
  apply hb'.trans_lt
  calc dist (F i) (F j)*μ.real Q ≤ dist (F i) (F j)*C := by
        apply mul_le_mul_of_nonneg_left _ dist_nonneg
        dsimp [C]; linarith
    _ < (ε/C)*C := mul_lt_mul_of_pos_right hij hC
    _ = ε := div_mul_cancel₀ _ (ne_of_gt hC)

end CAT0Fillings.JointBV
end

end OAI
