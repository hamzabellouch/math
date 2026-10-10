import OAI.Geometry.Perimeter.Regularity.TendstoWeightedHalfspaceBlowup

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

def HasC1TraceAt {n : ℕ} (S : Set (Space n)) (h : Space n → ℝ)
    (x : Space n) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧ ∃ f : Space n → ℝ,
    ContDiffOn ℝ 1 f U ∧ EqOn f h (S ∩ U)

theorem exists_c1_eqOn_of_local_trace {n : ℕ} {S : Set (Space n)}
    (hS : IsClosed S) (h : Space n → ℝ)
    (hloc : ∀ x ∈ S, HasC1TraceAt S h x) :
    ∃ f : Space n → ℝ, ContDiff ℝ 1 f ∧ EqOn f h S := by
  classical
  let t : Space n → Set ℝ := fun x ↦ if x ∈ S then {h x} else univ
  have hc : ∀ x, Convex ℝ (t x) := by
    intro x
    dsimp [t]
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  have hlocal : ∀ x : Space n, ∃ U ∈ 𝓝 x, ∃ g : Space n → ℝ,
      ContMDiffOn (modelWithCornersSelf ℝ (Space n)) (modelWithCornersSelf ℝ ℝ) 1 g U ∧
      ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, hU, hxU, f, hf, he⟩ := hloc x hx
      refine ⟨U, hU.mem_nhds hxU, f, hf.contMDiffOn, ?_⟩
      intro y hy
      by_cases hys : y ∈ S
      · simpa only [t, ite_eq_left hys, mem_singleton_iff] using he ⟨hys, hy⟩
      · simp only [t, ite_eq_right hys, mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ ↦ 0, contMDiffOn_const, ?_⟩
      intro y hy
      simp only [t, ite_eq_right hy, mem_univ]
  obtain ⟨f, hf⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (modelWithCornersSelf ℝ (Space n)) (n := (1 : ℕ∞)) hc hlocal
  refine ⟨f, f.contMDiff.contDiff, ?_⟩
  intro x hx
  simpa only [t, ite_eq_left hx, mem_singleton_iff] using hf x

def HasC1TraceJetAt {n : ℕ} (S : Set (Space n)) (h : Space n → ℝ)
    (G : Space n → Space n) (x : Space n) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧ ∃ f : Space n → ℝ,
    ContDiffOn ℝ 1 f U ∧ EqOn f h (S ∩ U) ∧ surfaceGradient S f x = G x

lemma HasC1TraceJetAt.trace {n : ℕ} {S : Set (Space n)} {h : Space n → ℝ}
    {G : Space n → Space n} {x : Space n} (hx : HasC1TraceJetAt S h G x) :
    HasC1TraceAt S h x := by
  obtain ⟨U, hU, hxU, f, hf, he, _⟩ := hx
  exact ⟨U, hU, hxU, f, hf, he⟩

theorem exists_c1_cutoff_trace {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasC1TraceJetAt S h G x)
    (χ : Space n → ℝ) (hχ : ContDiff ℝ 1 χ)
    (hzero : ∃ U : Set (Space n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ x = 0) :
    ∃ F : Space n → ℝ, ContDiff ℝ 1 F ∧ EqOn F (fun x ↦ χ x * h x) S ∧
      EqOn (surfaceGradient S F)
        (fun x ↦ χ x • G x + h x • surfaceGradient S χ x) S := by
  have hj : ∀ x ∈ S, HasC1TraceJetAt S (fun x ↦ χ x * h x)
      (fun x ↦ χ x • G x + h x • surfaceGradient S χ x) x := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · obtain ⟨U, hU, hZU, he⟩ := hzero
      have hxU := hZU hxZ
      refine ⟨U, hU, hxU, fun _ ↦ 0, contDiffOn_const, ?_, ?_⟩
      · intro y hy
        simp only [he y hy.2, zero_mul]
      · have hχgrad : gradient χ x = 0 := by
          have heq : χ =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
            filter_upwards [hU.mem_nhds hxU] with y hy using he y hy
          simpa only [gradient_fun_const] using heq.gradient_eq
        simp only [he x hxU, zero_smul, surfaceGradient, gradient_fun_const,
          hχgrad, map_zero, Submodule.coe_zero, smul_zero, add_zero]
    · obtain ⟨U, hU, hxU, f, hf, he, hG⟩ := hreg x ⟨hx, hxZ⟩
      refine ⟨U, hU, hxU, fun y ↦ χ y * f y, hχ.contDiffOn.mul hf, ?_, ?_⟩
      · intro y hy
        exact congrArg (fun a ↦ χ y * a) (he hy)
      · rw [surfaceGradient_mul (hχ.differentiable (by simp) x)
            ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)),
          hG, he ⟨hx, hxU⟩]
  obtain ⟨F, hF, hFe⟩ := exists_c1_eqOn_of_local_trace hS
    (fun x ↦ χ x * h x) (fun x hx ↦ (hj x hx).trace)
  refine ⟨F, hF, hFe, ?_⟩
  intro x hx
  obtain ⟨U, hU, hxU, f, hf, he, hG⟩ := hj x hx
  calc
    surfaceGradient S F x = surfaceGradient S f x := by
      apply surfaceGradient_congr_trace (hF.differentiable (by simp) x)
        ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
      filter_upwards [hU.mem_nhds hxU] with y hy
      intro hys
      exact (hFe hys).trans (he ⟨hys, hy⟩).symm
    _ = _ := hG

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

lemma surfaceGradient_norm_le_fderiv {n : ℕ} (S : Set (Space n))
    (f : Space n → ℝ) (x : Space n) : ‖surfaceGradient S f x‖ ≤ ‖fderiv ℝ f x‖ := by
  calc
    _ ≤ ‖gradient f x‖ := (tangentPlane S x).norm_orthogonalProjectionOnto_apply_le _
    _ = _ := (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map _

lemma c1Mollify_surfaceGradient_tendsto {n : ℕ} (S : Set (Space n))
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (x : Space n) :
    Tendsto (fun j ↦ surfaceGradient S (c1Mollify f j) x) atTop
      (𝓝 (surfaceGradient S f x)) := by
  have hcont : Continuous (fun z : Space n →L[ℝ] ℝ ↦
      ((tangentPlane S x).orthogonalProjectionOnto
        ((InnerProductSpace.toDual ℝ (Space n)).symm z) : Space n)) := by fun_prop
  exact hcont.continuousAt.tendsto.comp (c1Mollify_fderiv_tendsto hf hc x)

lemma c1_surfaceGradient_aestronglyMeasurable {n : ℕ} (S : Set (Space n))
    (μ : Measure (Space n))
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f → AEStronglyMeasurable (surfaceGradient S f) μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    AEStronglyMeasurable (surfaceGradient S f) μ :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun j ↦ hgrad _ (c1Mollify_contDiff hf.continuous j))
    (ae_of_all _ (c1Mollify_surfaceGradient_tendsto S hf hc))

lemma c1Mollify_pair_bounded {n : ℕ} (S : Set (Space n))
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ (∀ j x, ‖c1Mollify f j x‖ ≤ M ∧
      ‖surfaceGradient S (c1Mollify f j) x‖ ≤ M) ∧
      ∀ x, ‖f x‖ ≤ M ∧ ‖surfaceGradient S f x‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := c1Mollify_uniform_bound hf hc
  refine ⟨M, hM, ?_, ?_⟩
  · intro j x
    exact ⟨(hbound j x).1, (surfaceGradient_norm_le_fderiv S _ x).trans (hbound j x).2⟩
  · intro x
    refine ⟨le_of_tendsto (c1Mollify_tendsto hf.continuous x).norm
      (Eventually.of_forall fun j ↦ (hbound j x).1), ?_⟩
    apply le_of_tendsto (c1Mollify_surfaceGradient_tendsto S hf hc x).norm
    exact Eventually.of_forall fun j ↦ (surfaceGradient_norm_le_fderiv S _ x).trans (hbound j x).2

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI

lemma bounded_tendsto_toLp_two {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {μ : Measure X} [IsFiniteMeasure μ]
    {F : ℕ → X → V} {f : X → V}
    (hF : ∀ j, MemLp (F j) 2 μ) (hf : MemLp f 2 μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ j, ∀ᵐ x ∂μ, ‖F j x‖ ≤ M)
    (hfbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ M)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun j ↦ F j x) atTop (𝓝 (f x))) :
    Tendsto (fun j ↦ (hF j).toLp (F j)) atTop (𝓝 (hf.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hF _ hf).mpr
  apply tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
    (fun index ↦ ((hF index).sub hf).aestronglyMeasurable)
  have hlim := tendsto_lintegral_of_dominated_convergence'
    (fun _ : X ↦ ENNReal.ofReal ((2 * M) ^ 2))
    (f := fun _ ↦ (0 : ℝ≥0∞))
    (F := fun j x ↦ ENNReal.ofReal (‖F j x - f x‖ ^ 2))
    (fun j ↦ ((hF j).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2
      |>.aemeasurable.ennreal_ofReal) ?_ ?_ ?_
  · simpa only [vectorEnergy, Pi.sub_apply, lintegral_zero] using hlim
  · intro j
    filter_upwards [hbound j, hfbound] with x hx hy
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    exact (norm_sub_le _ _).trans (by linarith)
  · simp only [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · filter_upwards [ht] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ((hx.sub_const (f x)).norm.pow 2)

end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem c1_compact_mem_sobolevGraph {n : ℕ} (S V : Set (Space n))
    [IsFiniteMeasure ((surfaceMeasure S).restrict V)]
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) ((surfaceMeasure S).restrict V))
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hm : MemLp f 2 ((surfaceMeasure S).restrict V))
    (hD : MemLp (surfaceGradient S f) 2 ((surfaceMeasure S).restrict V)) :
    (hm.toLp f, hD.toLp (surfaceGradient S f)) ∈ closure (smoothGradientGraph S V) := by
  obtain ⟨M, hM, hbound, hfb⟩ := c1Mollify_pair_bounded S hf hc
  have hfm : ∀ j, MemLp (c1Mollify f j) 2 ((surfaceMeasure S).restrict V) := by
    intro j
    exact MemLp.of_bound (c1Mollify_contDiff hf.continuous j).continuous.aestronglyMeasurable M
      (ae_of_all _ fun x ↦ (hbound j x).1)
  have hDm : ∀ j, MemLp (surfaceGradient S (c1Mollify f j)) 2
      ((surfaceMeasure S).restrict V) := by
    intro j
    exact MemLp.of_bound (hgrad _ (c1Mollify_contDiff hf.continuous j)) M
      (ae_of_all _ fun x ↦ (hbound j x).2)
  have ht := bounded_tendsto_toLp_two hfm hm hM.le
    (fun j ↦ ae_of_all _ fun x ↦ (hbound j x).1)
    (ae_of_all _ fun x ↦ (hfb x).1) (ae_of_all _ fun x ↦ c1Mollify_tendsto hf.continuous x)
  have hDt := bounded_tendsto_toLp_two hDm hD hM.le
    (fun j ↦ ae_of_all _ fun x ↦ (hbound j x).2)
    (ae_of_all _ fun x ↦ (hfb x).2) (ae_of_all _ fun x ↦ c1Mollify_surfaceGradient_tendsto S hf hc x)
  apply mem_closure_of_tendsto (ht.prodMk_nhds hDt)
  exact Eventually.of_forall fun j ↦ ⟨c1Mollify f j, c1Mollify_contDiff hf.continuous j,
    hfm j, hDm j, rfl⟩

theorem exists_c1_compact_trace_on_bounded {n : ℕ} (S V : Set (Space n))
    (hV : Bornology.IsBounded V) (f : Space n → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ F : Space n → ℝ, ContDiff ℝ 1 F ∧ HasCompactSupport F ∧
      EqOn F f V ∧ EqOn (surfaceGradient S F) (surfaceGradient S f) V := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hV
  let b : ContDiffBump (0 : Space n) :=
    ⟨|r| + 1, |r| + 2, by positivity, by linarith⟩
  have hb : V ⊆ Metric.ball (0 : Space n) b.rIn := by
    intro x hx
    have hx' := Metric.mem_ball.mp (hr hx)
    change dist x 0 < |r| + 1
    linarith [le_abs_self r]
  have hb1 : ContDiff ℝ 1 b := b.contDiff
  refine ⟨fun x ↦ b x * f x, hb1.mul hf, b.hasCompactSupport.mul_right, ?_, ?_⟩
  · intro x hx
    change b x * f x = f x
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall (hb hx)), one_mul]
  · intro x hx
    apply surfaceGradient_congr_trace
      ((hb1.mul hf).differentiable (by norm_num) x)
      (hf.differentiable (by norm_num) x)
    filter_upwards [b.eventuallyEq_one_of_mem_ball (hb hx)] with y hy
    intro _
    simp only [hy, Pi.one_apply, one_mul]

theorem c1_mem_sobolevGraph_bounded {n : ℕ} (S V : Set (Space n))
    (hV : Bornology.IsBounded V) (hVm : MeasurableSet V)
    [IsFiniteMeasure ((surfaceMeasure S).restrict V)]
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) ((surfaceMeasure S).restrict V))
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hm : MemLp f 2 ((surfaceMeasure S).restrict V))
    (hD : MemLp (surfaceGradient S f) 2 ((surfaceMeasure S).restrict V)) :
    (hm.toLp f, hD.toLp (surfaceGradient S f)) ∈ closure (smoothGradientGraph S V) := by
  obtain ⟨F, hF, hcF, he, hDe⟩ := exists_c1_compact_trace_on_bounded S V hV f hf
  have he' : F =ᵐ[(surfaceMeasure S).restrict V] f := by
    filter_upwards [ae_restrict_mem hVm] with x hx using he hx
  have hDe' : surfaceGradient S F =ᵐ[(surfaceMeasure S).restrict V] surfaceGradient S f := by
    filter_upwards [ae_restrict_mem hVm] with x hx using hDe hx
  let hmF := hm.ae_eq he'.symm
  let hDF := hD.ae_eq hDe'.symm
  have hp := c1_compact_mem_sobolevGraph S V hgrad hF hcF hmF hDF
  simpa only [hmF.toLp_congr hm he', hDF.toLp_congr hD hDe'] using hp

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem c1_capacity_trace_mem_sobolevGraph {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) (V : Set (Space n))
    (hV : Bornology.IsBounded V) (hVm : MeasurableSet V)
    [IsFiniteMeasure ((surfaceMeasure S).restrict V)]
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) ((surfaceMeasure S).restrict V))
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasC1TraceJetAt S h G x)
    (hh : MemLp h 2 ((surfaceMeasure S).restrict V))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict V))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(surfaceMeasure S).restrict V, ‖h x‖ ≤ M)
    (χ : ℕ → Space n → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχzero : ∀ i, ∃ U : Set (Space n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ i x = 0)
    (hχb : ∀ i, ∀ᵐ x ∂(surfaceMeasure S).restrict V, χ i x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ᵐ x ∂(surfaceMeasure S).restrict V,
      Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    (hC : ∀ i, MemLp (surfaceGradient S (χ i)) 2 ((surfaceMeasure S).restrict V))
    (hC0 : Tendsto (fun i ↦ vectorEnergy ((surfaceMeasure S).restrict V)
      (surfaceGradient S (χ i))) atTop (𝓝 0)) :
    (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V) := by
  obtain ⟨hm, hg, ht⟩ := capacity_product_pair_tendsto hh hG χ
    (fun i ↦ (hχ i).continuous.aestronglyMeasurable) hχb hχlim hM hbound
    (fun i ↦ surfaceGradient S (χ i)) hC hC0
  apply isClosed_closure.mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro i
  obtain ⟨F, hF, hFe, hFG⟩ := exists_c1_cutoff_trace hS hreg (χ i) ((hχ i).of_le (by norm_num)) (hχzero i)
  have hμS : ∀ᵐ x ∂(surfaceMeasure S).restrict V, x ∈ S :=
    ae_restrict_of_ae (ae_restrict_mem hS.measurableSet)
  have he : F =ᵐ[(surfaceMeasure S).restrict V] (fun x ↦ χ i x * h x) := by
    filter_upwards [hμS] with x hx using hFe hx
  have hge : surfaceGradient S F =ᵐ[(surfaceMeasure S).restrict V]
      (fun x ↦ χ i x • G x + h x • surfaceGradient S (χ i) x) := by
    filter_upwards [hμS] with x hx using hFG hx
  let hfmem := MemLp.ae_eq he.symm (hm i)
  let hgfmem := MemLp.ae_eq hge.symm (hg i)
  have hmem := c1_mem_sobolevGraph_bounded S V hV hVm hgrad hF hfmem hgfmem
  have heLp := (hm i).toLp_congr hfmem he.symm
  have hgeLp := (hg i).toLp_congr hgfmem hge.symm
  simpa only [heLp, hgeLp] using hmem

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
theorem HasC1TraceJetAt.comp {n : ℕ} {S : Set (Space n)}
    {h : Space n → ℝ} {G : Space n → Space n} {x : Space n}
    (hxS : x ∈ S) (hx : HasC1TraceJetAt S h G x)
    {T : ℝ → ℝ} (hT : ContDiff ℝ 1 T) :
    HasC1TraceJetAt S (T ∘ h) (fun y ↦ deriv T (h y) • G y) x := by
  obtain ⟨U, hU, hxU, f, hf, hfh, hfG⟩ := hx
  refine ⟨U, hU, hxU, T ∘ f, hT.comp_contDiffOn hf, ?_, ?_⟩
  · intro y hy
    exact congrArg T (hfh hy)
  · rw [surfaceGradient_comp ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
        (hT.differentiable (by simp)).differentiableAt, hfh ⟨hxS, hxU⟩, hfG]

theorem HasC1TraceJetAt.smoothTruncation {n : ℕ} {S : Set (Space n)}
    {W : Space n → ℝ} {D : Space n → Space n} {x : Space n}
    (hxS : x ∈ S) (hx : HasC1TraceJetAt S W D x)
    {ε : ℝ} (hε : 0 < ε) :
    HasC1TraceJetAt S (fun y ↦ smoothTruncation ε (W y))
      (fun y ↦ truncationSlope ε (W y) • truncatedGradient W D y) x := by
  simpa only [Function.comp_def, smoothTruncation_deriv,
    truncationSlope_smul_truncatedGradient W D hε] using hx.comp hxS ((smoothTruncation_contDiff ε).of_le (by norm_num))

theorem c1_surfaceGradient_memLp_on_ball {n : ℕ} {S : Set (Space n)}
    {R : ℝ} [IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R))]
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hm : AEStronglyMeasurable (surfaceGradient S φ)
      ((surfaceMeasure S).restrict (Metric.ball 0 R))) :
    MemLp (surfaceGradient S φ) 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)) := by
  have hc : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt (hφ.of_le (by norm_num)).contDiffAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space n) R).exists_bound_of_continuousOn
    hc.continuousOn
  apply MemLp.of_bound hm M
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  calc
    ‖surfaceGradient S φ x‖ ≤ ‖gradient φ x‖ := by
      calc
        _ ≤ ‖(tangentPlane S x).orthogonalProjectionOnto‖ * ‖gradient φ x‖ :=
          (tangentPlane S x).orthogonalProjectionOnto.le_opNorm _
        _ ≤ 1 * ‖gradient φ x‖ := mul_le_mul_of_nonneg_right
          (tangentPlane S x).orthogonalProjectionOnto_norm_le (norm_nonneg _)
        _ = _ := one_mul _
    _ ≤ M := hM x (Metric.ball_subset_closedBall hx)

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem c1_exists_smooth_representative_near_regular_test {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) (hZ : IsClosed Z) {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    {K : Set (Space n)} (hK : IsClosed K) (hKZ : Disjoint K Z) :
    ∃ F : Space n → ℝ, ContDiff ℝ 1 F ∧
      (∀ x ∈ S ∩ K, F x = W x ∧ surfaceGradient S F x = D x) := by
  obtain ⟨σ, hσ0, hσ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ (Space n)) hZ hK hKZ.symm (n := (⊤ : ℕ∞))
  have hσ : ContDiff ℝ 1 σ := σ.contMDiff.contDiff.of_le (by norm_num)
  obtain ⟨U, hU, hUZ, hUσ⟩ := mem_nhdsSet_iff_exists.mp hσ0
  obtain ⟨F, hF, hFW, hFD⟩ := exists_c1_cutoff_trace hS htrace σ hσ
    ⟨U, hU, hUZ, hUσ⟩
  refine ⟨F, hF, ?_⟩
  intro x hx
  have hσx : σ x = 1 := hσ1.self_of_nhdsSet x hx.2
  have hσnear : (σ : Space n → ℝ) =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
    hσ1.filter_mono (nhds_le_nhdsSet hx.2)
  have hσg : surfaceGradient S σ x = 0 := by
    have hg : gradient (σ : Space n → ℝ) x = 0 := by
      simpa only [gradient_fun_const] using hσnear.gradient_eq
    simp only [surfaceGradient, hg, map_zero, Submodule.coe_zero]
  exact ⟨by simpa only [hσx, one_mul] using hFW hx.1,
    by simpa only [hσx, one_smul, hσg, smul_zero, add_zero] using hFD hx.1⟩

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
section RegularTests
variable {n : ℕ} {S Z : Set (Space n)}
variable (hS : IsClosed S) (hZ : IsClosed Z)
variable (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))

include hfinite hgrad

theorem c1_surfaceGradient_memLp_of_compact {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    MemLp (surfaceGradient S φ) 2 (surfaceMeasure S) := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.ball (0 : Space n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let : IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite R hR⟩
  have hloc := c1_surfaceGradient_memLp_on_ball (R := R) hφ
    ((hgrad φ hφ).mono_measure Measure.restrict_le_self)
  have hh := (memLp_indicator_iff_restrict measurableSet_ball).mpr hloc
  apply hh.ae_eq
  apply ae_of_all
  intro x
  by_cases hx : x ∈ Metric.ball (0 : Space n) R
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx]
    exact (surfaceGradient_eq_zero_of_notMem_tsupport S (fun h ↦ hx (hsupp h))).symm

include hS hZ

theorem c1_regular_gradient_memLp_indicator_test {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    {φ : Space n → ℝ} (hcφ : HasCompactSupport φ) (hφZ : Disjoint (tsupport φ) Z) :
    MemLp ((tsupport φ).indicator D) 2 (surfaceMeasure S) := by
  obtain ⟨F, hF, he⟩ := c1_exists_smooth_representative_near_regular_test hS hZ htrace
    (isClosed_tsupport φ) hφZ
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.ball (0 : Space n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let : IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite R hR⟩
  have hloc : MemLp (surfaceGradient S F) 2 ((surfaceMeasure S).restrict (tsupport φ)) :=
    (c1_surfaceGradient_memLp_on_ball (R := R) hF ((hgrad F hF).mono_measure Measure.restrict_le_self)).mono_measure
      (Measure.restrict_mono_set _ hsupp)
  apply ((memLp_indicator_iff_restrict (isClosed_tsupport φ).measurableSet).mpr hloc).ae_eq
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  by_cases hxt : x ∈ tsupport φ
  · simp only [indicator_of_mem hxt, (he x ⟨hx, hxt⟩).2]
  · simp only [indicator_of_notMem hxt]

theorem c1_integrable_regular_test_pair {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφZ : Disjoint (tsupport φ) Z) :
    Integrable (fun x ↦ inner ℝ (D x) (surfaceGradient S φ x)) (surfaceMeasure S) := by
  have hD := c1_regular_gradient_memLp_indicator_test hS hZ hfinite hgrad htrace hcφ hφZ
  have hB := c1_surfaceGradient_memLp_of_compact hfinite hgrad hφ hcφ
  apply (integrable_inner_of_memLp hD hB).congr
  apply ae_of_all
  intro x
  by_cases hxt : x ∈ tsupport φ
  · simp only [indicator_of_mem hxt]
  · simp only [indicator_of_notMem hxt, surfaceGradient_eq_zero_of_notMem_tsupport S hxt,
      inner_zero_right]

end RegularTests
end RPI.Boundary

end

end OAI
