import OAI.Geometry.KahlerSplitting.MixedShell

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsMixedBox.slice_holomorphic {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W D : Set ℂ} {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc (W ×ˢ D) f) {w : ℂ} (hw : w ∈ W) :
    MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun v ↦ f (w,v)) D :=
  hf.holomorphic.comp
    (fun z _ ↦ (hasFDerivAt_prodMk_right w z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt)
    (fun _ hv ↦ ⟨hw,hv⟩)

lemma IsMixedBox.fibre_eq_of_shell {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set ℂ} {f g Fs : ℂ × ℂ → X.Carrier} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hf : IsMixedBox (S := S) c hc (U ×ˢ ball 0 b) f)
    (hg : IsMixedBox (S := S) c hc (V ×ˢ ball 0 b) g)
    (hfs : EqOn f Fs (U ×ˢ complexAnnulus a b))
    (hgs : EqOn g Fs (V ×ˢ complexAnnulus a b))
    {w v : ℂ} (hwU : w ∈ U) (hwV : w ∈ V) (hv : v ∈ ball 0 b) : f (w,v) = g (w,v) := by
  obtain ⟨z,hz⟩ := complexAnnulus_nonempty ha hab
  have he : (fun v ↦ f (w,v)) =ᶠ[𝓝 z] (fun v ↦ g (w,v)) :=
    Filter.mem_of_superset ((isOpen_complexAnnulus a b).mem_nhds hz)
      (fun y hy ↦ (hfs ⟨hwU,hy⟩).trans (hgs ⟨hwV,hy⟩).symm)
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq isOpen_ball
    (convex_ball (0:ℂ) b).isPreconnected (hf.slice_holomorphic hwU) (hg.slice_holomorphic hwV)
    (complexAnnulus_subset_ball a b hz) he hv

def MixedFillable (S : HolomorphicSplitting X r s) (c : ℂ × ℂ) (hc : c.1 ≠ c.2)
    (W : Set ℂ) (Fs : ℂ × ℂ → X.Carrier) (a b : ℝ) : Set ℂ :=
  {w | ∃ e : ℝ, 0 < e ∧ ball w e ⊆ W ∧ ∃ F : ℂ × ℂ → X.Carrier,
    IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F ∧
    EqOn F Fs (ball w e ×ˢ complexAnnulus a b)}

lemma mixedFillable_subset {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs : ℂ × ℂ → X.Carrier} {a b : ℝ} :
    MixedFillable S c hc W Fs a b ⊆ W := by
  rintro w ⟨e,he,heW,F,hF,heq⟩
  exact heW (mem_ball_self he)

lemma ball_subset_mixedFillable {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs F : ℂ × ℂ → X.Carrier} {a b e : ℝ} {w : ℂ}
    (hW : ball w e ⊆ W) (hF : IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F)
    (heq : EqOn F Fs (ball w e ×ˢ complexAnnulus a b)) :
    ball w e ⊆ MixedFillable S c hc W Fs a b := by
  intro x hx
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
  exact ⟨d,hd,hdsub.trans hW,F,hF.mono (prod_mono hdsub subset_rfl),
    heq.mono (prod_mono hdsub subset_rfl)⟩

lemma isOpen_mixedFillable {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs : ℂ × ℂ → X.Carrier} {a b : ℝ} :
    IsOpen (MixedFillable S c hc W Fs a b) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro w ⟨e,he,heW,F,hF,heq⟩
  exact Filter.mem_of_superset (ball_mem_nhds w he) (ball_subset_mixedFillable heW hF heq)

theorem glue_all_mixed_fillings {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs : ℂ × ℂ → X.Carrier} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (MixedFillable S c hc W Fs a b ×ˢ ball 0 b) F ∧
      EqOn F Fs (MixedFillable S c hc W Fs a b ×ˢ complexAnnulus a b) := by
  classical
  let A := MixedFillable S c hc W Fs a b
  choose e he heW f hf heq using (fun w : A ↦ w.property)
  let U : A → Set (ℂ × ℂ) := fun w ↦ ball (w:ℂ) (e w) ×ˢ ball 0 b
  have hU (w : A) : IsOpen (U w) := isOpen_ball.prod isOpen_ball
  have hcompat (u v : A) : EqOn (f u) (f v) (U u ∩ U v) := by
    intro z hz
    exact (hf u).fibre_eq_of_shell ha hab (hf v) (heq u) (heq v) hz.1.1 hz.2.1 hz.1.2
  obtain ⟨F,hF,hFeq⟩ := glue_mixed_boxes U hU f hf hcompat (Fs 0)
  have hUnion : (⋃ w, U w) = A ×ˢ ball 0 b := by
    ext z
    constructor
    · rintro ⟨_,⟨w,rfl⟩,hz⟩
      exact ⟨ball_subset_mixedFillable (heW w) (hf w) (heq w) hz.1,hz.2⟩
    · intro hz
      exact mem_iUnion.mpr ⟨⟨z.1,hz.1⟩,mem_ball_self (he ⟨z.1,hz.1⟩),hz.2⟩
  refine ⟨F,hUnion ▸ hF,?_⟩
  intro z hz
  let w : A := ⟨z.1,hz.1⟩
  exact (hFeq w ⟨mem_ball_self (he w),complexAnnulus_subset_ball _ _ hz.2⟩).trans
    (heq w ⟨mem_ball_self (he w),hz.2⟩)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

lemma first_affine_slope (g : KahlerMetric X) {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {f : ℂ × ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f U)
    (u w : ℂ) (C : ℝ)
    (hs : ∀ z ∈ U, metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (0,1)))
    {z : ℂ × ℂ} (hz : separatedAffine (u,0) (w,1) z ∈ U) :
    metricNorm g ((f ∘ separatedAffine (u,0) (w,1)) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ separatedAffine (u,0) (w,1)) z (1,0)) ≤
    (C * ‖w‖) * metricNorm g ((f ∘ separatedAffine (u,0) (w,1)) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ separatedAffine (u,0) (w,1)) z (0,1)) := by
  have hm := mfderiv_comp z (hf.mdifferentiableAt (hU.mem_nhds hz))
    (separatedAffine_hasFDerivAt (u,0) (w,1) z).differentiableAt.mdifferentiableAt
  rw [hm,mfderiv_eq_fderiv,(separatedAffine_hasFDerivAt (u,0) (w,1) z).fderiv]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (separatedAffine (u,0) (w,1) z)) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (separatedAffine (u,0) (w,1) z)
  change metricNorm g _ (D (separatedLinear (w,1) (1,0))) ≤
    (C * ‖w‖) * metricNorm g _ (D (separatedLinear (w,1) (0,1)))
  have h₁ : separatedLinear (w,1) (1,0) = w • (1,0) := by ext <;> simp [separatedLinear]
  have h₂ : separatedLinear (w,1) (0,1) = (0,1) := by ext <;> simp [separatedLinear]
  rw [h₁,h₂,map_smul,metricNorm_complex_smul]
  calc
    _ ≤ ‖w‖ * (C * metricNorm g _ (D (0,1))) := mul_le_mul_of_nonneg_left (hs _ hz) (norm_nonneg _)
    _ = _ := by ring

theorem radial_disk_area_bound (g : KahlerMetric X)
    {A : Set ℂ} {u : ℂ} (hA : IsOpen A) {f : ℂ × ℂ → X.Carrier} {b ρ C R R₀ : ℝ}
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f (A ×ˢ ball 0 b))
    (_hρ : 0 < ρ) (hρA : ball u ρ ⊆ A) (hC : 0 ≤ C)
    (hR : 0 < R) (hRR : R + C * ρ < R₀) (hRb : R₀ < b)
    (hs : ∀ z ∈ A ×ˢ ball 0 b,
      metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (0,1))) :
    ∀ w ∈ ball u ρ, curveArea g (fun v ↦ f (w,v)) (closedBall 0 R) ≤
      curveArea g (fun v ↦ f (u,v)) (ball 0 R₀) := by
  intro w hw
  have hw' : ‖w-u‖ < ρ := by simpa [dist_eq_norm] using hw
  let T := separatedAffine (u,0) (w-u,1)
  let U := T ⁻¹' (A ×ˢ ball 0 b)
  let D := C * ‖w-u‖
  let R' : ℝ → ℝ := fun x ↦ R₀ - D * x
  have hD : 0 ≤ D := mul_nonneg hC (norm_nonneg _)
  have hmargin : R < R₀ - D := by
    have := mul_le_mul_of_nonneg_left hw'.le hC
    dsimp [D]
    linarith
  have hT : Continuous T := continuous_iff_continuousAt.mpr fun z ↦ (separatedAffine_hasFDerivAt (u,0) (w-u,1) z).continuousAt
  have hU : IsOpen U := (hA.prod isOpen_ball).preimage hT
  have hf' : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ T) U :=
    hf.comp (fun z _ ↦ (separatedAffine_hasFDerivAt (u,0) (w-u,1) z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt)
      (fun _ hz ↦ hz)
  have hRp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ R' x := by
    have := mul_le_mul_of_nonneg_left hx.2 hD
    dsimp [R']
    linarith
  have hslices : ∀ x ∈ Icc (0:ℝ) 1, MapsTo (fun v : ℂ ↦ ((x:ℂ),v)) (closedBall 0 (R' x)) U := by
    intro x hx v hv
    change separatedAffine (u,0) (w-u,1) ((x:ℂ),v) ∈ A ×ˢ ball 0 b
    simp only [separatedAffine,zero_add,one_mul]
    constructor
    · apply hρA
      simp only [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_right (norm_nonneg (w-u)) hx.2).trans_lt hw'
    · have hv' : ‖v‖ ≤ R₀ - D*x := by simpa [R'] using hv
      have := mul_nonneg hD hx.1
      simpa only [mem_ball,dist_zero_right] using (show ‖v‖ < b by linarith)
  have hm := moving_disk_area_le_of_slices g hU isOpen_univ hf'
    (show ContDiffOn ℝ ∞ R' univ from (by fun_prop : ContDiff ℝ ∞ R').contDiffOn)
    (show (0:ℝ) ≤ 1 by norm_num) (subset_univ _) hRp
    (fun x _ ↦ by
      have hd : HasDerivAt R' (-D) x := by simpa [R'] using ((hasDerivAt_id x).const_mul D).const_sub R₀
      exact hd.deriv.le) hslices
    (fun z hz ↦ first_affine_slope g (hA.prod isOpen_ball) hf u (w-u) C hs hz)
  have hfinal : curveArea g (fun v ↦ f (w,v)) (ball 0 (R₀-D)) ≤
      curveArea g (fun v ↦ f (u,v)) (ball 0 R₀) := by
    simpa only [Function.comp_apply,T,separatedAffine,R',mul_one,mul_zero,sub_zero,zero_add,one_mul,Complex.ofReal_one,Complex.ofReal_zero,add_sub_cancel,add_zero] using hm
  exact (curveArea_mono g _ (closedBall_subset_ball hmargin)).trans hfinal

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

theorem ball_subset_of_closedBall_continuation {E : Type*} [MetricSpace E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {x : E} (hx : x ∈ A) {e : ℝ}
    (hfill : ∀ ρ : ℝ, 0 < ρ → ρ < e → ball x ρ ⊆ A → closedBall x ρ ⊆ A) :
    ball x e ⊆ A := by
  by_contra h
  obtain ⟨y,hy,hny⟩ := not_subset.mp h
  obtain ⟨z,hz,hd⟩ := hA.isClosed_compl.exists_infDist_eq_dist ⟨y,hny⟩ x
  have hpos : 0 < infDist x Aᶜ := by
    rw [hd]
    exact dist_pos.mpr (ne_of_mem_of_not_mem hx hz)
  have hlt : infDist x Aᶜ < e :=
    (infDist_le_dist_of_mem hny).trans_lt (mem_ball'.mp hy)
  apply hz
  apply hfill _ hpos hlt ball_infDist_compl_subset
  rw [mem_closedBall,dist_comm,← hd]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma mixedFillable_closedBall [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) {a b R R₀ ρ C : ℝ} (ha : 0 ≤ a)
    (haR : a < R) (hRR : R + C*ρ < R₀) (hRb : R₀ < b)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    {F : ℂ × ℂ → X.Carrier}
    (hF : IsMixedBox (S := S) c hc (MixedFillable S c hc W Fs a b ×ˢ ball 0 b) F)
    (hFs : EqOn F Fs (MixedFillable S c hc W Fs a b ×ˢ complexAnnulus a b))
    (hslope : ∀ z ∈ MixedFillable S c hc W Fs a b ×ˢ ball 0 b,
      metricNorm g (F z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) F z (1,0)) ≤
      C * metricNorm g (F z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) F z (0,1)))
    {u : ℂ} (hball : ball u ρ ⊆ MixedFillable S c hc W Fs a b)
    (hclosed : closedBall u ρ ⊆ W) :
    closedBall u ρ ⊆ MixedFillable S c hc W Fs a b := by
  have hR : 0 < R := ha.trans_lt haR
  have hRR' : R < R₀ := lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg hC hρ.le)) hRR
  have hu : u ∈ MixedFillable S c hc W Fs a b := hball (mem_ball_self hρ)
  have hfin : curveArea g (fun v ↦ F (u,v)) (ball 0 R₀) ≠ (⊤ : ℝ≥0∞) :=
    curveArea_slice_ne_top g (isOpen_mixedFillable.prod isOpen_ball) hF.holomorphic
      (fun v hv ↦ ⟨hu,closedBall_subset_ball hRb hv⟩)
  let B : ℝ≥0 := (curveArea g (fun v ↦ F (u,v)) (ball 0 R₀)).toNNReal
  have hbound := radial_disk_area_bound g isOpen_mixedFillable hF.holomorphic hρ hball hC hR hRR hRb hslope
  intro w hw
  have hw' : w ∈ closure (ball u ρ) := by rwa [closure_ball u hρ.ne']
  obtain ⟨wj,hwj,hlim⟩ := mem_closure_iff_seq_limit.mp hw'
  exact mixed_shell_fill_of_bounded_slices g h₁ h₂ hW (hclosed hw) ha haR (hRR'.trans hRb) hs
    wj (fun j ↦ mixedFillable_subset (hball (hwj j))) hlim
    (fun j v ↦ F (wj j,v)) (fun j ↦ hF.slice_holomorphic (hball (hwj j)))
    (fun j v hv ↦ hFs ⟨hball (hwj j),hv⟩) B
    (fun j ↦ by simpa only [B,ENNReal.coe_toNNReal hfin] using hbound _ (hwj j))

theorem mixedFillable_uniform_local_continuation [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (c : ℂ × ℂ) (hc : c.1 ≠ c.2)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Set ℂ) (Fs : ℂ × ℂ → X.Carrier),
      IsOpen W → IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs →
      ∀ u ∈ MixedFillable S c hc W Fs a b, ∀ e : ℝ, 0 < e → e ≤ δ →
        ball u e ⊆ W → ball u e ⊆ MixedFillable S c hc W Fs a b := by
  obtain ⟨C,hC,hCs⟩ := exists_uniform_mixed_slope g S c hc
  obtain ⟨R,haR,hRb⟩ := exists_between hab
  obtain ⟨R₀,hRR,hR₀b⟩ := exists_between hRb
  let δ := (R₀-R)/(C+1)
  have hCp : 0 < C+1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hRR) hCp
  refine ⟨δ,hδ,?_⟩
  intro W Fs hW hs u hu e he heδ heW
  obtain ⟨F,hF,hFs⟩ := glue_all_mixed_fillings (S := S) (W := W) (Fs := Fs) ha hab
  apply ball_subset_of_closedBall_continuation isOpen_mixedFillable hu
  intro ρ hρ hρe hρA
  have hρδ : ρ < δ := hρe.trans_le heδ
  have hmargin : R + C*ρ < R₀ := by
    have hh : ρ*(C+1) < R₀-R := (lt_div_iff₀ hCp).mp hρδ
    have hρpos := hρ
    nlinarith
  exact mixedFillable_closedBall g h₁ h₂ hW ha haR hmargin hR₀b hρ hC hs hF hFs
    (hCs _ _ (isOpen_mixedFillable.prod isOpen_ball) hF) hρA
    ((closedBall_subset_ball hρe).trans heW)

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

theorem subset_of_uniform_local_continuation {E : Type*} [MetricSpace E]
    {W A : Set E} (hW : IsOpen W) (hWc : IsPreconnected W) (hA : IsOpen A)
    (hAW : A ⊆ W) (hAn : A.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hcont : ∀ u ∈ A, ∀ e : ℝ, 0 < e → e ≤ δ → ball u e ⊆ W → ball u e ⊆ A) :
    W ⊆ A := by
  apply hWc.subset_of_closure_inter_subset hA
  · obtain ⟨u,hu⟩ := hAn
    exact ⟨u,hAW hu,hu⟩
  intro x hx
  obtain ⟨ε,hε,hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hx.2)
  let d := min (ε/4) (δ/4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdε : d ≤ ε/4 := min_le_left _ _
  have hdδ : d ≤ δ/4 := min_le_right _ _
  obtain ⟨u,hux,huA⟩ := mem_closure_iff.mp hx.1 (ball x d) isOpen_ball (mem_ball_self hd)
  have hux' : dist u x < d := hux
  have hballW : ball u (2*d) ⊆ W := by
    intro y hy
    apply hεW
    have hy' : dist y u < 2*d := hy
    have ht := dist_triangle y u x
    change dist y x < ε
    linarith
  apply hcont u huA (2*d) (by positivity) (by linarith) hballW
  change dist x u < 2*d
  rw [dist_comm]
  linarith

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem mixed_shell_extension [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) (hWc : IsPreconnected W) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    {w : ℂ} (hw : w ∈ W) {H : ℂ → X.Carrier}
    (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (ball 0 b))
    (hHs : ∀ v ∈ complexAnnulus a b, H v = Fs (w,v)) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (W ×ˢ ball 0 b) F ∧
      EqOn F Fs (W ×ˢ complexAnnulus a b) := by
  have hwA : w ∈ MixedFillable S c hc W Fs a b :=
    mixed_shell_fill_of_slice h₁ h₂ hW hw ha hab le_rfl hs hH hHs
  obtain ⟨δ,hδ,hcont⟩ := mixedFillable_uniform_local_continuation g h₁ h₂ c hc ha hab
  have hWA : W ⊆ MixedFillable S c hc W Fs a b :=
    subset_of_uniform_local_continuation hW hWc isOpen_mixedFillable mixedFillable_subset
      ⟨w,hwA⟩ hδ (hcont W Fs hW hs)
  have hAW : MixedFillable S c hc W Fs a b = W := Subset.antisymm mixedFillable_subset hWA
  obtain ⟨F,hF,hFs⟩ := glue_all_mixed_fillings (S := S) (c := c) (hc := hc) (W := W) (Fs := Fs) ha hab
  rw [hAW] at hF hFs
  exact ⟨F,hF,hFs⟩

theorem mixed_hartogs_extension [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W U : Set ℂ} (hW : IsOpen W) (hWc : IsPreconnected W) (hUW : U ⊆ W) (hUn : U.Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc ((U ×ˢ ball 0 b) ∪ (W ×ˢ complexAnnulus a b)) f) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (W ×ˢ ball 0 b) F ∧
      EqOn F f ((U ×ˢ ball 0 b) ∪ (W ×ˢ complexAnnulus a b)) ∧
      ∀ G : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (W ×ˢ ball 0 b) G →
        EqOn G f (W ×ˢ complexAnnulus a b) → EqOn G F (W ×ˢ ball 0 b) := by
  obtain ⟨w,hw⟩ := hUn
  have hcap : IsMixedBox (S := S) c hc (U ×ˢ ball 0 b) f := hf.mono subset_union_left
  have hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) f := hf.mono subset_union_right
  obtain ⟨F,hF,hFs⟩ := mixed_shell_extension g h₁ h₂ hW hWc ha hab hs (hUW hw)
    (hcap.slice_holomorphic hw) (fun _ _ ↦ rfl)
  refine ⟨F,hF,?_,?_⟩
  · intro z hz
    rcases hz with hz|hz
    · exact hF.fibre_eq_of_shell ha hab hcap hFs (fun _ _ ↦ rfl) (hUW hz.1) hz.1 hz.2
    · exact hFs hz
  · intro G hG hGs z hz
    exact hG.fibre_eq_of_shell ha hab hF hGs hFs hz.1 hz.1 hz.2

end UniversalCoverSplitting

end

end OAI
