import OAI.Geometry.KahlerSplitting.Superellipsoids

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem box_axes_germ_unique (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsBox S (U ×ˢ V) f) (hg : IsBox S (U ×ˢ V) g)
    (p q : ℂ) (hp : p ∈ U) (hq : q ∈ V)
    (heq₁ : ∀ z ∈ U, f (z,q) = g (z,q)) (heq₂ : ∀ z ∈ V, f (p,z) = g (p,z)) :
    f =ᶠ[𝓝 (p,q)] g := by
  obtain ⟨e,het,_⟩ := exists_splittingChart S h₁ h₂ (f (p,q))
  have hpp : (p,q) ∈ U ×ˢ V := ⟨hp,hq⟩
  have hfn := (hf.1.continuousOn.continuousAt ((hU.prod hV).mem_nhds hpp))
    (e.chart.open_source.mem_nhds het)
  have hgn := (hg.1.continuousOn.continuousAt ((hU.prod hV).mem_nhds hpp))
    (e.chart.open_source.mem_nhds ((heq₁ p hp) ▸ het))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp (inter_mem ((hU.prod hV).mem_nhds hpp) (inter_mem hfn hgn))
  have hprod : ball p a ×ˢ ball q a = ball (p,q) a := ball_prod_same _ _ _
  have hsub₁ : ball p a ⊆ U := by
    intro z hz
    exact (hasub (hprod ▸ (show (z,q) ∈ ball p a ×ˢ ball q a from ⟨hz,mem_ball_self ha⟩))).1.1
  have hsub₂ : ball q a ⊆ V := by
    intro z hz
    exact (hasub (hprod ▸ (show (p,z) ∈ ball p a ×ˢ ball q a from ⟨mem_ball_self ha,hz⟩))).1.2
  have hm (z : ℂ × ℂ) (hz : z ∈ ball p a ×ˢ ball q a) :
      f z ∈ e.chart.source ∧ g z ∈ e.chart.source := (hasub (hprod ▸ hz)).2
  have hbsub : ball p a ×ˢ ball q a ⊆ U ×ˢ V := prod_mono hsub₁ hsub₂
  have hfb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball q a) f from ⟨hf.1.mono hbsub,fun z hz ↦ hf.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).1)
  have hgb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball q a) g from ⟨hg.1.mono hbsub,fun z hz ↦ hg.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).2)
  filter_upwards [ball_mem_nhds (p,q) ha] with z hz
  have hzz : z ∈ ball p a ×ˢ ball q a := hprod.symm ▸ hz
  apply e.chart.injOn (hm z hzz).1 (hm z hzz).2
  have hfe := separated_eq_axes isOpen_ball isOpen_ball (convex_ball p a).isPreconnected
    (convex_ball q a).isPreconnected hfb.1 hfb.2 hzz.1 (mem_ball_self ha) hzz.2 (mem_ball_self ha)
  have hge := separated_eq_axes isOpen_ball isOpen_ball (convex_ball p a).isPreconnected
    (convex_ball q a).isPreconnected hgb.1 hgb.2 hzz.1 (mem_ball_self ha) hzz.2 (mem_ball_self ha)
  change (e.chart ∘ f) z = (e.chart ∘ g) z
  rw [hfe,hge]
  simp only [Function.comp_apply,heq₁ z.1 (hsub₁ hzz.1),heq₂ z.2 (hsub₂ hzz.2)]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma horizontal_axis_boundary_extension (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S))
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    {O : Set ℂ} (hO : IsOpen O) {α : ℂ → X.Carrier} (hα : IsHorizontalCurve S O α)
    {p : ℂ} (hp : p ∈ O) (hpc : p ∈ closure {z : ℂ | (z,0) ∈ U})
    (haxis : ∀ z ∈ O, (z,0) ∈ U → f (z,0) = α z) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ (p,0) ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ U) := by
  obtain ⟨e,hep,_⟩ := exists_splittingChart S h₁ h₂ (α p)
  have hαn := (hα.1.continuousOn.continuousAt (hO.mem_nhds hp)) (e.chart.open_source.mem_nhds hep)
  obtain ⟨d,hd,hdO⟩ := Metric.mem_nhds_iff.mp (inter_mem (hO.mem_nhds hp) hαn)
  have hdsub : ball p d ⊆ O := fun _ hz ↦ (hdO hz).1
  have hdae : MapsTo α (ball p d) e.chart.source := fun _ hz ↦ (hdO hz).2
  obtain ⟨q,hq,hqp⟩ := mem_closure_iff_nhds.mp hpc (ball p d) (ball_mem_nhds p hd)
  have hqe : f (q,0) ∈ e.chart.source := (haxis q (hdsub hq) hqp) ▸ hdae hq
  have hfn := (hf.1.continuousOn.continuousAt (hU.mem_nhds hqp)) (e.chart.open_source.mem_nhds hqe)
  obtain ⟨a,ha,haV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hqp) hfn)
  have hβmap (z : ℂ) (hz : z ∈ ball (0:ℂ) a) : (q,z) ∈ U ∧ f (q,z) ∈ e.chart.source := by
    apply haV
    rw [← ball_prod_same]
    exact ⟨mem_ball_self ha,hz⟩
  let β : ℂ → X.Carrier := fun z ↦ f (q,z)
  have hβ : IsVerticalCurve S (ball 0 a) β := hf.vertical_slice hU q (fun z hz ↦ (hβmap z hz).1)
  let V := ball p d ×ˢ ball (0:ℂ) a
  let F : ℂ × ℂ → X.Carrier := fun z ↦ e.chart.symm ((e.chart (α z.1)).1,(e.chart (β z.2)).2)
  have hF : IsBox S V F := e.mix_curves isOpen_ball isOpen_ball (hα.1.mono hdsub)
    hβ.1 hdae (fun z hz ↦ (hβmap z hz).2)
  have haxes := e.mix_curves_axes isOpen_ball isOpen_ball (convex_ball p d).isPreconnected
    (convex_ball (0:ℂ) a).isPreconnected (hα.mono hdsub) hβ hdae (fun z hz ↦ (hβmap z hz).2)
    hq (mem_ball_self ha) (haxis q (hdsub hq) hqp).symm
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hqc : (q,0) ∈ V ∩ U := ⟨⟨hq,mem_ball_self ha⟩,hqp⟩
  obtain ⟨b,hb,hbV⟩ := Metric.mem_nhds_iff.mp ((hVo.inter hU).mem_nhds hqc)
  have hbsub : ball q b ×ˢ ball (0:ℂ) b ⊆ V ∩ U := by rwa [ball_prod_same]
  have hFg : F =ᶠ[𝓝 (q,0)] f := by
    apply box_axes_germ_unique h₁ h₂ isOpen_ball isOpen_ball
      (hF.mono (hbsub.trans inter_subset_left)) (hf.mono (hbsub.trans inter_subset_right)) q 0
      (mem_ball_self hb) (mem_ball_self hb)
    · intro z hz
      have hm := hbsub (show (z,0) ∈ ball q b ×ˢ ball (0:ℂ) b from ⟨hz,mem_ball_self hb⟩)
      exact (haxes.1 z hm.1.1).trans (haxis z (hdsub hm.1.1) hm.2).symm
    · intro z hz
      have hm := hbsub (show (q,z) ∈ ball q b ×ˢ ball (0:ℂ) b from ⟨mem_ball_self hb,hz⟩)
      exact haxes.2 z hm.1.2
  refine ⟨V,hVo,⟨mem_ball_self hd,mem_ball_self ha⟩,F,hF,?_⟩
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hVo.inter hU)
    (((convex_ball p d).prod (convex_ball (0:ℂ) a)).inter hUc).isPreconnected
    (hF.1.mono inter_subset_left) (hf.1.mono inter_subset_right) hqc hFg

lemma vertical_axis_boundary_extension (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S))
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    {O : Set ℂ} (hO : IsOpen O) {α : ℂ → X.Carrier} (hα : IsVerticalCurve S O α)
    {p : ℂ} (hp : p ∈ O) (hpc : p ∈ closure {z : ℂ | (0,z) ∈ U})
    (haxis : ∀ z ∈ O, (0,z) ∈ U → f (0,z) = α z) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ (0,p) ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ U) := by
  obtain ⟨e,hep,_⟩ := exists_splittingChart S h₁ h₂ (α p)
  have hαn := (hα.1.continuousOn.continuousAt (hO.mem_nhds hp)) (e.chart.open_source.mem_nhds hep)
  obtain ⟨d,hd,hdO⟩ := Metric.mem_nhds_iff.mp (inter_mem (hO.mem_nhds hp) hαn)
  have hdsub : ball p d ⊆ O := fun _ hz ↦ (hdO hz).1
  have hdae : MapsTo α (ball p d) e.chart.source := fun _ hz ↦ (hdO hz).2
  obtain ⟨q,hq,hqp⟩ := mem_closure_iff_nhds.mp hpc (ball p d) (ball_mem_nhds p hd)
  have hqe : f (0,q) ∈ e.chart.source := (haxis q (hdsub hq) hqp) ▸ hdae hq
  have hfn := (hf.1.continuousOn.continuousAt (hU.mem_nhds hqp)) (e.chart.open_source.mem_nhds hqe)
  obtain ⟨a,ha,haV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hqp) hfn)
  have hβmap (z : ℂ) (hz : z ∈ ball (0:ℂ) a) : (z,q) ∈ U ∧ f (z,q) ∈ e.chart.source := by
    apply haV
    rw [← ball_prod_same]
    exact ⟨hz,mem_ball_self ha⟩
  let β : ℂ → X.Carrier := fun z ↦ f (z,q)
  have hβ : IsHorizontalCurve S (ball 0 a) β := hf.horizontal_slice hU q (fun z hz ↦ (hβmap z hz).1)
  let V := ball (0:ℂ) a ×ˢ ball p d
  let F : ℂ × ℂ → X.Carrier := fun z ↦ e.chart.symm ((e.chart (β z.1)).1,(e.chart (α z.2)).2)
  have hF : IsBox S V F := e.mix_curves isOpen_ball isOpen_ball hβ.1 (hα.1.mono hdsub)
    (fun z hz ↦ (hβmap z hz).2) hdae
  have haxes := e.mix_curves_axes isOpen_ball isOpen_ball (convex_ball (0:ℂ) a).isPreconnected
    (convex_ball p d).isPreconnected hβ (hα.mono hdsub) (fun z hz ↦ (hβmap z hz).2) hdae
    (mem_ball_self ha) hq (haxis q (hdsub hq) hqp)
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hqc : (0,q) ∈ V ∩ U := ⟨⟨mem_ball_self ha,hq⟩,hqp⟩
  obtain ⟨b,hb,hbV⟩ := Metric.mem_nhds_iff.mp ((hVo.inter hU).mem_nhds hqc)
  have hbsub : ball (0:ℂ) b ×ˢ ball q b ⊆ V ∩ U := by rwa [ball_prod_same]
  have hFg : F =ᶠ[𝓝 (0,q)] f := by
    apply box_axes_germ_unique h₁ h₂ isOpen_ball isOpen_ball
      (hF.mono (hbsub.trans inter_subset_left)) (hf.mono (hbsub.trans inter_subset_right)) 0 q
      (mem_ball_self hb) (mem_ball_self hb)
    · intro z hz
      have hm := hbsub (show (z,q) ∈ ball (0:ℂ) b ×ˢ ball q b from ⟨hz,mem_ball_self hb⟩)
      exact haxes.1 z hm.1.1
    · intro z hz
      have hm := hbsub (show (0,z) ∈ ball (0:ℂ) b ×ˢ ball q b from ⟨mem_ball_self hb,hz⟩)
      exact (haxes.2 z hm.1.2).trans (haxis z (hdsub hm.1.2) hm.2).symm
  refine ⟨V,hVo,⟨mem_ball_self ha,mem_ball_self hd⟩,F,hF,?_⟩
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hVo.inter hU)
    (((convex_ball (0:ℂ) a).prod (convex_ball p d)).inter hUc).isPreconnected
    (hF.1.mono inter_subset_left) (hf.1.mono inter_subset_right) hqc hFg

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superPotential_norm_bound {m : ℕ} (hm : 0 < m) {z : ℂ × ℂ} {a : ℝ}
    (hz : superPotential m z ≤ a) : ‖z‖ ≤ max a 1 + 1 := by
  have hb (w : ℂ) (hw : Complex.normSq w ^ m ≤ a) : ‖w‖ ≤ max a 1 + 1 := by
    by_cases h : ‖w‖ ≤ 1
    · linarith [le_max_right a 1]
    have hh : 1 ≤ Complex.normSq w := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have hpow := le_self_pow₀ hh hm.ne'
    rw [Complex.normSq_eq_norm_sq] at hpow hw
    nlinarith [le_max_left a 1,le_max_right a 1,norm_nonneg w]
  exact max_le (hb z.1 (le_trans (le_add_of_nonneg_right
    (pow_nonneg (Complex.normSq_nonneg z.2) m)) hz))
    (hb z.2 (le_trans (le_add_of_nonneg_left
      (pow_nonneg (Complex.normSq_nonneg z.1) m)) hz))

lemma superSublevel_compact {m : ℕ} (hm : 0 < m) (a : ℝ) :
    IsCompact {z | superPotential m z ≤ a} := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_le (superPotential_contDiff m (k := 0)).continuous continuous_const,?_⟩
  apply (isBounded_closedBall (x := (0:ℂ × ℂ)) (r := max a 1+1)).subset
  intro z hz
  rw [mem_closedBall,dist_zero_right]
  exact superPotential_norm_bound hm hz

lemma superPotential_radial_lt {m : ℕ} (hm : 0 < m) {a t : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (ht1 : t < 1) {z : ℂ × ℂ} (hz : superPotential m z ≤ a) :
    t • z ∈ superDomain m a := by
  change superPotential m (t • z) < a
  rw [superPotential_smul]
  have htP : t^(2*m) < 1 := pow_lt_one₀ ht ht1 (by omega)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz (pow_nonneg ht _)) (by nlinarith)

lemma superDomain_closure {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    closure (superDomain m a) = {z | superPotential m z ≤ a} := by
  apply Subset.antisymm
  · exact closure_minimal (fun z (h : superPotential m z < a) ↦ h.le)
      (isClosed_le (superPotential_contDiff m (k := 0)).continuous continuous_const)
  intro z hz
  have ht : Tendsto (fun t : ℝ ↦ t • z) (𝓝[<] 1) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ ↦ t • (z : ℂ × ℂ)) := continuous_id.smul continuous_const
    have hh := hc.continuousAt (x := (1:ℝ)) |>.tendsto
    rw [one_smul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with t ht ht0
  exact superPotential_radial_lt hm ha ht0.le ht hz

lemma superDomain_frontier {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    frontier (superDomain m a) = {z | superPotential m z = a} := by
  rw [frontier, (superDomain_open m a).interior_eq, superDomain_closure hm ha]
  ext z
  change (superPotential m z ≤ a ∧ ¬superPotential m z < a) ↔ superPotential m z = a
  rw [not_lt]
  exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le,h.ge⟩⟩

lemma superDomain_axis_closure {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a)
    {p : ℂ} (hp : superPotential m (p,0) ≤ a) :
    p ∈ closure {z : ℂ | (z,0) ∈ superDomain m a} := by
  have ht : Tendsto (fun t : ℝ ↦ t • p) (𝓝[<] 1) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ ↦ t • (p : ℂ)) := continuous_id.smul continuous_const
    have hh := hc.continuousAt (x := (1:ℝ)) |>.tendsto
    rw [one_smul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with t ht ht0
  simpa only [Prod.smul_mk,smul_zero] using superPotential_radial_lt hm ha ht0.le ht hp

lemma superDomain_vertical_axis_closure {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a)
    {p : ℂ} (hp : superPotential m (0,p) ≤ a) :
    p ∈ closure {z : ℂ | (0,z) ∈ superDomain m a} := by
  have ht : Tendsto (fun t : ℝ ↦ t • p) (𝓝[<] 1) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ ↦ t • (p : ℂ)) := continuous_id.smul continuous_const
    have hh := hc.continuousAt (x := (1:ℝ)) |>.tendsto
    rw [one_smul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with t ht ht0
  simpa only [Prod.smul_mk,smul_zero] using superPotential_radial_lt hm ha ht0.le ht hp

lemma superSublevel_subset_bidisk {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : a < 1) :
    {z | superPotential m z ≤ a} ⊆ ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
  intro z hz
  exact superDomain_subset_bidisk hm (le_refl 1) (lt_of_le_of_lt hz ha)

lemma superSublevel_widen {m : ℕ} (hm : 0 < m) {a : ℝ} {W : Set (ℂ × ℂ)}
    (hW : IsOpen W) (hsub : {z | superPotential m z ≤ a} ⊆ W) :
    ∃ b : ℝ, a < b ∧ superDomain m b ⊆ W := by
  let K := {z | superPotential m z ≤ a+1} \ W
  have hK : IsCompact K := (superSublevel_compact hm (a+1)).diff hW
  by_cases hne : K.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne (superPotential_contDiff m (k := 0)).continuous.continuousOn
    have hap : a < superPotential m p := by
      by_contra h
      exact hp.2 (hsub (le_of_not_gt h))
    refine ⟨min (superPotential m p) (a+1),lt_min hap (by linarith),?_⟩
    intro z hz
    change superPotential m z < _ at hz
    by_contra h
    exact not_lt_of_ge (hmin ⟨le_of_lt (lt_of_lt_of_le hz (min_le_right _ _)),h⟩)
      (lt_of_lt_of_le hz (min_le_left _ _))
  · refine ⟨a+1,by linarith,?_⟩
    intro z hz
    change superPotential m z < _ at hz
    by_contra h
    exact hne ⟨z,hz.le,h⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma segment_meets_inter_balls {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : E} {r s : ℝ} (hi : (ball p r ∩ ball q s).Nonempty) :
    (segment ℝ p q ∩ (ball p r ∩ ball q s)).Nonempty := by
  obtain ⟨x,hxp,hxq⟩ := hi
  have hr : 0 < r := (dist_nonneg : 0 ≤ dist x p).trans_lt hxp
  have hs : 0 < s := (dist_nonneg : 0 ≤ dist x q).trans_lt hxq
  have hd : dist p q < r+s := lt_of_le_of_lt (dist_triangle p x q)
    (add_lt_add (by simpa only [mem_ball,dist_comm] using hxp) hxq)
  have hrs : 0 < r+s := add_pos hr hs
  let t : ℝ := r/(r+s)
  have ht : 0 < t := div_pos hr hrs
  have ht1 : t < 1 := (div_lt_one hrs).mpr (by linarith)
  have heq : 1-t = s/(r+s) := by dsimp [t]; field_simp; ring
  refine ⟨AffineMap.lineMap p q t,lineMap_mem_segment ℝ p q ⟨ht.le,ht1.le⟩,?_,?_⟩
  · rw [mem_ball,dist_lineMap_left,Real.norm_eq_abs,abs_of_pos ht]
    have h := mul_lt_mul_of_pos_left hd ht
    have he : t*(r+s)=r := by dsimp [t]; field_simp
    rwa [he] at h
  · rw [mem_ball,dist_lineMap_right,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ht1),heq]
    have h := mul_lt_mul_of_pos_left hd (div_pos hs hrs)
    have he : s/(r+s)*(r+s)=s := by field_simp
    rwa [he] at h

lemma convex_boundary_ball_overlap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) {p q : E} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hi : (ball p r ∩ ball q s).Nonempty) :
    ((ball p r ∩ ball q s) ∩ U).Nonempty := by
  obtain ⟨x,hxs,hxi⟩ := segment_meets_inter_balls hi
  have hxc := hU.closure.segment_subset hp hq hxs
  obtain ⟨y,hyi,hyU⟩ := mem_closure_iff_nhds.mp hxc (ball p r ∩ ball q s)
    ((isOpen_ball.inter isOpen_ball).mem_nhds hxi)
  exact ⟨y,hyi,hyU⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma box_extend_closure {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (hext : ∀ p ∈ frontier U, ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ U)) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ closure U ⊆ W ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S W F ∧ EqOn F f U := by
  classical
  have hb (p : frontier U) : ∃ a : ℝ, 0 < a ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S (ball (p:ℂ × ℂ) a) F ∧
        EqOn F f (ball (p:ℂ × ℂ) a ∩ U) := by
    obtain ⟨V,hV,hp,F,hF,he⟩ := hext p p.property
    obtain ⟨a,ha,haV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hp)
    exact ⟨a,ha,F,hF.mono haV,he.mono (inter_subset_inter_left U haV)⟩
  choose a ha G hG hGf using hb
  have hGG (p q : frontier U) : EqOn (G p) (G q) (ball (p:ℂ × ℂ) (a p) ∩ ball (q:ℂ × ℂ) (a q)) := by
    by_cases hne : (ball (p:ℂ × ℂ) (a p) ∩ ball (q:ℂ × ℂ) (a q)).Nonempty
    · obtain ⟨z,hzi,hzU⟩ := convex_boundary_ball_overlap hUc
        (frontier_subset_closure p.property) (frontier_subset_closure q.property) hne
      apply holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
        (isOpen_ball.inter isOpen_ball) ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
        ((hG p).1.mono inter_subset_left) ((hG q).1.mono inter_subset_right) hzi
      filter_upwards [(isOpen_ball.inter isOpen_ball |>.inter hU).mem_nhds ⟨hzi,hzU⟩] with w hw
      exact (hGf p ⟨hw.1.1,hw.2⟩).trans (hGf q ⟨hw.1.2,hw.2⟩).symm
    · intro z hz
      exact (hne ⟨z,hz⟩).elim
  let V : Option (frontier U) → Set (ℂ × ℂ)
    | none => U
    | some p => ball (p:ℂ × ℂ) (a p)
  let G' : Option (frontier U) → ℂ × ℂ → X.Carrier
    | none => f
    | some p => G p
  have hVo : ∀ i, IsOpen (V i) := by intro i; cases i with
    | none => exact hU
    | some p => exact isOpen_ball
  have hGb : ∀ i, IsBox S (V i) (G' i) := by intro i; cases i with
    | none => exact hf
    | some p => exact hG p
  have hcompat : ∀ i j, EqOn (G' i) (G' j) (V i ∩ V j) := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact fun _ _ ↦ rfl
      | some q => exact fun z hz ↦ (hGf q ⟨hz.2,hz.1⟩).symm
    | some p =>
      cases j with
      | none => exact hGf p
      | some q => exact hGG p q
  obtain ⟨F,hF,he⟩ := glue_boxes V hVo G' hGb hcompat (f 0)
  refine ⟨⋃ i, V i,isOpen_iUnion hVo,?_,F,hF,he none⟩
  intro p hp
  by_cases hpU : p ∈ U
  · exact mem_iUnion.mpr ⟨none,hpU⟩
  · have hpf : p ∈ frontier U := ⟨hp,by simpa only [hU.interior_eq] using hpU⟩
    exact mem_iUnion.mpr ⟨some ⟨p,hpf⟩,mem_ball_self (ha ⟨p,hpf⟩)⟩

end UniversalCoverSplitting

end

end OAI
