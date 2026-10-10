import OAI.Geometry.KahlerSplitting.AxisContinuation

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

lemma superDomain_axes_of_eventually {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S (superDomain m a) f)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S (ball (0:ℂ) 1) α)
    (hβ : IsVerticalCurve S (ball (0:ℂ) 1) β)
    (he₁ : (fun z : ℂ ↦ f (z,0)) =ᶠ[𝓝 0] α)
    (he₂ : (fun z : ℂ ↦ f (0,z)) =ᶠ[𝓝 0] β) :
    (∀ z, (z,0) ∈ superDomain m a → f (z,0)=α z) ∧
    (∀ z, (0,z) ∈ superDomain m a → f (0,z)=β z) := by
  let L₁ : ℂ →L[ℝ] ℂ × ℂ := (ContinuousLinearMap.id ℝ ℂ).prod 0
  let L₂ : ℂ →L[ℝ] ℂ × ℂ := (0:ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)
  have hD₁ : IsOpen {z : ℂ | (z,0) ∈ superDomain m a} := (superDomain_open m a).preimage L₁.continuous
  have hD₂ : IsOpen {z : ℂ | (0,z) ∈ superDomain m a} := (superDomain_open m a).preimage L₂.continuous
  have hC₁ : Convex ℝ {z : ℂ | (z,0) ∈ superDomain m a} := (superDomain_convex m a).linear_preimage L₁.toLinearMap
  have hC₂ : Convex ℝ {z : ℂ | (0,z) ∈ superDomain m a} := (superDomain_convex m a).linear_preimage L₂.toLinearMap
  constructor
  · exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq hD₁ hC₁.isPreconnected
      (hf.horizontal_slice (superDomain_open m a) 0 (fun _ hz ↦ hz)).1
      (hα.1.mono (fun _ hz ↦ (superDomain_subset_bidisk hm ha1 hz).1))
      (show (0:ℂ) ∈ {z : ℂ | (z,0) ∈ superDomain m a} from superDomain_zero hm ha) he₁
  · exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq hD₂ hC₂.isPreconnected
      (hf.vertical_slice (superDomain_open m a) 0 (fun _ hz ↦ hz)).1
      (hβ.1.mono (fun _ hz ↦ (superDomain_subset_bidisk hm ha1 hz).2))
      (show (0:ℂ) ∈ {z : ℂ | (0,z) ∈ superDomain m a} from superDomain_zero hm ha) he₂

lemma superDomain_full_boundary [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {m : ℕ} (hm : 0 < m)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S (superDomain m a) f)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S (ball (0:ℂ) 1) α)
    (hβ : IsVerticalCurve S (ball (0:ℂ) 1) β)
    (he₁ : ∀ z, (z,0) ∈ superDomain m a → f (z,0)=α z)
    (he₂ : ∀ z, (0,z) ∈ superDomain m a → f (0,z)=β z)
    {p : ℂ × ℂ} (hp : p ∈ frontier (superDomain m a)) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ superDomain m a) := by
  have hpa : superPotential m p = a := by rwa [superDomain_frontier hm ha] at hp
  have hpD := superSublevel_subset_bidisk hm ha1 (show superPotential m p ≤ a from hpa.le)
  rcases p with ⟨u,v⟩
  by_cases hv : v = 0
  · subst v
    exact horizontal_axis_boundary_extension h₁ h₂ (superDomain_open m a) (superDomain_convex m a) hf
      isOpen_ball hα hpD.1 (superDomain_axis_closure hm ha hpa.le) (fun z _ hz ↦ he₁ z hz)
  by_cases hu : u = 0
  · subst u
    exact vertical_axis_boundary_extension h₁ h₂ (superDomain_open m a) (superDomain_convex m a) hf
      isOpen_ball hβ hpD.2 (superDomain_vertical_axis_closure hm ha hpa.le) (fun z _ hz ↦ he₂ z hz)
  exact superDomain_mixed_boundary g h₁ h₂ hm ha hf hpa hu hv

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma super_box_maximal {m : ℕ} (hm : 0 < m) (f₀ : ℂ × ℂ → X.Carrier)
    (hini : ∃ a : ℝ, 0 < a ∧ ∃ f : ℂ × ℂ → X.Carrier,
      IsBox S (superDomain m a) f ∧ f =ᶠ[𝓝 0] f₀)
    (hforward : ∀ a : ℝ, 0 < a → a < 1 → ∀ f : ℂ × ℂ → X.Carrier,
      IsBox S (superDomain m a) f → f =ᶠ[𝓝 0] f₀ →
      ∃ b : ℝ, a < b ∧ ∃ F : ℂ × ℂ → X.Carrier,
        IsBox S (superDomain m b) F ∧ F =ᶠ[𝓝 0] f₀) :
    ∃ f : ℂ × ℂ → X.Carrier, IsBox S (superDomain m 1) f ∧ f =ᶠ[𝓝 0] f₀ := by
  classical
  let T : Set ℝ := {a | 0 < a ∧ a ≤ 1 ∧ ∃ f : ℂ × ℂ → X.Carrier,
    IsBox S (superDomain m a) f ∧ f =ᶠ[𝓝 0] f₀}
  obtain ⟨a₀,ha₀,f,hf,hfg⟩ := hini
  have hTne : T.Nonempty := ⟨min a₀ 1,lt_min ha₀ (by norm_num),min_le_right _ _,f,
    hf.mono (superDomain_mono m (min_le_left _ _)),hfg⟩
  have hTbdd : BddAbove T := ⟨1,fun _ h ↦ h.2.1⟩
  let A := sSup T
  have hA : 0 < A := lt_csSup_of_lt hTbdd hTne.choose_spec hTne.choose_spec.1
  have hA1 : A ≤ 1 := csSup_le hTne (fun _ h ↦ h.2.1)
  have hfchoose (a : T) : ∃ f : ℂ × ℂ → X.Carrier,
      IsBox S (superDomain m a) f ∧ f =ᶠ[𝓝 0] f₀ := a.property.2.2
  choose F hF hF₀ using hfchoose
  have hcompat (a b : T) : EqOn (F a) (F b) (superDomain m a ∩ superDomain m b) := by
    apply holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      ((superDomain_open m a).inter (superDomain_open m b))
      (((superDomain_convex m a).inter (superDomain_convex m b)).isPreconnected)
      ((hF a).1.mono inter_subset_left) ((hF b).1.mono inter_subset_right)
      (show (0:ℂ × ℂ) ∈ superDomain m a ∩ superDomain m b from
        ⟨superDomain_zero hm a.property.1,superDomain_zero hm b.property.1⟩)
      ((hF₀ a).trans (hF₀ b).symm)
  obtain ⟨G,hG,hGF⟩ := glue_boxes (fun a : T ↦ superDomain m a)
    (fun a ↦ superDomain_open m a) F hF hcompat (f₀ 0)
  have hUnion : (⋃ a : T, superDomain m a) = superDomain m A := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha⟩ := mem_iUnion.mp hz
      exact superDomain_mono m (le_csSup hTbdd a.property) ha
    · intro hz
      obtain ⟨a,ha,haP⟩ := exists_lt_of_lt_csSup hTne hz
      exact mem_iUnion.mpr ⟨⟨a,ha⟩,haP⟩
  have hGb : IsBox S (superDomain m A) G := hUnion ▸ hG
  let a : T := ⟨hTne.choose,hTne.choose_spec⟩
  have hGg : G =ᶠ[𝓝 0] f₀ := by
    apply EventuallyEq.trans _ (hF₀ a)
    exact mem_of_superset ((superDomain_open m a).mem_nhds (superDomain_zero hm a.property.1)) (hGF a)
  have hAeq : A = 1 := by
    by_contra hne
    obtain ⟨b,hb,H,hH,hH₀⟩ := hforward A hA (lt_of_le_of_ne hA1 hne) G hGb hGg
    have hmin : min b 1 ∈ T := ⟨lt_min (hA.trans hb) (by norm_num),min_le_right _ _,H,
      hH.mono (superDomain_mono m (min_le_left _ _)),hH₀⟩
    have hle : min b 1 ≤ A := le_csSup hTbdd hmin
    have hlt : A < min b 1 := lt_min hb (lt_of_le_of_ne hA1 hne)
    exact not_lt_of_ge hle hlt
  exact ⟨G,hAeq ▸ hGb,hGg⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superSublevel_zero {m : ℕ} (hm : 0 < m) :
    {z | superPotential m z ≤ 0} = {(0:ℂ × ℂ)} := by
  ext z
  constructor
  · intro hz
    have h₁ : Complex.normSq z.1 ^ m = 0 := by
      have h1 := pow_nonneg (Complex.normSq_nonneg z.1) m
      have h2 := pow_nonneg (Complex.normSq_nonneg z.2) m
      change Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m ≤ 0 at hz
      linarith
    have h₂ : Complex.normSq z.2 ^ m = 0 := by
      have h1 := pow_nonneg (Complex.normSq_nonneg z.1) m
      have h2 := pow_nonneg (Complex.normSq_nonneg z.2) m
      change Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m ≤ 0 at hz
      linarith
    exact Prod.ext (Complex.normSq_eq_zero.mp ((pow_eq_zero_iff hm.ne').mp h₁)) (Complex.normSq_eq_zero.mp ((pow_eq_zero_iff hm.ne').mp h₂))
  · intro hz
    change superPotential m z ≤ 0
    rw [mem_singleton_iff.mp hz,superPotential_zero hm]

lemma superDomain_small {m : ℕ} (hm : 0 < m) {U : Set (ℂ × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ a : ℝ, 0 < a ∧ superDomain m a ⊆ U := by
  apply superSublevel_widen hm hU
  rw [superSublevel_zero hm]
  exact singleton_subset_iff.mpr h0

lemma superDomain_exhaustion :
    (⋃ m : {m : ℕ // 0 < m}, superDomain m 1) = ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨m,hm⟩ := mem_iUnion.mp hz
    exact superDomain_subset_bidisk m.property (le_refl 1) hm
  intro z hz
  have hn₁ : Complex.normSq z.1 < 1 := by
    have hh : ‖z.1‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.1
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z.1]
  have hn₂ : Complex.normSq z.2 < 1 := by
    have hh : ‖z.2‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.2
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z.2]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Complex.normSq_nonneg z.1) hn₁).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one (Complex.normSq_nonneg z.2) hn₂)
  have hev : ∀ᶠ m : ℕ in atTop, superPotential m z < 1 :=
    ht (Iio_mem_nhds (show (0:ℝ)+0 < 1 by norm_num))
  obtain ⟨m,hm,hPm⟩ := (eventually_gt_atTop (0:ℕ) |>.and hev).exists
  exact mem_iUnion.mpr ⟨⟨m,hm⟩,hPm⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem disk_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S (ball (0:ℂ) 1) α)
    (hβ : IsVerticalCurve S (ball (0:ℂ) 1) β) (hbase : α 0 = β 0) :
    ∃ F : ℂ × ℂ → X.Carrier, IsBox S (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) F ∧
      (∀ z ∈ ball (0:ℂ) 1, F (z,0)=α z) ∧ (∀ z ∈ ball (0:ℂ) 1, F (0,z)=β z) := by
  classical
  obtain ⟨d,hd,_,_,f₀,hf₀,hfα,hfβ⟩ := exists_axis_box_germ h₁ h₂ isOpen_ball isOpen_ball
    (mem_ball_self (show (0:ℝ)<1 by norm_num)) (mem_ball_self (show (0:ℝ)<1 by norm_num)) hα hβ hbase
  have hgα : (fun z : ℂ ↦ f₀ (z,0)) =ᶠ[𝓝 0] α := mem_of_superset (ball_mem_nhds 0 hd) hfα
  have hgβ : (fun z : ℂ ↦ f₀ (0,z)) =ᶠ[𝓝 0] β := mem_of_superset (ball_mem_nhds 0 hd) hfβ
  have hcont₁ : Tendsto (fun z : ℂ ↦ (z,(0:ℂ))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hcont₂ : Tendsto (fun z : ℂ ↦ ((0:ℂ),z)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hex (m : ℕ) (hm : 0 < m) :
      ∃ f : ℂ × ℂ → X.Carrier, IsBox S (superDomain m 1) f ∧ f =ᶠ[𝓝 0] f₀ := by
    apply super_box_maximal hm f₀
    · obtain ⟨a,ha,haU⟩ := superDomain_small hm (isOpen_ball.prod isOpen_ball)
        (show (0:ℂ × ℂ) ∈ ball (0:ℂ) d ×ˢ ball (0:ℂ) d from ⟨mem_ball_self hd,mem_ball_self hd⟩)
      exact ⟨a,ha,f₀,hf₀.mono haU,EventuallyEq.rfl⟩
    intro a ha ha1 f hf hfg
    have haxes := superDomain_axes_of_eventually hm ha ha1.le hf hα hβ
      ((hfg.comp_tendsto hcont₁).trans hgα) ((hfg.comp_tendsto hcont₂).trans hgβ)
    obtain ⟨W,hW,hWsub,H,hH,hHf⟩ := box_extend_closure (superDomain_open m a) (superDomain_convex m a) hf
      (fun _ hp ↦ superDomain_full_boundary g h₁ h₂ hm ha ha1 hf hα hβ haxes.1 haxes.2 hp)
    obtain ⟨b,hb,hbW⟩ := superSublevel_widen hm hW (by rwa [← superDomain_closure hm ha])
    refine ⟨b,hb,H,hH.mono hbW,?_⟩
    have hHfg : H =ᶠ[𝓝 0] f := mem_of_superset ((superDomain_open m a).mem_nhds (superDomain_zero hm ha)) hHf
    exact hHfg.trans hfg
  choose F hF hFg using (fun m : {m : ℕ // 0 < m} ↦ hex m m.property)
  have hcompat (m k : {m : ℕ // 0 < m}) :
      EqOn (F m) (F k) (superDomain m 1 ∩ superDomain k 1) := by
    exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      ((superDomain_open m 1).inter (superDomain_open k 1))
      (((superDomain_convex m 1).inter (superDomain_convex k 1)).isPreconnected)
      ((hF m).1.mono inter_subset_left) ((hF k).1.mono inter_subset_right)
      (show (0:ℂ × ℂ) ∈ superDomain m 1 ∩ superDomain k 1 from
        ⟨superDomain_zero m.property (by norm_num),superDomain_zero k.property (by norm_num)⟩)
      ((hFg m).trans (hFg k).symm)
  obtain ⟨G,hG,hGF⟩ := glue_boxes (fun m : {m : ℕ // 0 < m} ↦ superDomain m 1)
    (fun m ↦ superDomain_open m 1) F hF hcompat (α 0)
  refine ⟨G,superDomain_exhaustion ▸ hG,?_,?_⟩
  · intro z hz
    have hzU : (z,0) ∈ ⋃ m : {m : ℕ // 0 < m}, superDomain m 1 := by
      rw [superDomain_exhaustion]
      exact ⟨hz,mem_ball_self (by norm_num)⟩
    obtain ⟨m,hm⟩ := mem_iUnion.mp hzU
    exact (hGF m hm).trans ((superDomain_axes_of_eventually m.property (by norm_num) (le_refl 1)
      (hF m) hα hβ ((hFg m).comp_tendsto hcont₁ |>.trans hgα)
      ((hFg m).comp_tendsto hcont₂ |>.trans hgβ)).1 z hm)
  · intro z hz
    have hzU : (0,z) ∈ ⋃ m : {m : ℕ // 0 < m}, superDomain m 1 := by
      rw [superDomain_exhaustion]
      exact ⟨mem_ball_self (by norm_num),hz⟩
    obtain ⟨m,hm⟩ := mem_iUnion.mp hzU
    exact (hGF m hm).trans ((superDomain_axes_of_eventually m.property (by norm_num) (le_refl 1)
      (hF m) hα hβ ((hFg m).comp_tendsto hcont₁ |>.trans hgα)
      ((hFg m).comp_tendsto hcont₂ |>.trans hgβ)).2 z hm)

lemma disk_axes_unique (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {F G : ℂ × ℂ → X.Carrier} (hF : IsBox S (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) F)
    (hG : IsBox S (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) G)
    (hα : ∀ z ∈ ball (0:ℂ) 1, F (z,0)=G (z,0))
    (hβ : ∀ z ∈ ball (0:ℂ) 1, F (0,z)=G (0,z)) :
    EqOn F G (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) := by
  have h0 : (0:ℂ) ∈ ball (0:ℂ) 1 := mem_ball_self (by norm_num)
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (isOpen_ball.prod isOpen_ball)
    (((convex_ball (0:ℂ) 1).prod (convex_ball (0:ℂ) 1)).isPreconnected)
    hF.1 hG.1 (show (0,0) ∈ ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 from ⟨h0,h0⟩)
    (box_axes_germ_unique h₁ h₂ isOpen_ball isOpen_ball hF hG 0 0 h0 h0 hα hβ)

end UniversalCoverSplitting

end

end OAI
