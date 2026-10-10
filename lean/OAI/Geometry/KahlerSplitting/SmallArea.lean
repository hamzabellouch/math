import OAI.Geometry.KahlerSplitting.AreaBounds

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set Metric Filter Topology
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric

namespace UniversalCoverSplitting

theorem exists_brody_maximum {a : ℂ → ℝ} {c : ℂ} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (ha : ContinuousOn a (closedBall c R))
    (han : ∀ z ∈ closedBall c R, 0 ≤ a z)
    (hw : ∃ z ∈ ball c R, ε ≤ (R - dist z c) * a z) :
    ∃ p ∈ ball c R, 0 < a p ∧ ε ≤ (R - dist p c) * a p ∧
      ∀ z ∈ ball p ((R - dist p c) / 2), z ∈ ball c R ∧ a z ≤ 2 * a p := by
  let w := fun z ↦ (R - dist z c) * a z
  have hc : ContinuousOn w (closedBall c R) :=
    (continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn).mul ha
  obtain ⟨p,hp,hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    (nonempty_closedBall.mpr hR.le) hc
  obtain ⟨z,hz,hwz⟩ := hw
  have hep : ε ≤ w p := hwz.trans (hmax (ball_subset_closedBall hz))
  have hap := han p hp
  have hdp : dist p c < R := by
    have hh : dist p c ≤ R := hp
    by_contra hn
    have he : dist p c = R := le_antisymm hh (le_of_not_gt hn)
    dsimp [w] at hep
    rw [he, sub_self, zero_mul] at hep
    linarith
  have hapos : 0 < a p := by
    by_contra hn
    have he : a p = 0 := le_antisymm (le_of_not_gt hn) hap
    dsimp [w] at hep
    rw [he, mul_zero] at hep
    linarith
  refine ⟨p,hdp,hapos,hep,?_⟩
  intro v hv
  have hvp : dist v p < (R - dist p c) / 2 := hv
  have htri := dist_triangle v p c
  have hvd : dist v c < R := by linarith
  refine ⟨hvd,?_⟩
  have ham := han v (ball_subset_closedBall hvd)
  have hvmax := hmax (ball_subset_closedBall hvd)
  dsimp [w] at hvmax
  have hdist : (R - dist p c) / 2 ≤ R - dist v c := by linarith
  have hm := mul_le_mul_of_nonneg_right hdist ham
  have hpdist : 0 < R - dist p c := sub_pos.mpr hdp
  nlinarith

theorem exists_brody_rescaling {a : ℂ → ℝ} {c : ℂ} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (ha : ContinuousOn a (closedBall c R))
    (han : ∀ z ∈ closedBall c R, 0 ≤ a z)
    (hw : ∃ z ∈ ball c R, ε ≤ (R - dist z c) * a z) :
    ∃ p ∈ ball c R, 0 < a p ∧ a p / a p = 1 ∧
      ∀ ζ ∈ ball (0 : ℂ) (ε/4),
        p + ζ / (a p : ℂ) ∈ ball c R ∧ a (p + ζ / (a p : ℂ)) / a p ≤ 2 := by
  obtain ⟨p,hp,hap,hep,hbound⟩ := exists_brody_maximum hR hε ha han hw
  refine ⟨p,hp,hap,div_self hap.ne',?_⟩
  intro ζ hζ
  have hn : ‖ζ‖ < ε/4 := by simpa using hζ
  have hd : dist (p + ζ / (a p : ℂ)) p = ‖ζ‖ / a p := by
    rw [dist_eq_norm]
    simp [Complex.norm_real, abs_of_pos hap]
  have hnear : p + ζ / (a p : ℂ) ∈ ball p ((R-dist p c)/2) := by
    rw [mem_ball, hd, div_lt_iff₀ hap]
    nlinarith
  obtain ⟨hmem,hle⟩ := hbound _ hnear
  exact ⟨hmem,(div_le_iff₀ hap).mpr hle⟩

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem small_area_weighted_speed [CompactSpace X.Carrier] (g : KahlerMetric X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (f : ℂ → X.Carrier) (Ω : Set ℂ), IsOpen Ω →
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      ∀ (c : ℂ) (R : ℝ), 0 < R → closedBall c R ⊆ Ω →
      curveArea g f (ball c R) < ENNReal.ofReal η →
      ∀ z ∈ ball c R, (R - dist z c) * curveSpeed g f z < ε := by
  obtain ⟨η,hη,hlower⟩ := exists_uniform_normalized_curveArea_lowerBound g
    (by positivity : 0 < ε/4)
  refine ⟨η,hη,?_⟩
  intro f Ω hΩ hf c R hR hsub harea z hz
  by_contra hsmall
  obtain ⟨p,hp,hap,_,hbr⟩ := exists_brody_rescaling hR hε
    ((curveSpeed_continuousOn g hΩ hf).mono hsub)
    (fun z _ ↦ curveSpeed_nonneg g f z) ⟨z,hz,le_of_not_gt hsmall⟩
  let a := (curveSpeed g f p)⁻¹
  have ha : 0 < a := inv_pos.mpr hap
  let φ : ℂ → ℂ := fun ζ ↦ p + a • ζ
  have hφ (ζ : ℂ) : φ ζ = p + ζ / (curveSpeed g f p : ℂ) := by
    simp only [φ,a,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  have hφmem (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) (ε/4)) : φ ζ ∈ ball c R := by
    rw [hφ]; exact (hbr ζ hζ).1
  let k : ℂ → X.Carrier := f ∘ φ
  have hφdiff (ζ : ℂ) : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ ζ := by
    apply DifferentiableAt.mdifferentiableAt
    simpa only [φ,Complex.real_smul,id_eq] using
      (((differentiableAt_id (𝕜 := ℂ) (x := ζ)).const_mul (a : ℂ)).const_add p)
  have hkdiff : MDifferentiableOn 𝓘(ℂ, ℂ) (model n) k (ball 0 (ε/4)) := by
    intro ζ hζ
    exact ((hf.mdifferentiableAt (hΩ.mem_nhds (hsub (ball_subset_closedBall (hφmem ζ hζ))))).comp ζ
      (hφdiff ζ)).mdifferentiableWithinAt
  have hkSpeed (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) (ε/4)) :
      curveSpeed g k ζ = a * curveSpeed g f (φ ζ) := by
    simpa only [k,Function.comp_def,φ,Complex.real_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos ha] using
      curveSpeed_affine g p (a : ℂ) ζ
        (hf.mdifferentiableAt (hΩ.mem_nhds (hsub (ball_subset_closedBall (hφmem ζ hζ)))))
  have hk0 : curveSpeed g k 0 = 1 := by
    rw [hkSpeed 0 (mem_ball_self (by positivity))]
    simp [φ,a,inv_mul_cancel₀ hap.ne']
  have hk2 (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) (ε/4)) : curveSpeed g k ζ ≤ 2 := by
    rw [hkSpeed ζ hζ,hφ]
    simpa only [a,div_eq_mul_inv,mul_comm] using (hbr ζ hζ).2
  have hsubarea : curveArea g k (ball 0 (ε/4)) ≤ curveArea g f (ball c R) := by
    change curveArea g (fun ζ ↦ f (p + a • ζ)) (ball 0 (ε/4)) ≤ _
    rw [curveArea_positive_affine g _ measurableSet_ball p ha]
    · exact curveArea_mono g f (by rintro _ ⟨ζ,hζ,rfl⟩; exact hφmem ζ hζ)
    · rintro _ ⟨ζ,hζ,rfl⟩
      exact hf.mdifferentiableAt (hΩ.mem_nhds (hsub (ball_subset_closedBall (hφmem ζ hζ))))
  exact (not_lt_of_ge ((hlower k hkdiff hk0 hk2).trans hsubarea)) harea

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem exists_small_area_speed_bound [CompactSpace X.Carrier] (g : KahlerMetric X)
    {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ f : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      curveArea g f Ω < ENNReal.ofReal η → ∀ z ∈ K, curveSpeed g f z < ε := by
  obtain ⟨R,hR,hball⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨η,hη,hb⟩ := small_area_weighted_speed g (mul_pos hε hR)
  refine ⟨η,hη,?_⟩
  intro f hf harea z hz
  have hc : closedBall z R ⊆ Ω := (closedBall_subset_cthickening hz R).trans hball
  have he := hb f Ω hΩ hf z R hR hc ((curveArea_mono g f
    (ball_subset_closedBall.trans hc)).trans_lt harea) z (mem_ball_self hR)
  simp only [dist_self,sub_zero] at he
  nlinarith

theorem small_area_derivatives_tendstoUniformlyOn [CompactSpace X.Carrier]
    (g : KahlerMetric X) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (h : ℕ → ℂ → X.Carrier)
    (hhol : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (h j) Ω)
    (harea : Tendsto (fun j ↦ curveArea g (h j) Ω) atTop (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun j z ↦ curveSpeed g (h j) z) (fun _ ↦ 0) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨η,hη,hb⟩ := exists_small_area_speed_bound g hΩ hK hKΩ hε
  filter_upwards [harea.eventually_lt_const (ENNReal.ofReal_pos.mpr hη)] with j hj
  intro z hz
  simpa only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (curveSpeed_nonneg g (h j) z)] using
    hb (h j) (hhol j) hj z hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem bounded_curveSpeed_local_trapping (g : KahlerMetric X) (c : X.Carrier)
    {V : Set X.Carrier} (hV : V ∈ 𝓝 c) {L : ℝ} (hL : 0 ≤ L) :
    ∃ W ∈ 𝓝 c, ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ r →
      ∀ (f : ℂ → X.Carrier) (Ω : Set ℂ),
      IsOpen Ω → MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      closedBall (0 : ℂ) ρ ⊆ Ω → f 0 ∈ W →
      (∀ z ∈ closedBall (0 : ℂ) ρ, curveSpeed g f z ≤ L) →
      MapsTo f (closedBall (0 : ℂ) ρ) V := by
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  have het : e c ∈ e.target := e.map_source hc
  have hnear : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e c) :=
    inter_mem (e.open_target.mem_nhds het)
      ((e.continuousOn_symm.continuousAt (e.open_target.mem_nhds het))
        (by simpa only [e.left_inv hc] using hV))
  obtain ⟨R,hR,hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have he : closedBall (e c) R ⊆ e.target := fun z hz ↦ (hRsub hz).1
  obtain ⟨C,D,hC,_,hcomp⟩ := g.exists_chart_speed_comparison c
    (isCompact_closedBall (e c) R) he
  let W := e.source ∩ e ⁻¹' ball (e c) (R/2)
  have hW : W ∈ 𝓝 c := (e.isOpen_inter_preimage isOpen_ball).mem_nhds
    ⟨hc,by simpa using half_pos hR⟩
  let r := R / (4 * (C * L + 1))
  have hCL : 0 ≤ C * L := mul_nonneg hC.le hL
  have hr : 0 < r := div_pos hR (by positivity)
  have hrCL : C * L * r ≤ R / 4 := by
    dsimp [r]
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    have hd : 0 < 4 * (C * L + 1) := by positivity
    field_simp
    nlinarith
  refine ⟨W,hW,r,hr,?_⟩
  intro ρ hρ hρr f Ω hΩ hf hsub hzero hspeed z hz
  have hρCL : C * L * ρ ≤ R / 4 :=
    (mul_le_mul_of_nonneg_left hρr hCL).trans hrCL
  have htrap : ∀ z ∈ closedBall (0 : ℂ) ρ,
      f z ∈ e.source ∧ e (f z) ∈ ball (e c) R := by
    apply chart_trapping_on_disk e hR hCL hρ he (hf.continuousOn.mono hsub)
    · refine ⟨hzero.1,?_⟩
      have hh : dist (e (f 0)) (e c) < R/2 := hzero.2
      linarith
    · intro w hw hk
      obtain ⟨v,hv,hvf⟩ := hk
      have hs : f w ∈ e.source := hvf ▸ e.map_target (he hv)
      have hv' : e (f w) ∈ closedBall (e c) R := by
        rw [← hvf,e.right_inv (he hv)]; exact hv
      have hfd := hf.mdifferentiableAt (hΩ.mem_nhds (hsub hw))
      have hed : MDifferentiableAt (model n) (model n) e (f w) :=
        mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hs)
      refine ⟨(hed.comp w hfd).differentiableAt,?_⟩
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv ((extChartAt (model n) c) ∘ f) w‖ ≤ C * L
      rw [chart_deriv_curve hfd c hs]
      exact ((hcomp (f w) hs hv' (mfderiv 𝓘(ℂ, ℂ) (model n) f w (1:ℂ))).1).trans
        (mul_le_mul_of_nonneg_left (hspeed w hw) hC.le)
  have ht := htrap z hz
  have hv := (hRsub (ball_subset_closedBall ht.2)).2
  simpa only [mem_preimage,e.left_inv ht.1] using hv

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

noncomputable abbrev compactManifoldMetric (X : ComplexManifold n)
    [CompactSpace X.Carrier] : MetricSpace X.Carrier := by
  letI : TopologicalSpace.MetrizableSpace X.Carrier :=
    Manifold.metrizableSpace 𝓘(ℝ, Model n) X.Carrier
  exact TopologicalSpace.metrizableSpaceMetric X.Carrier

local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem bounded_curveSpeed_uniform_trapping [CompactSpace X.Carrier]
    (g : KahlerMetric X) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ r →
      ∀ (f : ℂ → X.Carrier) (Ω : Set ℂ),
      IsOpen Ω → MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      closedBall (0 : ℂ) ρ ⊆ Ω →
      (∀ z ∈ closedBall (0 : ℂ) ρ, curveSpeed g f z ≤ L) →
      ∀ z ∈ closedBall (0 : ℂ) ρ, dist (f 0) (f z) < ε := by
  classical
  choose W hW r hr hb using fun c : X.Carrier ↦
    bounded_curveSpeed_local_trapping g c (ball_mem_nhds c (half_pos hε)) hL
  let V (c : X.Carrier) := W c ∩ ball c (ε/2)
  have hV (c : X.Carrier) : V c ∈ 𝓝 c := inter_mem (hW c) (ball_mem_nhds c (half_pos hε))
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have covered (x : X.Carrier) : ∃ c ∈ s, x ∈ V c := by
    have hx : x ∈ ⋃ c ∈ s, V c := by rw [hs]; trivial
    simpa only [mem_iUnion,exists_prop] using hx
  by_cases hne : s.Nonempty
  · refine ⟨s.inf' hne r, (Finset.lt_inf'_iff hne).mpr (fun c _ ↦ hr c),?_⟩
    intro ρ hρ hρr f Ω hΩ hf hsub hspeed z hz
    obtain ⟨c,hcs,hc⟩ := covered (f 0)
    have ht := hb c ρ hρ (hρr.trans (s.inf'_le r hcs)) f Ω hΩ hf hsub hc.1 hspeed hz
    calc
      dist (f 0) (f z) ≤ dist (f 0) c + dist c (f z) := dist_triangle _ _ _
      _ < ε/2 + ε/2 := add_lt_add hc.2 (by simpa only [mem_ball,dist_comm] using ht)
      _ = ε := by ring
  · refine ⟨1,by norm_num,?_⟩
    intro ρ hρ hρr f
    obtain ⟨c,hcs,_⟩ := covered (f 0)
    exact (hne ⟨c,hcs⟩).elim

theorem bounded_curveSpeed_equicontinuousOn [CompactSpace X.Carrier]
    (g : KahlerMetric X) {ι : Type*} (f : ι → ℂ → X.Carrier)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f i) Ω)
    (hb : ∀ p ∈ Ω, ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ closedBall p R ⊆ Ω ∧
      ∀ i z, z ∈ closedBall p R → curveSpeed g (f i) z ≤ L) :
    EquicontinuousOn f Ω := by
  intro p hp
  apply EquicontinuousAt.equicontinuousWithinAt
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R,L,hR,hL,hRΩ,hbound⟩ := hb p hp
  obtain ⟨r,hr,htrap⟩ := bounded_curveSpeed_uniform_trapping g hL hε
  let ρ := min r R
  have hρ : 0 < ρ := lt_min hr hR
  refine ⟨ρ,hρ,?_⟩
  intro z hz i
  let φ : ℂ → ℂ := fun w ↦ p + w
  have hφdiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ :=
    (differentiable_id.const_add p).mdifferentiable
  have hφmem {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) : φ w ∈ closedBall p R := by
    simpa [φ,mem_closedBall,dist_eq_norm] using
      (hw.trans (min_le_right r R))
  have hk : MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f i ∘ φ) (φ ⁻¹' Ω) :=
    (hf i).comp hφdiff.mdifferentiableOn (fun _ hw ↦ hw)
  have hspeed (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
      curveSpeed g (f i ∘ φ) w ≤ L := by
    have ha := curveSpeed_affine g p (1:ℂ) w
      (by simpa only [one_mul,φ] using
        (hf i).mdifferentiableAt (hΩ.mem_nhds (hRΩ (hφmem hw))))
    have hs : curveSpeed g (f i ∘ φ) w = curveSpeed g (f i) (φ w) := by
      simpa only [φ,Function.comp_def,one_mul,norm_one] using ha
    exact hs.trans_le (hbound i (φ w) (hφmem hw))
  have hw : z-p ∈ closedBall (0 : ℂ) ρ := by
    simpa only [mem_closedBall,dist_zero_right,← dist_eq_norm] using hz.le
  have ht := htrap ρ hρ.le (min_le_left r R) (f i ∘ φ) (φ ⁻¹' Ω)
    (hΩ.preimage hφdiff.continuous) hk (fun w hw ↦ hRΩ (hφmem hw)) hspeed (z-p) hw
  simpa only [Function.comp_def,φ,add_zero,add_sub_cancel] using ht

end UniversalCoverSplitting

open Set Filter Topology
namespace UniversalCoverSplitting

theorem equicontinuous_compact_target_subsequence
    {T Y : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MetricSpace Y] [CompactSpace Y]
    (f : ℕ → C(T,Y)) (he : Equicontinuous (fun j x ↦ f j x)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : C(T,Y),
      Tendsto (f ∘ σ) atTop (𝓝 g) := by
  classical
  have he' : Equicontinuous (fun (i : range f) x ↦ i.val x) := by
    choose a ha using fun i : range f ↦ i.property
    have hh := he.comp a
    simpa only [Function.comp_def,ha] using hh
  have : T2Space (UniformOnFun T Y {K : Set T | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      ext x
      simp only [mem_sUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨{x},isCompact_singleton,mem_singleton x⟩)
  have hc : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun (h : C(T,Y)) x ↦ h x) (𝔖 := {K : Set T | IsCompact K})
      (fun _ h ↦ h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · exact fun K _ ↦ he'.equicontinuousOn K
    · exact fun _ _ _ _ ↦ ⟨univ,isCompact_univ,fun _ _ ↦ mem_univ _⟩
  obtain ⟨g,_,σ,hσ,hg⟩ := hc.tendsto_subseq (fun j ↦ subset_closure (mem_range_self j))
  exact ⟨σ,hσ,g,hg⟩

end UniversalCoverSplitting

end

end OAI
