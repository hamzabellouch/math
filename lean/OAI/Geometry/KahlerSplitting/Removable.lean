import OAI.Geometry.KahlerSplitting.CompactCurves

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology MeasureTheory
open Complex
open Set Filter Topology

namespace UniversalCoverSplitting

theorem compact_family_trapping {M T : Type*}
    [TopologicalSpace M] [TopologicalSpace T] [CompactSpace T]
    (H : ℝ → T → M) (hH : Continuous (Function.uncurry H))
    {K V : Set M} (hK : IsClosed K) (hV : IsOpen V) (hVK : V ⊆ K)
    {b : ℝ} (_hb : 0 ≤ b) (hzero : ∀ u, H 0 u ∈ K)
    (hcontrol : ∀ t ∈ Ico 0 b,
      (∀ s ∈ Icc 0 t, ∀ u, H s u ∈ K) → ∀ u, H t u ∈ V) :
    ∀ t ∈ Icc 0 b, ∀ u, H t u ∈ K := by
  let A : Set ℝ := {t | ∀ u, H t u ∈ K}
  have hA : IsClosed A := by
    have he : A = ⋂ u : T, (fun t ↦ H t u) ⁻¹' K := by ext t; simp [A]
    rw [he]
    exact isClosed_iInter (fun u ↦ hK.preimage (hH.comp (continuous_id.prodMk continuous_const)))
  have hall : Icc 0 b ⊆ A := by
    apply (hA.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
    intro t ht hst
    have hc := hcontrol t ht (fun s hs u ↦ hst hs u)
    have he : ∀ᶠ s in 𝓝 t, ∀ u : T, H s u ∈ V := by
      have hh := isCompact_univ.eventually_forall_of_forall_eventually
        (x₀ := t) (K := (univ : Set T)) (P := fun s u ↦ H s u ∈ V)
        (fun u _ ↦ hH.continuousAt (hV.mem_nhds (hc u)))
      simpa only [mem_univ,forall_const] using hh
    exact nhdsWithin_le_nhds (he.mono (fun s hs u ↦ hVK (hs u)))
  exact fun t ht u ↦ hall ht u

end UniversalCoverSplitting

open Set Metric Filter Topology Complex
namespace UniversalCoverSplitting
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [ProperSpace E]

theorem punctured_chart_trapping (e : OpenPartialHomeomorph M E)
    {f : ℂ → M} {c : E} {R r L : ℝ}
    (_hR : 0 < R) (_hr : 0 < r) (hL : 0 ≤ L)
    (hchart : closedBall c R ⊆ e.target)
    (hc : ContinuousOn f {z | 0 < ‖z‖ ∧ ‖z‖ ≤ r})
    (houter : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.source ∧ e (f z) ∈ closedBall c R)
    (hmargin : dist (e (f (r:ℂ))) c + 24 * L < R)
    (hd : ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ e.symm '' closedBall c R → DifferentiableAt ℂ (e ∘ f) z)
    (hb : ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ e.symm '' closedBall c R → ‖deriv (e ∘ f) z‖ * ‖z‖ ≤ L) :
    ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ e.source ∧ e (f z) ∈ closedBall c R := by
  let K := e.symm '' closedBall c R
  let V := e.source ∩ e ⁻¹' ball c R
  have hK : IsClosed K :=
    ((isCompact_closedBall c R).image_of_continuousOn (e.continuousOn_symm.mono hchart)).isClosed
  have hV : IsOpen V := e.isOpen_inter_preimage isOpen_ball
  have hVK : V ⊆ K := by
    intro x hx
    exact ⟨e x,ball_subset_closedBall hx.2,e.left_inv hx.1⟩
  have hmem (x : M) (hx : x ∈ K) : x ∈ e.source ∧ e x ∈ closedBall c R := by
    obtain ⟨w,hw,rfl⟩ := hx
    exact ⟨e.map_target (hchart hw), by rwa [e.right_inv (hchart hw)]⟩
  have hring (a : ℝ) (ha : 0 < a) (har : a ≤ r) :
      ∀ z, a ≤ ‖z‖ → ‖z‖ ≤ r → f z ∈ K := by
    let T := sphere (0:ℂ) 1
    let : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_sphere (0:ℂ) 1)
    let ρ : ℝ → ℝ := fun t ↦ max a (min (r-t) r)
    have hρ : Continuous ρ := continuous_const.max ((continuous_const.sub continuous_id).min continuous_const)
    have hρlo (t : ℝ) : a ≤ ρ t := le_max_left _ _
    have hρhi (t : ℝ) : ρ t ≤ r := max_le har (min_le_right _ _)
    have hρeq (t : ℝ) (ht : t ∈ Icc 0 (r-a)) : ρ t = r-t := by
      dsimp [ρ]
      rw [min_eq_left (by linarith [ht.1]),max_eq_right (by linarith [ht.2])]
    let H : ℝ → T → M := fun t u ↦ f ((ρ t : ℂ) * (u:ℂ))
    have harg (t : ℝ) (u : T) : ‖(ρ t : ℂ) * (u:ℂ)‖ = ρ t := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha.trans_le (hρlo t)),
        norm_eq_of_mem_sphere,mul_one]
    have hH : Continuous (Function.uncurry H) := by
      apply hc.comp_continuous
      · exact ((Complex.continuous_ofReal.comp (hρ.comp continuous_fst)).mul
          (continuous_subtype_val.comp continuous_snd))
      · intro p
        exact ⟨by rw [harg]; exact ha.trans_le (hρlo p.1), by rw [harg]; exact hρhi p.1⟩
    have hzero : ∀ u, H 0 u ∈ K := by
      intro u
      have hn : ‖(ρ 0 : ℂ) * (u:ℂ)‖ = r := by rw [harg,hρeq 0 ⟨le_rfl,sub_nonneg.mpr har⟩,sub_zero]
      have ho := houter ((ρ 0:ℂ)*(u:ℂ)) (by simpa only [mem_sphere,dist_zero_right] using hn)
      exact ⟨e _,ho.2,e.left_inv ho.1⟩
    have hcontrol : ∀ t ∈ Ico 0 (r-a),
        (∀ s ∈ Icc 0 t, ∀ u, H s u ∈ K) → ∀ u, H t u ∈ V := by
      intro t ht hprev u
      have ht' : t ∈ Icc 0 (r-a) := ⟨ht.1,ht.2.le⟩
      have hrt : 0 < r-t := by linarith [ht.2]
      have hrtR : r-t ≤ r := by linarith [ht.1]
      have hann : ∀ z ∈ closedBall (0:ℂ) r \ ball 0 (r-t), f z ∈ K := by
        intro w hw
        have hwlo : r-t ≤ ‖w‖ := by simpa using hw.2
        have hwhi : ‖w‖ ≤ r := by simpa using hw.1
        have hwpos : 0 < ‖w‖ := hrt.trans_le hwlo
        let v : T := ⟨(‖w‖⁻¹ : ℂ) * w, by
          simp [T,inv_mul_cancel₀ hwpos.ne']⟩
        have hs : r-‖w‖ ∈ Icc 0 t := ⟨by linarith,by linarith⟩
        have hp := hprev (r-‖w‖) hs v
        have hv : (ρ (r-‖w‖) : ℂ) * (v:ℂ) = w := by
          rw [hρeq _ ⟨hs.1,hs.2.trans ht.2.le⟩]
          dsimp [v]
          simp only [sub_sub_cancel]
          rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hwpos.ne'),one_mul]
        simpa only [H,hv] using hp
      have hfc : ContinuousOn (e ∘ f) (closedBall 0 r \ ball 0 (r-t)) := by
        apply e.continuousOn.comp (hc.mono _) (fun w hw ↦ (hmem _ (hann w hw)).1)
        intro w hw
        have hlo : r-t ≤ ‖w‖ := by simpa using hw.2
        exact ⟨hrt.trans_le hlo,by simpa using hw.1⟩
      have ho := holomorphic_annulus_oscillation hrt hrtR hL hfc
        (fun w hw ↦ hd w (hrt.trans_le (by simpa using hw.2)) (by simpa using hw.1) (hann w hw))
        (fun w hw ↦ hb w (hrt.trans_le (by simpa using hw.2)) (by simpa using hw.1) (hann w hw))
        ((ρ t:ℂ)*(u:ℂ)) (by simp only [mem_sphere,dist_zero_right]; rw [harg,hρeq t ht'])
      have hm := hmem _ (hprev t ⟨ht.1,le_rfl⟩ u)
      refine ⟨hm.1,?_⟩
      change dist (e (H t u)) c < R
      have htri := dist_triangle (e (H t u)) (e (f (r:ℂ))) c
      have hdist : dist (e (H t u)) (e (f (r:ℂ))) ≤ 24*L := by
        simpa only [dist_eq_norm,Function.comp_apply,H] using ho
      linarith
    intro z hzlo hzhi
    let u : T := ⟨(‖z‖⁻¹:ℂ)*z, by
      have hzpos := ha.trans_le hzlo
      simp [T,inv_mul_cancel₀ hzpos.ne']⟩
    have hs : r-‖z‖ ∈ Icc 0 (r-a) := ⟨by linarith,by linarith⟩
    have hg := compact_family_trapping H hH hK hV hVK (sub_nonneg.mpr har) hzero hcontrol _ hs u
    have hv : (ρ (r-‖z‖):ℂ)*(u:ℂ) = z := by
      rw [hρeq _ hs]
      dsimp [u]
      simp only [sub_sub_cancel]
      rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ha.trans_le hzlo).ne'),one_mul]
    simpa only [H,hv] using hg
  intro z hz hrz
  exact hmem _ (hring ‖z‖ hz hrz z le_rfl hrz)

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting

theorem finite_density_small_ball {w : ℂ → ℝ≥0∞} {Ω : Set ℂ}
    (hfin : (∫⁻ z in Ω, w z) ≠ (⊤ : ℝ≥0∞)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ D : Set ℂ, D ⊆ ball 0 δ → D ⊆ Ω →
      (∫⁻ z in D, w z) < ε := by
  obtain ⟨b,hb,hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin hε.ne'
  have hv : Tendsto (fun t : ℝ ↦ volume (ball (0:ℂ) t)) (𝓝 0) (𝓝 0) := by
    have hh := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2)
      (ENNReal.continuous_ofReal.tendsto (0:ℝ))) (Or.inr (ENNReal.coe_ne_top : (NNReal.pi : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)))
    simpa only [Complex.volume_ball,ENNReal.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0),zero_mul] using hh
  obtain ⟨a,ha,haV⟩ := Metric.nhds_basis_ball.mem_iff.mp (hv.eventually_lt_const hb)
  let δ := a/2
  have hδ : 0 < δ := half_pos ha
  have hm : volume (ball (0:ℂ) δ) < b := haV (by simpa [δ,Real.dist_eq,abs_of_pos ha] using (half_lt_self ha))
  refine ⟨δ,hδ,?_⟩
  intro D hD hDΩ
  have hh := hsmall D ((Measure.restrict_le_self _).trans_lt ((measure_mono hD).trans_lt hm))
  rwa [Measure.restrict_restrict_of_subset hDΩ] at hh

variable {n : ℕ} {X : ComplexManifold n}

theorem finite_curveArea_scaled_speed [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ha : curveArea g f (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ δ →
      ‖z‖ * curveSpeed g f z < ε := by
  obtain ⟨η,hη,hsmall⟩ := small_area_weighted_speed g (half_pos hε)
  obtain ⟨a,ha',harea⟩ := finite_density_small_ball ha (ENNReal.ofReal_pos.mpr hη)
  let δ := min a R / 4
  have hδ : 0 < δ := div_pos (lt_min ha' hR) (by norm_num)
  have hδR : δ < R := by
    have hd := min_le_right a R
    dsimp [δ]; linarith [lt_min ha' hR]
  refine ⟨δ,hδ,hδR,?_⟩
  intro z hz hzδ
  have hc : closedBall z (‖z‖/2) ⊆ ball 0 R \ {0} := by
    intro w hw
    have hwz : dist w z ≤ ‖z‖/2 := hw
    have htri := dist_triangle w z 0
    simp only [dist_zero_right] at htri
    have htri' := dist_triangle z w 0
    simp only [dist_zero_right] at htri'
    rw [dist_comm z w] at htri'
    have hnorm : ‖w‖ < R := by
      have hzR := hzδ.trans hδR.le
      dsimp [δ] at hzδ
      have hh := min_le_right a R
      linarith
    refine ⟨by simpa using hnorm,?_⟩
    intro hw0
    have he : w = 0 := hw0
    subst w
    simp only [norm_zero,dist_zero_left] at htri' hwz
    linarith
  have hcsmall : ball z (‖z‖/2) ⊆ ball (0:ℂ) a := by
    intro w hw
    have hwz : dist w z < ‖z‖/2 := hw
    have htri := dist_triangle w z 0
    simp only [dist_zero_right] at htri
    have hh := min_le_left a R
    dsimp [δ] at hzδ
    have hn : ‖w‖ < a := by linarith
    simpa using hn
  have he : curveArea g f (ball z (‖z‖/2)) < ENNReal.ofReal η :=
    harea _ hcsmall (ball_subset_closedBall.trans hc)
  have hh := hsmall f (ball 0 R \ {0}) (isOpen_ball.sdiff isClosed_singleton) hf z (‖z‖/2)
    (half_pos hz) hc he z (mem_ball_self (half_pos hz))
  simp only [dist_self,sub_zero] at hh
  nlinarith

end UniversalCoverSplitting

open Set Metric Filter Topology Complex
namespace UniversalCoverSplitting
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [ProperSpace E]

theorem chart_trapping_on_circle (e : OpenPartialHomeomorph M E)
    {f : ℂ → M} {c : E} {R r L : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hL : 0 ≤ L)
    (he : closedBall c R ⊆ e.target)
    (hc : ContinuousOn f (sphere (0:ℂ) r))
    (hzero : f (r:ℂ) ∈ e.source ∧ dist (e (f (r:ℂ))) c < R - 8*L)
    (hd : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.symm '' closedBall c R →
      DifferentiableAt ℂ (e ∘ f) z)
    (hb : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.symm '' closedBall c R →
      ‖deriv (e ∘ f) z‖ * r ≤ L) :
    ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.source ∧ e (f z) ∈ ball c R := by
  have hγ : ContinuousOn (fun θ : ℝ ↦ f (circleMap 0 r θ)) (Icc 0 (2*Real.pi)) :=
    hc.comp (continuous_circleMap 0 r).continuousOn (fun θ _ ↦ circleMap_mem_sphere 0 hr.le θ)
  have hinit : f (circleMap 0 r 0) ∈ e.source ∧
      dist (e (f (circleMap 0 r 0))) c < R - L * (2*Real.pi) := by
    simpa [circleMap] using And.intro hzero.1 (hzero.2.trans_le (by
      have ht : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      nlinarith))
  have ht := chart_trapping_on_interval e hR hL Real.two_pi_pos.le he hγ hinit
    (fun θ _ hk ↦ ?_)
  · intro z hz
    have hz' : z ∈ circleMap 0 r '' Ioc 0 (2*Real.pi) := by
      rw [image_circleMap_Ioc,abs_of_pos hr]
      exact hz
    obtain ⟨θ,hθ,rfl⟩ := hz'
    exact ht θ ⟨hθ.1.le,hθ.2⟩
  have hm := circleMap_mem_sphere (0:ℂ) hr.le θ
  refine ⟨(circleMap 0 r θ * I) • deriv (e ∘ f) (circleMap 0 r θ),?_,?_⟩
  · exact ((hd _ hm hk).hasDerivAt.scomp θ (hasDerivAt_circleMap 0 r θ)).hasDerivWithinAt
  · rw [norm_smul,norm_mul,norm_I,mul_one]
    have hn : ‖circleMap 0 r θ‖ = r := by simpa using hm
    rw [hn,mul_comm]
    exact hb _ hm hk

end UniversalCoverSplitting

open Set Metric Filter Topology Complex
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem finite_curveArea_compact_chart [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ha : curveArea g f (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞)) :
    ∃ c : X.Carrier, ∃ r B : ℝ, 0 < r ∧ r < R ∧ 0 < B ∧
      closedBall ((extChartAt (model n) c) c) B ⊆ (extChartAt (model n) c).target ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r →
        f z ∈ (extChartAt (model n) c).source ∧
        (extChartAt (model n) c) (f z) ∈ closedBall ((extChartAt (model n) c) c) B := by
  let u (j : ℕ) : ℝ := 1 / (j+1)
  have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨c,σ,hσ,hlim⟩ := CompactSpace.tendsto_subseq (fun j ↦ f (u j : ℂ))
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨B,hB,hBt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (e.open_target.mem_nhds (e.map_source hc))
  obtain ⟨C,D,hC,_,hcomp⟩ := g.exists_chart_speed_comparison c (isCompact_closedBall (e c) B) hBt
  let L := B/100
  have hL : 0 < L := div_pos hB (by norm_num)
  obtain ⟨δ,hδ,hδR,hspeed⟩ := finite_curveArea_scaled_speed g hR hf ha (div_pos hL hC)
  have hnear : e.source ∩ e ⁻¹' ball (e c) (B/4) ∈ 𝓝 c :=
    (e.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hc, by simpa using div_pos hB (by norm_num : (0:ℝ)<4)⟩
  have hnear' : ∀ᶠ j in atTop, f (u (σ j):ℂ) ∈ e.source ∩ e ⁻¹' ball (e c) (B/4) := hlim hnear
  have he := hnear'.and ((hu0.comp hσ.tendsto_atTop).eventually_lt_const hδ)
  obtain ⟨j,hj,hjr⟩ := he.exists
  let r := u (σ j)
  have hr : 0 < r := hu _
  have hrδ : r < δ := hjr
  have hrR : r < R := hrδ.trans hδR
  have hsource (z : ℂ) (hz : 0 < ‖z‖) (hzr : ‖z‖ ≤ r) : z ∈ ball 0 R \ {0} := by
    refine ⟨by simpa using hzr.trans_lt hrR,?_⟩
    simpa only [mem_singleton_iff] using (norm_pos_iff.mp hz)
  have hK (x : X.Carrier) (hx : x ∈ e.symm '' closedBall (e c) B) :
      x ∈ e.source ∧ e x ∈ closedBall (e c) B := by
    obtain ⟨v,hv,rfl⟩ := hx
    exact ⟨e.map_target (hBt hv), by rwa [e.right_inv (hBt hv)]⟩
  have hdiff (z : ℂ) (hz : 0 < ‖z‖) (hzr : ‖z‖ ≤ r)
      (hk : f z ∈ e.symm '' closedBall (e c) B) : DifferentiableAt ℂ (e ∘ f) z := by
    have hfd := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsource z hz hzr))
    have hed : MDifferentiableAt (model n) (model n) e (f z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using (hK _ hk).1)
    exact (hed.comp z hfd).differentiableAt
  have hbound (z : ℂ) (hz : 0 < ‖z‖) (hzr : ‖z‖ ≤ r)
      (hk : f z ∈ e.symm '' closedBall (e c) B) : ‖deriv (e ∘ f) z‖ * ‖z‖ ≤ L := by
    have hfd := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsource z hz hzr))
    have hnorm : ‖deriv (e ∘ f) z‖ ≤ C * curveSpeed g f z := by
      change ‖deriv ((extChartAt (model n) c) ∘ f) z‖ ≤ C * curveSpeed g f z
      rw [chart_deriv_curve hfd c (hK _ hk).1]
      exact (hcomp (f z) (hK _ hk).1 (hK _ hk).2 (mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ))).1
    have hh := hspeed z hz (hzr.trans hrδ.le)
    have hm := mul_lt_mul_of_pos_left hh hC
    rw [mul_div_cancel₀ _ hC.ne'] at hm
    nlinarith
  have hcircle : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.source ∧ e (f z) ∈ ball (e c) B := by
    apply chart_trapping_on_circle e hB hr hL.le hBt
    · apply hf.continuousOn.mono
      intro z hz
      have hn : ‖z‖ = r := by simpa using hz
      exact hsource z (hn ▸ hr) hn.le
    · refine ⟨hj.1,?_⟩
      have hh : dist (e (f (r:ℂ))) (e c) < B/4 := hj.2
      dsimp [L]; linarith
    · intro z hz hk
      have hn : ‖z‖ = r := by simpa using hz
      exact hdiff z (hn ▸ hr) hn.le hk
    · intro z hz hk
      have hn : ‖z‖ = r := by simpa using hz
      simpa only [hn] using hbound z (hn ▸ hr) hn.le hk
  have htrap := punctured_chart_trapping e hB hr hL.le hBt
    (hf.continuousOn.mono (fun z hz ↦ hsource z hz.1 hz.2))
    (fun z hz ↦ ⟨(hcircle z hz).1,ball_subset_closedBall (hcircle z hz).2⟩)
    (show dist (e (f (r:ℂ))) (e c) + 24*L < B from by
      have hh : dist (e (f (r:ℂ))) (e c) < B/4 := hj.2
      dsimp [L]; linarith) hdiff hbound
  exact ⟨c,r,B,hr,hrR,hB,hBt,htrap⟩

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem compact_chart_removable {f : ℂ → X.Carrier} {R r B : ℝ}
    (_hR : 0 < R) (hr : 0 < r) (hrR : r < R) (c : X.Carrier)
    (hBt : closedBall ((extChartAt (model n) c) c) B ⊆ (extChartAt (model n) c).target)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ht : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ (extChartAt (model n) c).source ∧
      (extChartAt (model n) c) (f z) ∈ closedBall ((extChartAt (model n) c) c) B) :
    ∃ x : X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (Function.update f 0 x) (ball 0 R) := by
  classical
  let e := extChartAt (model n) c
  let Ω := ball (0:ℂ) r \ {0}
  have hsub : Ω ⊆ ball 0 R \ {0} := sdiff_subset_sdiff_left (ball_subset_ball hrR.le)
  have hmem (z : ℂ) (hz : z ∈ Ω) : f z ∈ e.source ∧ e (f z) ∈ closedBall (e c) B := by
    exact ht z (norm_pos_iff.mpr hz.2) (le_of_lt (by simpa using hz.1))
  have hd : DifferentiableOn ℂ (e ∘ f) Ω := by
    intro z hz
    have hfd := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsub hz))
    have he : MDifferentiableAt (model n) (model n) e (f z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using (hmem z hz).1)
    exact (he.comp z hfd).differentiableAt.differentiableWithinAt
  have hb : BddAbove (norm ∘ (e ∘ f) '' Ω) := by
    refine ⟨B + ‖e c‖,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have ht' := norm_le_insert (e c) (e (f z))
    rw [norm_sub_rev] at ht'
    have hh : ‖e (f z) - e c‖ ≤ B := by simpa only [mem_closedBall,dist_eq_norm] using (hmem z hz).2
    dsimp [Function.comp_def]
    linarith
  let b := limUnder (𝓝[≠] (0:ℂ)) (e ∘ f)
  let q := Function.update (e ∘ f) 0 b
  have hq : DifferentiableOn ℂ q (ball 0 r) :=
    differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr) hd hb
  have hq0 := hq.differentiableAt (ball_mem_nhds 0 hr)
  have hlim : Tendsto (e ∘ f) (𝓝[≠] (0:ℂ)) (𝓝 b) :=
    continuousAt_update_same.mp hq0.continuousAt
  have hevent : ∀ᶠ z in 𝓝[≠] (0:ℂ), e (f z) ∈ closedBall (e c) B := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr),self_mem_nhdsWithin] with z hz hz0
    exact (hmem z ⟨hz,hz0⟩).2
  have hbK : b ∈ closedBall (e c) B := isClosed_closedBall.mem_of_tendsto hlim hevent
  have hbi : MDifferentiableAt (model n) (model n) e.symm b :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target c).mem_nhds (hBt hbK))
  have hqzero : q 0 = b := Function.update_self _ _ _
  have hcomp : MDifferentiableAt 𝓘(ℂ,ℂ) (model n) (e.symm ∘ q) 0 := by
    apply (hqzero ▸ hbi).comp 0 hq0.mdifferentiableAt
  have hzero : MDifferentiableAt 𝓘(ℂ,ℂ) (model n) (Function.update f 0 (e.symm b)) 0 := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0:ℂ) hr] with z hz
    by_cases hz0 : z = 0
    · subst z
      simp only [Function.comp_apply,hqzero,Function.update_self]
    · simp only [Function.update_of_ne hz0,q,Function.comp_apply]
      exact (e.left_inv (hmem z ⟨hz,hz0⟩).1).symm
  refine ⟨e.symm b,?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z; exact hzero.mdifferentiableWithinAt
  · have hd' := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz,hz0⟩)
    apply (hd'.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
    exact Function.update_of_ne hw _ _

theorem finite_curveArea_removable [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ha : curveArea g f (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞)) :
    ∃ x : X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (Function.update f 0 x) (ball 0 R) := by
  obtain ⟨c,r,B,hr,hrR,_,hBt,ht⟩ := finite_curveArea_compact_chart g hR hf ha
  exact compact_chart_removable hR hr hrR c hBt hf ht

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem locally_uniform_curveSpeed_tendsto [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℕ → ℂ → X.Carrier} {F : ℂ → X.Carrier} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (hconv : TendstoLocallyUniformlyOn f F atTop Ω) {p : ℂ} (hp : p ∈ Ω) :
    Tendsto (fun j ↦ curveSpeed g (f j) p) atTop (𝓝 (curveSpeed g F p)) := by
  have hF := manifold_holomorphic_locally_uniform_limit hΩ hf hconv
  have hc : ContinuousOn F Ω := hconv.continuousOn
    (Filter.Eventually.of_forall (fun j ↦ (hf j).continuousOn)).frequently
  let c := F p
  let e := extChartAt (model n) c
  have hes : IsOpen e.source := isOpen_extChartAt_source c
  have hcs : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨δ,hδ,hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hes.mem_nhds hcs)
  have hnear : Ω ∩ F ⁻¹' ball c (δ/3) ∈ 𝓝 p := inter_mem (hΩ.mem_nhds hp)
    ((hc.continuousAt (hΩ.mem_nhds hp)) (ball_mem_nhds c (by positivity)))
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hKΩ : closedBall p r ⊆ Ω := fun z hz ↦ (hrsub hz).1
  have hFsmall (z : ℂ) (hz : z ∈ closedBall p r) : dist (F z) c < δ/3 := (hrsub hz).2
  have hu : TendstoUniformlyOn f F atTop (closedBall p r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv _ hKΩ (isCompact_closedBall p r)
  have hlate : ∀ᶠ j in atTop, MapsTo (f j) (ball p r) (closedBall c δ) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (δ/3) (by positivity)] with j hj
    intro z hz
    have hzK := ball_subset_closedBall hz
    have hdist : dist (f j z) (F z) < δ/3 := by simpa only [dist_comm] using hj z hzK
    have ht := dist_triangle (f j z) (F z) c
    have hh := hFsmall z hzK
    change dist (f j z) c ≤ δ
    linarith
  have hFmap : MapsTo F (ball p r) (closedBall c δ) := by
    intro z hz
    change dist (F z) c ≤ δ
    exact (hFsmall z (ball_subset_closedBall hz)).le.trans (by linarith)
  have heuc : UniformContinuousOn e (closedBall c δ) :=
    (isCompact_closedBall c δ).uniformContinuousOn_of_continuous ((continuousOn_extChartAt c).mono hδsub)
  have hl : TendstoLocallyUniformlyOn (fun j ↦ e ∘ f j) (e ∘ F) atTop (ball p r) :=
    heuc.comp_tendstoLocallyUniformlyOn (hconv.mono (ball_subset_closedBall.trans hKΩ)) hFmap hlate
  have hhol : ∀ᶠ j in atTop, DifferentiableOn ℂ (e ∘ f j) (ball p r) := by
    filter_upwards [hlate] with j hj
    intro z hz
    have hfj := (hf j).mdifferentiableAt (hΩ.mem_nhds (hKΩ (ball_subset_closedBall hz)))
    have hej : MDifferentiableAt (model n) (model n) e (f j z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hδsub (hj hz))
    exact (hej.comp z hfj).differentiableAt.differentiableWithinAt
  have hpb : p ∈ ball p r := mem_ball_self hr
  have ht := (hl.tendsto_at hpb).prodMk ((hl.deriv hhol isOpen_ball).tendsto_at hpb)
  rw [← nhds_prod_eq] at ht
  have het : e (F p) ∈ (extChartAt (model n) c).target := e.map_source hcs
  have hq := ((g.continuous_quadraticInChart c).continuousAt
    (((isOpen_extChartAt_target c).prod isOpen_univ).mem_nhds ⟨het,mem_univ _⟩)).tendsto.comp ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hfp := hF.mdifferentiableAt (hΩ.mem_nhds hp)
  dsimp only [Function.comp_def,e] at hs
  have heq := curveSpeed_eq_chart g hfp c hcs
  dsimp only [Function.comp_def] at heq
  rw [← heq] at hs
  apply Filter.Tendsto.congr' _ hs
  filter_upwards [hlate] with j hj
  exact (curveSpeed_eq_chart g ((hf j).mdifferentiableAt (hΩ.mem_nhds hp)) c
    (hδsub (hj hpb))).symm

theorem locally_uniform_curveArea_le [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℕ → ℂ → X.Carrier} {F : ℂ → X.Carrier} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (hconv : TendstoLocallyUniformlyOn f F atTop Ω) {C : ℝ≥0∞}
    (hC : ∀ j, curveArea g (f j) Ω ≤ C) : curveArea g F Ω ≤ C := by
  let w (j : ℕ) (z : ℂ) := ENNReal.ofReal (curveSpeed g (f j) z ^ 2)
  have hm (j : ℕ) : AEMeasurable (w j) (volume.restrict Ω) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn ((curveSpeed_continuousOn g hΩ (hf j)).pow 2))).aemeasurable hΩ.measurableSet
  have hl (z : ℂ) (hz : z ∈ Ω) : liminf (fun j ↦ w j z) atTop =
      ENNReal.ofReal (curveSpeed g F z ^ 2) := by
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((locally_uniform_curveSpeed_tendsto g hΩ hf hconv hz).pow 2)).liminf_eq
  calc
    curveArea g F Ω = ∫⁻ z in Ω, liminf (fun j ↦ w j z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
      exact (hl z hz).symm
    _ ≤ liminf (fun j ↦ curveArea g (f j) Ω) atTop := lintegral_liminf_le' hm
    _ ≤ C := by
      exact liminf_le_of_frequently_le (Filter.Eventually.of_forall hC).frequently

end UniversalCoverSplitting

end

end OAI
