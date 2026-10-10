import OAI.Geometry.Riemannian.HarmonicCore.GradientContinuity
import OAI.Geometry.Riemannian.HarmonicCore.Regularization

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma sobolev_continuous_hasFDerivAt (T : ℝ) (u : ZeroSobolev T)
    (U : E3 → ℝ) (W : E3 → E3) (hU : Continuous U) (hW : Continuous W)
    (hUa : U =ᵐ[volume] (sobolevValue T u : E3 → ℝ))
    (hWa : W =ᵐ[volume] (sobolevDerivative T u : E3 → E3)) (x : E3) :
    HasFDerivAt U (InnerProductSpace.toDual ℝ E3 (W x)) x := by
  apply HarmonicCounterexample.Analytic.continuous_weak_hasFDerivAt U
    (fun y ↦ InnerProductSpace.toDual ℝ E3 (W y)) hU
    ((InnerProductSpace.toDual ℝ E3).continuous.comp hW)
  intro φ hφ hsφ a
  calc
    (∫ y, U y*fderiv ℝ φ y a) = ∫ y, (sobolevValue T u) y*fderiv ℝ φ y a := by
      apply integral_congr_ae
      filter_upwards [hUa] with y hy
      rw [hy]
    _ = -(∫ y, φ y*⟪(sobolevDerivative T u) y,a⟫_ℝ) := sobolev_weak_derivative T u hφ hsφ a
    _ = -(∫ y, φ y*(InnerProductSpace.toDual ℝ E3 (W y)) a) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hWa] with y hy
      rw [hy]
      rfl

lemma cutoffSobolev_continuous_representatives (S T : ℝ) (u : ZeroSobolev T)
    (U : E3 → ℝ) (W : E3 → E3)
    (hUa : U =ᵐ[volume.restrict (Metric.ball 0 S)] (sobolevValue T u : E3 → ℝ))
    (hWa : W =ᵐ[volume.restrict (Metric.ball 0 S)] (sobolevDerivative T u : E3 → E3))
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 S)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) :
    (fun x ↦ χ x*U x) =ᵐ[volume]
      (sobolevValue S (cutoffSobolev S T χ hχ hsupp K D hK hD u) : E3 → ℝ) ∧
    (fun x ↦ χ x • W x+U x • gradient χ x) =ᵐ[volume]
      (sobolevDerivative S (cutoffSobolev S T χ hχ hsupp K D hK hD u) : E3 → E3) := by
  have hUall := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hUa
  have hWall := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hWa
  have hz (x : E3) (hx : x ∉ Metric.ball (0:E3) S) : χ x = 0 ∧ gradient χ x = 0 := by
    have hxt : x ∉ tsupport χ := fun h ↦ hx (hsupp h)
    refine ⟨image_eq_zero_of_notMem_tsupport hxt,?_⟩
    change (InnerProductSpace.toDual ℝ E3).symm (fderiv ℝ χ x) = 0
    rw [fderiv_of_notMem_tsupport ℝ hxt,map_zero]
  constructor
  · filter_upwards [hUall,scalarFieldCLM_coe χ hχ.continuous K hK (sobolevValue T u)] with x hx hy
    change χ x*U x = (scalarFieldCLM χ hχ.continuous K hK (sobolevValue T u)) x
    rw [hy]
    by_cases hb : x ∈ Metric.ball (0:E3) S
    · rw [hx hb]; rfl
    · rw [(hz x hb).1]; simp
  · filter_upwards [hUall,hWall,cutoffSobolev_derivative_coe S T χ hχ hsupp K D hK hD u] with x hx hy hz'
    rw [hz']
    by_cases hb : x ∈ Metric.ball (0:E3) S
    · rw [hx hb,hy hb]
    · rw [(hz x hb).1,(hz x hb).2]; simp

theorem sobolev_local_continuous_hasFDerivAt (r S T : ℝ) (hr : 0 < r) (hrS : r < S)
    (u : ZeroSobolev T) (U : E3 → ℝ) (W : E3 → E3) (hU : Continuous U) (hW : Continuous W)
    (hUa : U =ᵐ[volume.restrict (Metric.ball 0 S)] (sobolevValue T u : E3 → ℝ))
    (hWa : W =ᵐ[volume.restrict (Metric.ball 0 S)] (sobolevDerivative T u : E3 → E3))
    (x : E3) (hx : x ∈ Metric.ball (0:E3) r) :
    HasFDerivAt U (InnerProductSpace.toDual ℝ E3 (W x)) x := by
  obtain ⟨χ,D,hχ,hsχ,hK,hD,hχ1,hdχ⟩ := smooth_ball_cutoff r S hr hrS
  let v := cutoffSobolev S T χ hχ hsχ 1 D hK hD u
  obtain ⟨h1,h2⟩ := cutoffSobolev_continuous_representatives S T u U W hUa hWa χ hχ hsχ 1 D hK hD
  have he := sobolev_continuous_hasFDerivAt S v (fun y ↦ χ y*U y)
    (fun y ↦ χ y • W y+U y • gradient χ y) (hχ.continuous.mul hU)
    ((hχ.continuous.smul hW).add (hU.smul (gradient_continuous hχ))) h1 h2 x
  have hxc := Metric.ball_subset_closedBall hx
  rw [hχ1 x hxc,hdχ x hxc,one_smul,smul_zero,add_zero] at he
  apply he.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  rw [hχ1 y (Metric.ball_subset_closedBall hy),one_mul]

theorem metric_weak_classical_first (g : SmoothMetric3) (r S T : ℝ)
    (hr : 0 < r) (hrS : r < S) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T u) x),
        (sobolevDerivative S v) x⟫_ℝ) = 0) :
    ∃ (U : E3 →ᵇ ℝ) (W : E3 → E3), Continuous W ∧
      (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevValue T u : E3 → ℝ) ∧
      W =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevDerivative T u : E3 → E3) ∧
      ∀ x ∈ Metric.ball (0:E3) r, HasFDerivAt (U:E3 → ℝ) (InnerProductSpace.toDual ℝ E3 (W x)) x := by
  classical
  let R := (r+S)/2
  have hrR : r < R := by dsimp [R]; linarith
  have hRS : R < S := by dsimp [R]; linarith
  obtain ⟨B,hB,hBs⟩ := g.metric_weak_interior_sup_L2 R S T (hr.trans hrR) hRS
  obtain ⟨U,hU,hUn⟩ := hBs u hu
  let b := stdOrthonormalBasis ℝ E3
  choose V hV using fun i ↦ g.metric_weak_gradient_continuous R S T (hr.trans hrR) hRS u hu (b i)
  let W : E3 → E3 := fun x ↦ ∑ i,V i x • b i
  have hW : Continuous W := continuous_finsetSum _ (fun i _ ↦ (V i).continuous.smul continuous_const)
  have hWa : W =ᵐ[volume.restrict (Metric.ball 0 R)] (sobolevDerivative T u : E3 → E3) := by
    have hall : ∀ᵐ x ∂volume.restrict (Metric.ball (0:E3) R), ∀ i, V i x = ⟪b i,(sobolevDerivative T u) x⟫_ℝ := by
      rw [ae_all_iff]
      exact hV
    filter_upwards [hall] with x hx
    simpa only [W,hx] using b.sum_repr' ((sobolevDerivative T u) x)
  refine ⟨U,W,hW,ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hrR.le) hU,
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hrR.le) hWa,?_⟩
  exact sobolev_local_continuous_hasFDerivAt r R T hr hrR u U W U.continuous hW hU hWa

lemma metric_weak_C1 (g : SmoothMetric3) (r S T : ℝ)
    (hr : 0 < r) (hrS : r < S) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T u) x),
        (sobolevDerivative S v) x⟫_ℝ) = 0) :
    ∃ U : E3 →ᵇ ℝ, ContDiffOn ℝ 1 (U:E3 → ℝ) (Metric.ball 0 r) ∧
      (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevValue T u : E3 → ℝ) := by
  obtain ⟨U,W,hW,hU,hWa,hd⟩ := g.metric_weak_classical_first r S T hr hrS u hu
  refine ⟨U,?_,hU⟩
  rw [show (1 : WithTop ℕ∞) = 0+1 by simp,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
  refine ⟨by simp,fun x ↦ InnerProductSpace.toDual ℝ E3 (W x),?_,fun x hx ↦ (hd x hx).hasFDerivWithinAt⟩
  exact contDiffOn_zero.mpr (((InnerProductSpace.toDual ℝ E3).continuous.comp hW).continuousOn)

theorem metric_affine_weak_C1 (g : SmoothMetric3) (R : ℝ) (hR : 0 < R)
    {F : E3 → ℝ} (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F) :
    ∃ u : ZeroSobolev R,
      (∀ v : ZeroSobolev R,
        (∫ x, ⟪g.energyOperator x (gradient F x+(sobolevDerivative R u) x),
          (sobolevDerivative R v) x⟫_ℝ) = 0) ∧
      ∀ r : ℝ, 0 < r → r < R → ∃ U : E3 →ᵇ ℝ,
        ContDiffOn ℝ 1 (U:E3 → ℝ) (Metric.ball 0 r) ∧
        (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
          (fun x ↦ F x+(sobolevValue R u) x) := by
  obtain ⟨u,hu,_⟩ := g.metric_affine_weak_dirichlet R hR.le hF hcompact
  obtain ⟨T,hRT,hTs⟩ := compact_test_extension hF hcompact R
  let φ : DirichletTest T := ⟨F,hF,hcompact,hTs⟩
  let w : ZeroSobolev T := testSobolev T φ+includeSobolev hRT u
  have hw : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T w) x),(sobolevDerivative R v) x⟫_ℝ) = 0 := by
    intro v
    rw [←hu v]
    apply integral_congr_ae
    filter_upwards [affineSobolev_derivative hRT φ u] with x hx
    rw [hx]
  refine ⟨u,hu,fun r hr hrR ↦ ?_⟩
  obtain ⟨U,hUc,hU⟩ := g.metric_weak_C1 r R T hr hrR w hw
  exact ⟨U,hUc,hU.trans ((affineSobolev_value hRT φ u).filter_mono ae_restrict_le)⟩

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
