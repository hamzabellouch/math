import Mathlib
import OAI.MathematicalPhysics.BFSS.OrbitDensity

namespace OAI

/-! Small slice patches, localized measures and norm moments. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

theorem normalPatch_exists_small (hN : 2 ≤ N) (q : Boson N) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r : ℝ) (b : Boson N → ℝ) (V : Set (Boson N)), 0 < r ∧ r ≤ ρ ∧
      InjOn (M.normalEuclideanChart q) (Metric.closedBall 0 r) ∧
      (∀ x ∈ Metric.closedBall (0 : Boson N) r,
        1/2 < M.normalChartJacobian q x ∧ M.normalChartJacobian q x < 2) ∧
      Continuous b ∧ HasCompactSupport b ∧ (∀ x, 0 ≤ b x) ∧ 0 < b q ∧
      tsupport b ⊆ M.normalEuclideanChart q '' Metric.ball 0 r ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ x ∈ V, M.gaugeAverage hN b x = 1 := by
  let e := (M.normalEuclideanChart_strictFDeriv_zero q).toOpenPartialHomeomorph
    (f' := ContinuousLinearEquiv.refl ℝ (Boson N)) (M.normalEuclideanChart q)
  let W := (M.normalChartJacobian q) ⁻¹' Ioo (1/2) 2
  have hW : IsOpen W := isOpen_Ioo.preimage (M.normalChartJacobian_continuous q)
  have h0W : (0 : Boson N) ∈ W := by
    change 1/2 < M.normalChartJacobian q 0 ∧ M.normalChartJacobian q 0 < 2
    rw [M.normalChartJacobian_zero]
    norm_num
  have h0e : (0 : Boson N) ∈ e.source :=
    (M.normalEuclideanChart_strictFDeriv_zero q).mem_toOpenPartialHomeomorph_source
      (f' := ContinuousLinearEquiv.refl ℝ (Boson N))
  obtain ⟨r₀,hr₀,hr₀sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((e.open_source.inter hW).mem_nhds ⟨h0e,h0W⟩)
  let r := min r₀ ρ
  have hr : 0 < r := lt_min hr₀ hρ
  have hrsub : Metric.closedBall (0 : Boson N) r ⊆ e.source ∩ W :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hr₀sub
  have hbr : Metric.ball (0 : Boson N) r ⊆ e.source :=
    fun _ hx => (hrsub (Metric.ball_subset_closedBall hx)).1
  have hO : IsOpen (M.normalEuclideanChart q '' Metric.ball 0 r) :=
    e.isOpen_image_of_subset_source Metric.isOpen_ball hbr
  have hq : q ∈ M.normalEuclideanChart q '' Metric.ball 0 r :=
    ⟨0,Metric.mem_ball_self hr,M.normalEuclideanChart_zero q⟩
  obtain ⟨s,hs,hssub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hq)
  let f : ContDiffBump q := ⟨s/2,s,half_pos hs,(half_lt_self hs)⟩
  have hfc : Continuous (f : Boson N → ℝ) := f.continuous
  have hfq : (f : Boson N → ℝ) q = 1 :=
    f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
  let c := M.gaugeAverage hN (f : Boson N → ℝ) q / 2
  have hc : 0 < c := half_pos (M.gaugeAverage_pos hN f hfc (fun _ => f.nonneg) q (by rw [hfq]; norm_num))
  let b := M.gaugePatchWeight hN f c
  let V := {x : Boson N | c < M.gaugeAverage hN f x}
  have hbc : Continuous b := M.gaugePatchWeight_continuous hN f hfc hc
  have hbK : HasCompactSupport b := M.gaugePatchWeight_compactSupport hN f f.hasCompactSupport c
  have hbsupp : tsupport b ⊆ tsupport (f : Boson N → ℝ) := by
    apply closure_mono
    intro x hx hz
    apply hx
    simp only [b,gaugePatchWeight,hz,zero_div]
  refine ⟨r,b,V,hr,min_le_right _ _,e.injOn.mono (fun _ hx => (hrsub hx).1),
    (fun _ hx => (hrsub hx).2),hbc,hbK,(fun x => ?_),?_,?_,?_,?_,?_,?_⟩
  · exact div_nonneg f.nonneg (le_trans hc.le (le_max_left _ _))
  · change 0 < f q / max c (M.gaugeAverage hN f q)
    exact div_pos (by rw [hfq]; norm_num) (lt_of_lt_of_le hc (le_max_left _ _))
  · exact hbsupp.trans (by rw [f.tsupport_eq]; exact hssub)
  · exact isOpen_lt continuous_const (M.gaugeAverage_continuous hN f hfc)
  · rintro x ⟨U,hU,rfl⟩
    change c < M.gaugeAverage hN f (M.gaugeAction ⟨U,hU⟩ q)
    rw [M.gaugeAverage_invariant]
    change M.gaugeAverage hN f q / 2 < M.gaugeAverage hN f q
    change 0 < M.gaugeAverage hN f q / 2 at hc
    linarith
  · intro U x
    change (c < M.gaugeAverage hN f (M.gaugeAction U x)) ↔ c < M.gaugeAverage hN f x
    rw [M.gaugeAverage_invariant]
  · intro x hx
    exact M.gaugePatchWeight_average hN f hc x hx.le

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
variable {N : ℕ} (M : AlgebraData N)

lemma sliceLinearEquiv_normal_norm_le (q : Boson N) (v : M.SliceParameter q) :
    ‖v.2‖ ≤ ‖M.sliceLinearEquiv q v‖ := by
  have hv : inner ℝ (v.1 : Boson N) (v.2 : Boson N) = 0 :=
    ((LinearMap.range (M.gaugeTangent q)).mem_orthogonal _).mp v.2.property _ v.1.property
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hv
  rw [M.sliceLinearEquiv_apply]
  change ‖(v.2 : Boson N)‖ ≤ ‖(v.1 : Boson N)+(v.2 : Boson N)‖
  nlinarith [sq_nonneg ‖(v.1 : Boson N)‖,norm_nonneg (v.2 : Boson N),
    norm_nonneg ((v.1 : Boson N)+(v.2 : Boson N))]

lemma normalSliceDensity_eq_zero (q : Boson N) (r : ℝ) (b : Boson N → ℝ)
    (z : M.normalSlice q) (hz : r ≤ ‖z‖) :
    M.normalSliceDensity q (Metric.ball 0 r) b z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  have hn : M.sliceLinearEquiv q (t,z) ∉ Metric.ball (0 : Boson N) r := by
    simp only [Metric.mem_ball,dist_zero_right,not_lt]
    exact hz.trans (M.sliceLinearEquiv_normal_norm_le q (t,z))
  exact Set.indicator_of_notMem hn _

theorem normalSlice_measure_small (hN : 2 ≤ N) (q : Boson N) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧
      (∀ z, ρ ≤ ‖z‖ → J z = 0) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
        (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
        Function.support F ⊆ V →
        (∫ x, F x) = ∫ z : M.normalSlice q, J z * F (q+(z : Boson N)) := by
  obtain ⟨r,b,V,hr,hrρ,hi,_,hb,_,hbn,hbq,hsupp,hV,hqV,hVi,havg⟩ :=
    M.normalPatch_exists_small hN q hρ
  let J := M.normalSliceDensity q (Metric.ball 0 r) b
  have hJ : Continuous J := M.normalSliceDensity_continuous q r b hi hb hsupp
  have hJ0 : 0 < J 0 := M.normalSliceDensity_pos_zero q hr b hi hb hbn hbq hsupp
  refine ⟨J,V,hJ,M.normalSliceDensity_nonneg q _ b hbn,hJ0,?_,hV,hqV,hVi,?_⟩
  · intro z hz
    exact M.normalSliceDensity_eq_zero q r b z (hrρ.trans hz)
  · intro F hF hFK hFi hsF
    rw [M.gaugePatch_integral hN b F hb hF hFK hFi (fun x hx => havg x (hsF hx))]
    exact M.normalSlice_integral q (Metric.ball 0 r) Metric.isOpen_ball.measurableSet
      (hi.mono Metric.ball_subset_closedBall) b F hb hF hFK
      ((subset_tsupport b).trans hsupp) hFi
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] gaugeAction

theorem normalOrbit_measure_small (hN : 2 ≤ N) (q : Boson N) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)) (δ : ℝ),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧
      (∀ z, ρ ≤ ‖z‖ → J z = 0) ∧ 0 < δ ∧
      (∀ z, ‖z‖ < δ → J 0 / 2 < J z ∧ J z < 2 * J 0) ∧
      (∀ U : M.gaugeStabilizer q, ∀ z, J (M.stabilizerNormalIsometry q U z) = J z) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ (h : ℝ), 0 < h → ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
        (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
        (∀ x ∈ Function.support F, h • x ∈ V) →
        (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
          ∫ z : M.normalSlice q, J (h • z) * F (h⁻¹ • q+(z : Boson N)) := by
  obtain ⟨J,V,hJ,hJn,hJ0,hJs,hV,hqV,hVi,hmeasure⟩ := M.normalSlice_measure_small hN q hρ
  let K := M.normalInvariantDensity hN q J
  have hK : Continuous K := M.normalInvariantDensity_continuous hN q J hJ
  have hK0 : 0 < K 0 := by
    dsimp [K]
    rwa [M.normalInvariantDensity_zero]
  have hneigh : {z : M.normalSlice q | K 0 / 2 < K z ∧ K z < 2 * K 0} ∈ nhds 0 := by
    apply (isOpen_lt continuous_const hK |>.inter (isOpen_lt hK continuous_const)).mem_nhds
    change K 0 / 2 < K 0 ∧ K 0 < 2 * K 0
    exact ⟨by linarith,by linarith⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨K,V,r,hK,M.normalInvariantDensity_nonneg hN q J hJn,hK0,?_,hr,?_,
    M.normalInvariantDensity_invariant hN q J,hV,hqV,hVi,?_⟩
  · intro z hz
    apply integral_eq_zero_of_ae
    filter_upwards [] with U
    apply hJs
    simpa only [LinearIsometryEquiv.norm_map] using hz
  · intro z hz
    exact hrsub (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  · intro h hh F hF hFK hFi hs
    apply M.normalSlice_scaled_measure q K V ?_ hh F hF hFK hFi hs
    intro G hG hGK hGi hGs
    rw [hmeasure G hG hGK hGi hGs]
    have hc : Continuous (fun z : M.normalSlice q => G (q+(z : Boson N))) :=
      hG.comp (continuous_const.add continuous_subtype_val)
    have hi (U : M.gaugeStabilizer q) (z : M.normalSlice q) :
        G (q+((M.stabilizerNormalIsometry q U z) : Boson N)) = G (q+(z : Boson N)) := by
      change G (q+M.gaugeAction U z) = G (q+(z : Boson N))
      have hU : M.gaugeAction U q = q := U.prop
      have ha : M.gaugeAction U (q+(z : Boson N)) = q+M.gaugeAction U z := by
        rw [M.gaugeAction_add,hU]
      rw [←ha,hGi]
    exact (M.normalInvariantDensity_integral hN q J _ hJ hc
      (M.normalAffine_compactSupport q G hGK) hi).symm

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] gaugeAction normalSlice massiveDistance

lemma massiveDistance_gauge (h : ℝ) (hh : 0 < h)
    (U : unitary (ColorMatrix N)) (x : Boson N) :
    M.massiveDistance h (M.gaugeAction U x) = M.massiveDistance h x := by
  apply mul_left_cancel₀ hh.ne'
  rw [←M.massiveDistance_rescale h hh,←M.massiveDistance_rescale h hh,
    ←M.gaugeAction_smul,M.gaugeAction_infDist]

theorem normalOrbit_norm_moment (hN : 2 ≤ N) (q : Boson N) (hq : q ∈ M.massiveZeros) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)) (δ : ℝ),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧ 0 < δ ∧
      (∀ z, ‖z‖ < δ → J 0 / 2 < J z ∧ J z < 2 * J 0) ∧
      (∀ U : M.gaugeStabilizer q, ∀ z, J (M.stabilizerNormalIsometry q U z) = J z) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ (h : ℝ), 0 < h → ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
        (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
        (∀ x ∈ Function.support F, h • x ∈ V) →
        (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
          ∫ z : M.normalSlice q, J (h • z) * F (h⁻¹ • q+(z : Boson N)) ∧
        (∫ x, (M.massiveDistance h x)^2 * F x) = (h ^ M.orbitDimension q)⁻¹ *
          ∫ z : M.normalSlice q, ‖z‖^2 * (J (h • z) * F (h⁻¹ • q+(z : Boson N))) := by
  obtain ⟨ρ,hρ,htube⟩ := M.massiveDistance_normal_tube hN
  obtain ⟨J,V,δ,hJ,hJn,hJ0,hJs,hδ,hδJ,hJi,hV,hqV,hVi,hm⟩ :=
    M.normalOrbit_measure_small hN q hρ
  refine ⟨J,V,δ,hJ,hJn,hJ0,hδ,hδJ,hJi,hV,hqV,hVi,?_⟩
  intro h hh F hF hFK hFi hFs
  refine ⟨hm h hh F hF hFK hFi hFs,?_⟩
  let W : Boson N → ℝ := fun x => (M.massiveDistance h x)^2 * F x
  have hW : Continuous W := ((M.massiveDistance_continuous h).pow 2).mul hF
  have hWK : HasCompactSupport W := hFK.mul_left
  have hWi (U : unitary (ColorMatrix N)) (x : Boson N) : W (M.gaugeAction U x) = W x := by
    dsimp [W]
    rw [M.massiveDistance_gauge h hh,hFi]
  have hWs (x : Boson N) (hx : x ∈ Function.support W) : h • x ∈ V := by
    apply hFs x
    intro hz
    exact hx (by simp only [W,hz,mul_zero])
  rw [hm h hh W hW hWK hWi hWs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : h*‖z‖ ≤ ρ
  · have he := htube h hh q hq (z : Boson N) z.prop hz
    dsimp [W]
    rw [he,Submodule.norm_coe]
    ring
  · have hj : J (h • z) = 0 := by
      apply hJs
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh]
      exact (not_le.mp hz).le
    simp only [hj,zero_mul,mul_zero]

end
end BFSSQuantum.AlgebraData
namespace BFSSNormalMeasure
open MeasureTheory
variable {X F : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
omit [MeasurableSpace X] [BorelSpace X] in
lemma square_compact (f : X → F) (hK : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖^2) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hK ⊢
  filter_upwards [hK] with x hx
  change f x = 0 at hx
  change ‖f x‖^2 = 0
  rw [hx, norm_zero, zero_pow (by decide)]
lemma square_integrable (f : X → F) (hf : Continuous f) (hK : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖^2) μ :=
  (hf.norm.pow 2).integrable_of_hasCompactSupport (square_compact f hK)
end BFSSNormalMeasure

end OAI
