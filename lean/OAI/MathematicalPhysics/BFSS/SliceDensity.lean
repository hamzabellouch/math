import Mathlib
import OAI.MathematicalPhysics.BFSS.GaugeAverages

namespace OAI

/-! Positive continuous slice density and scaled measures. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma normalPatchDensity_nonneg (q : Boson N) (U : Set (Boson N))
    (b : Boson N → ℝ) (hb : ∀ x, 0 ≤ b x) (v : M.SliceParameter q) :
    0 ≤ M.normalPatchDensity q U b v := by
  exact Set.indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (hb _)) _

lemma normalPatchDensity_compact (q : Boson N) (r : ℝ) (b : Boson N → ℝ) :
    HasCompactSupport (M.normalPatchDensity q (Metric.ball 0 r) b) := by
  let K := (M.sliceLinearEquiv q).symm '' Metric.closedBall 0 r
  have hK : IsCompact K := (isCompact_closedBall (0 : Boson N) r).image
    (M.sliceLinearEquiv q).symm.continuous
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro v hv
  have hx : M.sliceLinearEquiv q v ∈ Metric.ball 0 r := by
    by_contra hx
    exact hv (by simp only [normalPatchDensity,Set.indicator_of_notMem hx])
  exact ⟨M.sliceLinearEquiv q v,Metric.ball_subset_closedBall hx,
    (M.sliceLinearEquiv q).symm_apply_apply v⟩

lemma normalPatchDensity_continuous (q : Boson N) (r : ℝ) (b : Boson N → ℝ)
    (hi : InjOn (M.normalEuclideanChart q) (Metric.closedBall 0 r))
    (hb : Continuous b)
    (hsupp : tsupport b ⊆ M.normalEuclideanChart q '' Metric.ball 0 r) :
    Continuous (M.normalPatchDensity q (Metric.ball 0 r) b) := by
  have hw : Continuous (fun x => |M.normalChartJacobian q x| * b (M.normalEuclideanChart q x)) :=
    (M.normalChartJacobian_continuous q).abs.mul (hb.comp (M.normalEuclideanChart_contDiff q).continuous)
  have hfront (x : Boson N) (hx : x ∈ frontier (Metric.ball (0 : Boson N) r)) :
      |M.normalChartJacobian q x| * b (M.normalEuclideanChart q x) = 0 := by
    have hxc : x ∈ Metric.closedBall (0 : Boson N) r :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hx.1
    have hxn : x ∉ Metric.ball (0 : Boson N) r := by
      simpa only [Metric.isOpen_ball.interior_eq] using hx.2
    have hz : b (M.normalEuclideanChart q x) = 0 := by
      by_contra hn
      obtain ⟨y,hy,he⟩ := hsupp (subset_tsupport b hn)
      have hyx := hi (Metric.ball_subset_closedBall hy) hxc he
      exact hxn (hyx ▸ hy)
    rw [hz,mul_zero]
  exact (hw.indicator hfront).comp (M.sliceLinearEquiv q).continuous

lemma normalSliceDensity_continuous (q : Boson N) (r : ℝ) (b : Boson N → ℝ)
    (hi : InjOn (M.normalEuclideanChart q) (Metric.closedBall 0 r))
    (hb : Continuous b)
    (hsupp : tsupport b ⊆ M.normalEuclideanChart q '' Metric.ball 0 r) :
    Continuous (M.normalSliceDensity q (Metric.ball 0 r) b) := by
  let g := M.normalPatchDensity q (Metric.ball 0 r) b
  have hg : Continuous g := M.normalPatchDensity_continuous q r b hi hb hsupp
  have hgK : HasCompactSupport g := M.normalPatchDensity_compact q r b
  let K := Prod.fst '' tsupport g
  have hK : IsCompact K := hgK.image continuous_fst
  have hswap : Continuous (fun p : M.normalSlice q × LinearMap.range (M.gaugeTangent q) =>
      g (p.2,p.1)) := hg.comp continuous_swap
  have hcont := continuous_parametric_integral_of_continuous (μ := (volume : Measure (LinearMap.range (M.gaugeTangent q))))
    (f := fun z t => g (t,z)) hswap hK
  have he : (M.normalSliceDensity q (Metric.ball 0 r) b) =
      (fun z => ∫ t in K, g (t,z)) := by
    funext z
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    by_contra hn
    exact ht ⟨(t,z),subset_tsupport g hn,rfl⟩
  rw [he]
  exact hcont

lemma normalSliceDensity_nonneg (q : Boson N) (U : Set (Boson N))
    (b : Boson N → ℝ) (hb : ∀ x, 0 ≤ b x) (z : M.normalSlice q) :
    0 ≤ M.normalSliceDensity q U b z :=
  integral_nonneg (fun t => M.normalPatchDensity_nonneg q U b hb (t,z))

lemma normalSliceDensity_pos_zero (q : Boson N) {r : ℝ} (hr : 0 < r)
    (b : Boson N → ℝ)
    (hi : InjOn (M.normalEuclideanChart q) (Metric.closedBall 0 r))
    (hb : Continuous b) (hbn : ∀ x, 0 ≤ b x) (hbq : 0 < b q)
    (hsupp : tsupport b ⊆ M.normalEuclideanChart q '' Metric.ball 0 r) :
    0 < M.normalSliceDensity q (Metric.ball 0 r) b 0 := by
  let g := M.normalPatchDensity q (Metric.ball 0 r) b
  have hg : Continuous g := M.normalPatchDensity_continuous q r b hi hb hsupp
  have hgK : HasCompactSupport g := M.normalPatchDensity_compact q r b
  have hc : Continuous (fun t : LinearMap.range (M.gaugeTangent q) => g (t,0)) :=
    hg.comp (continuous_id.prodMk continuous_const)
  have hKs : HasCompactSupport (fun t : LinearMap.range (M.gaugeTangent q) => g (t,0)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hgK.image continuous_fst)
    intro t ht
    exact ⟨(t,0),subset_tsupport g ht,rfl⟩
  apply integral_pos_of_integrable_nonneg_nonzero hc (hc.integrable_of_hasCompactSupport hKs)
    (fun t => M.normalPatchDensity_nonneg q _ b hbn (t,0)) (x := 0)
  have hzero : M.sliceLinearEquiv q (0,0) = 0 := map_zero _
  change g (0,0) ≠ 0
  change (Metric.ball (0 : Boson N) r).indicator
    (fun x => |M.normalChartJacobian q x| * b (M.normalEuclideanChart q x))
      (M.sliceLinearEquiv q (0,0)) ≠ 0
  rw [hzero,Set.indicator_of_mem (Metric.mem_ball_self hr),
    M.normalChartJacobian_zero,M.normalEuclideanChart_zero,abs_one,one_mul]
  exact hbq.ne'

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

theorem normalSlice_measure_exists (hN : 2 ≤ N) (q : Boson N) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)) (δ : ℝ),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧ 0 < δ ∧
      (∀ z, ‖z‖ < δ → J 0 / 2 < J z ∧ J z < 2 * J 0) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
        (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
        Function.support F ⊆ V →
        (∫ x, F x) = ∫ z : M.normalSlice q, J z * F (q+(z : Boson N)) := by
  obtain ⟨r,b,V,hr,hi,_,hb,_,hbn,hbq,hsupp,hV,hqV,hVi,havg⟩ :=
    M.normalPatch_exists hN q
  let J := M.normalSliceDensity q (Metric.ball 0 r) b
  have hJ : Continuous J := M.normalSliceDensity_continuous q r b hi hb hsupp
  have hJ0 : 0 < J 0 := M.normalSliceDensity_pos_zero q hr b hi hb hbn hbq hsupp
  have hneigh : {z : M.normalSlice q | J 0 / 2 < J z ∧ J z < 2 * J 0} ∈ nhds 0 := by
    apply (isOpen_lt continuous_const hJ |>.inter (isOpen_lt hJ continuous_const)).mem_nhds
    change J 0 / 2 < J 0 ∧ J 0 < 2 * J 0
    exact ⟨by linarith,by linarith⟩
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨J,V,δ,hJ,M.normalSliceDensity_nonneg q _ b hbn,hJ0,hδ,?_,hV,hqV,hVi,?_⟩
  · intro z hz
    exact hδsub (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  · intro F hF hFK hFi hsF
    rw [M.gaugePatch_integral hN b F hb hF hFK hFi (fun x hx => havg x (hsF hx))]
    exact M.normalSlice_integral q (Metric.ball 0 r) Metric.isOpen_ball.measurableSet
      (hi.mono Metric.ball_subset_closedBall) b F hb hF hFK
      ((subset_tsupport b).trans hsupp) hFi

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

def orbitDimension (q : Boson N) : ℕ := Module.finrank ℝ (LinearMap.range (M.gaugeTangent q))

lemma orbitDimension_add_normalDimension (q : Boson N) :
    M.orbitDimension q + Module.finrank ℝ (M.normalSlice q) = Module.finrank ℝ (Boson N) :=
  (LinearMap.range (M.gaugeTangent q)).finrank_add_finrank_orthogonal

theorem normalSlice_scaled_measure (q : Boson N)
    (J : M.normalSlice q → ℝ) (V : Set (Boson N))
    (hmeasure : ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
      (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
      Function.support F ⊆ V →
      (∫ x, F x) = ∫ z : M.normalSlice q, J z * F (q+(z : Boson N)))
    {h : ℝ} (hh : 0 < h) (F : Boson N → ℝ)
    (hF : Continuous F) (hFK : HasCompactSupport F)
    (hFi : ∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x)
    (hs : ∀ x ∈ Function.support F, h • x ∈ V) :
    (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
      ∫ z : M.normalSlice q, J (h • z) * F (h⁻¹ • q+(z : Boson N)) := by
  let G (x : Boson N) := F (h⁻¹ • x)
  have hGc : Continuous G := hF.comp (continuous_id.const_smul h⁻¹)
  have hGK : HasCompactSupport G := by
    exact hFK.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hh.ne')).unit)
  have hGi (U : unitary (ColorMatrix N)) (x : Boson N) :
      G (M.gaugeAction U x) = G x := by
    change F (h⁻¹ • M.gaugeAction U x) = F (h⁻¹ • x)
    rw [←M.gaugeAction_smul,hFi]
  have hGs : Function.support G ⊆ V := by
    intro x hx
    have he := hs (h⁻¹ • x) hx
    simpa only [smul_smul,mul_inv_cancel₀ hh.ne',one_smul] using he
  have hm := hmeasure G hGc hGK hGi hGs
  have hamb := Measure.integral_comp_inv_smul (volume : Measure (Boson N)) F h
  rw [abs_of_pos (pow_pos hh _)] at hamb
  change (∫ x, G x) = h ^ Module.finrank ℝ (Boson N) * ∫ x, F x at hamb
  rw [hamb] at hm
  let K (z : M.normalSlice q) := J z * G (q+(z : Boson N))
  have hnor := Measure.integral_comp_smul (volume : Measure (M.normalSlice q)) K h
  rw [abs_of_pos (inv_pos.mpr (pow_pos hh _))] at hnor
  have he : (fun z : M.normalSlice q => K (h • z)) =
      (fun z => J (h • z) * F (h⁻¹ • q+(z : Boson N))) := by
    funext z
    simp only [K,G,Submodule.coe_smul,smul_add,smul_smul,inv_mul_cancel₀ hh.ne',one_smul]
  rw [he] at hnor
  change (∫ z : M.normalSlice q, J (h • z) * F (h⁻¹ • q+(z : Boson N))) =
    (h ^ Module.finrank ℝ (M.normalSlice q))⁻¹ * ∫ z, K z at hnor
  change h ^ Module.finrank ℝ (Boson N) * (∫ x, F x) = ∫ z, K z at hm
  rw [hnor,←hm,←M.orbitDimension_add_normalDimension q,pow_add]
  field_simp

end
end BFSSQuantum.AlgebraData

end OAI
