import Mathlib
import OAI.MathematicalPhysics.BFSS.SliceIntegrals

namespace OAI

/-! Gauge patch averages and normal integration patches. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
local instance gaugeMeasurableSpace₂ : MeasurableSpace (unitary (ColorMatrix N)) := borel _
local instance gaugeBorelSpace₂ : BorelSpace (unitary (ColorMatrix N)) := ⟨rfl⟩

def gaugeAverage (hN : 2 ≤ N) (f : Boson N → ℝ) (x : Boson N) : ℝ :=
  ∫ U, f (M.gaugeAction U⁻¹ x) ∂gaugeHaar hN

lemma gaugeAverage_invariant (hN : 2 ≤ N) (f : Boson N → ℝ)
    (U : unitary (ColorMatrix N)) (x : Boson N) :
    M.gaugeAverage hN f (M.gaugeAction U x) = M.gaugeAverage hN f x :=
  M.gauge_average_on_orbit hN f x U

lemma gaugeAverage_continuous (hN : 2 ≤ N) (f : Boson N → ℝ) (hf : Continuous f) :
    Continuous (M.gaugeAverage hN f) := by
  change Continuous (fun x => ∫ U, f (M.gaugeAction U⁻¹ x) ∂gaugeHaar hN)
  let : CompactSpace (unitary (ColorMatrix N)) :=
    isCompact_iff_compactSpace.mp (BFSSOrbit.unitary_compact hN)
  have hc : Continuous (fun p : Boson N × unitary (ColorMatrix N) => (p.2⁻¹,p.1)) :=
    continuous_snd.inv.prodMk continuous_fst
  have hg := M.gaugeAction_continuous.comp hc
  have hh := hf.comp hg
  have hi := continuous_parametric_integral_of_continuous (μ := gaugeHaar hN)
    (f := fun x U => f (M.gaugeAction U⁻¹ x)) hh isCompact_univ
  simpa only [Measure.restrict_univ] using hi

lemma gaugeAverage_pos (hN : 2 ≤ N) (f : Boson N → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (x : Boson N) (hx : 0 < f x) :
    0 < M.gaugeAverage hN f x := by
  let : CompactSpace (unitary (ColorMatrix N)) :=
    isCompact_iff_compactSpace.mp (BFSSOrbit.unitary_compact hN)
  have hc : Continuous (fun U : unitary (ColorMatrix N) => f (M.gaugeAction U⁻¹ x)) :=
    hf.comp ((M.gaugeOrbitMap_continuous x).comp continuous_inv)
  apply integral_pos_of_integrable_nonneg_nonzero hc (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun _ => hn _) (x := (1 : unitary (ColorMatrix N)))
  simpa only [inv_one,M.gaugeAction_one] using hx.ne'

def gaugePatchWeight (hN : 2 ≤ N) (f : Boson N → ℝ) (c : ℝ) (x : Boson N) : ℝ :=
  f x / max c (M.gaugeAverage hN f x)

lemma gaugePatchWeight_continuous (hN : 2 ≤ N) (f : Boson N → ℝ)
    (hf : Continuous f) {c : ℝ} (hc : 0 < c) :
    Continuous (M.gaugePatchWeight hN f c) :=
  hf.div (continuous_const.max (M.gaugeAverage_continuous hN f hf))
    (fun _ => ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _)))

lemma gaugePatchWeight_compactSupport (hN : 2 ≤ N) (f : Boson N → ℝ)
    (hf : HasCompactSupport f) (c : ℝ) : HasCompactSupport (M.gaugePatchWeight hN f c) := by
  apply HasCompactSupport.of_support_subset_isCompact hf
  intro x hx
  apply subset_tsupport f
  intro hz
  apply hx
  simp only [gaugePatchWeight,hz,zero_div]

lemma gaugePatchWeight_average (hN : 2 ≤ N) (f : Boson N → ℝ)
    {c : ℝ} (hc : 0 < c) (x : Boson N) (hx : c ≤ M.gaugeAverage hN f x) :
    M.gaugeAverage hN (M.gaugePatchWeight hN f c) x = 1 := by
  have he (U : unitary (ColorMatrix N)) :
      M.gaugePatchWeight hN f c (M.gaugeAction U⁻¹ x) =
        f (M.gaugeAction U⁻¹ x) / M.gaugeAverage hN f x := by
    rw [gaugePatchWeight,M.gaugeAverage_invariant,max_eq_right hx]
  unfold gaugeAverage at ⊢
  simp_rw [he]
  rw [integral_div]
  exact div_self (ne_of_gt (lt_of_lt_of_le hc hx))

theorem gaugePatch_near_orbit (hN : 2 ≤ N) (q : Boson N)
    (f : Boson N → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfn : ∀ x, 0 ≤ f x) (hfq : 0 < f q) :
    ∃ (b : Boson N → ℝ) (V : Set (Boson N)),
      Continuous b ∧ HasCompactSupport b ∧ (∀ x, 0 ≤ b x) ∧
      Function.support b ⊆ Function.support f ∧ IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ x ∈ V, M.gaugeAverage hN b x = 1 := by
  let c := M.gaugeAverage hN f q / 2
  have hc : 0 < c := half_pos (M.gaugeAverage_pos hN f hf hfn q hfq)
  let V := {x : Boson N | c < M.gaugeAverage hN f x}
  refine ⟨M.gaugePatchWeight hN f c,V,M.gaugePatchWeight_continuous hN f hf hc,
    M.gaugePatchWeight_compactSupport hN f hfc c,?_,?_,?_,?_,?_,?_⟩
  · intro x
    exact div_nonneg (hfn x) (le_trans hc.le (le_max_left _ _))
  · intro x hx
    contrapose! hx
    simp only [Function.mem_support,not_not] at hx ⊢
    simp only [gaugePatchWeight,hx,zero_div]
  · exact isOpen_lt continuous_const (M.gaugeAverage_continuous hN f hf)
  · rintro x ⟨U,hU,rfl⟩
    change c < M.gaugeAverage hN f (M.gaugeAction ⟨U,hU⟩ q)
    rw [M.gaugeAverage_invariant]
    exact half_lt_self (M.gaugeAverage_pos hN f hf hfn q hfq)
  · intro U x
    change (c < M.gaugeAverage hN f (M.gaugeAction U x)) ↔ c < M.gaugeAverage hN f x
    rw [M.gaugeAverage_invariant]
  · intro x hx
    exact M.gaugePatchWeight_average hN f hc x hx.le

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
local instance gaugeMeasurableSpace₃ : MeasurableSpace (unitary (ColorMatrix N)) := borel _
local instance gaugeBorelSpace₃ : BorelSpace (unitary (ColorMatrix N)) := ⟨rfl⟩

theorem gaugeAverage_integral (hN : 2 ≤ N) (b F : Boson N → ℝ)
    (hb : Continuous b) (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFi : ∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) :
    (∫ x, M.gaugeAverage hN b x * F x) = ∫ x, b x * F x := by
  let : CompactSpace (unitary (ColorMatrix N)) :=
    isCompact_iff_compactSpace.mp (BFSSOrbit.unitary_compact hN)
  let g : unitary (ColorMatrix N) → Boson N → ℝ :=
    fun U x => b (M.gaugeAction U⁻¹ x) * F x
  have hact : Continuous (fun p : unitary (ColorMatrix N) × Boson N => (p.1⁻¹,p.2)) :=
    continuous_fst.inv.prodMk continuous_snd
  have hga := M.gaugeAction_continuous.comp hact
  have hgb := hb.comp hga
  have hF' : Continuous (fun p : unitary (ColorMatrix N) × Boson N => F p.2) :=
    hF.comp continuous_snd
  have hg : Continuous g.uncurry := hgb.mul hF' 
  have hgc : HasCompactSupport g.uncurry := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ.prod hFc)
    rintro ⟨U,x⟩ hx
    refine ⟨Set.mem_univ U,subset_tsupport F ?_⟩
    intro he
    exact hx (by simp only [g,Function.uncurry_apply_pair,he,mul_zero])
  have hi (U : unitary (ColorMatrix N)) :
      (∫ x, g U x) = ∫ x, b x * F x := by
    have hp := (M.gaugeAction_measurePreserving U⁻¹).integral_comp
      (M.gaugeIsometry U⁻¹).toHomeomorph.measurableEmbedding
      (fun x => b x * F x)
    change (∫ x, b (M.gaugeAction U⁻¹ x) * F (M.gaugeAction U⁻¹ x)) = _ at hp
    simpa only [g,hFi] using hp
  calc
    (∫ x, M.gaugeAverage hN b x * F x) = ∫ x, ∫ U, g U x ∂gaugeHaar hN := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_mul_const (F x) (fun U => b (M.gaugeAction U⁻¹ x))).symm
    _ = ∫ U, (∫ x, g U x) ∂gaugeHaar hN :=
      (integral_integral_swap_of_hasCompactSupport hg hgc).symm
    _ = ∫ U, (∫ x, b x * F x) ∂gaugeHaar hN := by simp_rw [hi]
    _ = ∫ x, b x * F x := by simp

theorem gaugePatch_integral (hN : 2 ≤ N) (b F : Boson N → ℝ)
    (hb : Continuous b) (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFi : ∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x)
    (hpart : ∀ x ∈ Function.support F, M.gaugeAverage hN b x = 1) :
    (∫ x, F x) = ∫ x, b x * F x := by
  rw [← M.gaugeAverage_integral hN b F hb hF hFc hFi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : F x = 0
  · simp only [hx,mul_zero]
  · rw [hpart x hx,one_mul]

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

theorem normalPatch_exists (hN : 2 ≤ N) (q : Boson N) :
    ∃ (r : ℝ) (b : Boson N → ℝ) (V : Set (Boson N)), 0 < r ∧
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
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((e.open_source.inter hW).mem_nhds ⟨h0e,h0W⟩)
  have hbr : Metric.ball (0 : Boson N) r ⊆ e.source :=
    fun x hx => (hrsub (Metric.ball_subset_closedBall hx)).1
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
  refine ⟨r,b,V,hr,e.injOn.mono (fun x hx => (hrsub hx).1),
    (fun x hx => (hrsub hx).2),hbc,hbK,(fun x => ?_),?_,?_,?_,?_,?_,?_⟩
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

end OAI
