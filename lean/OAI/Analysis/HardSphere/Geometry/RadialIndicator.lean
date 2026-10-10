import Mathlib
import OAI.Analysis.HardSphere.Capacity.IntegralMulSq
import OAI.Analysis.HardSphere.Geometry.Point

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

lemma radial_indicator {K : Set Point} {ω : Point} {R : ℝ}
    (hR : {t : ℝ | 0≤t ∧ t • ω∈K}=Icc 0 R) (a : ℝ → ℝ≥0∞) (H : Point → ℝ≥0∞) :
    (∫⁻ t in Ioi (0:ℝ), a t*(K.indicator H) (t • ω))=
      ∫⁻ t in Ioc (0:ℝ) R, a t*H (t • ω) := by
  classical
  rw [← lintegral_indicator measurableSet_Ioi,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht0 : 0<t
  · have hk : t • ω∈K ↔ t≤R := by
      have he := Set.ext_iff.mp hR t
      simpa only [mem_ofPred_eq,mem_Icc,ht0.le,true_and] using he
    by_cases htR : t≤R
    · simp [ht0,htR,hk.mpr htR]
    · simp [ht0,htR,mt hk.mp htR]
  · simp [ht0]

lemma convex_capacity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {K : Set Point}
    (hk : IsClosed K) (hc : Convex ℝ K) (h0 : (0:Point)∈K)
    {r B : ℝ} (hr : 0<r) (hB : 0≤B) (hb : ∀x∈K,sqRadius x≤B^2)
    (hz : ∀x, sqRadius x≤r^2 → f x=0) :
    (∫⁻ x in K, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ x in K, ENNReal.ofReal (gradSq f x)) := by
  classical
  rw [← lintegral_indicator hk.measurableSet,← lintegral_indicator hk.measurableSet]
  have hm : Measurable (fun x ↦ ENNReal.ofReal (‖f x‖^2)) := by
    simpa only [Pi.pow_apply] using (hf.continuous.norm.pow 2).measurable.ennreal_ofReal
  rw [spherical_integral (K.indicator (fun x ↦ ENNReal.ofReal (‖f x‖^2))) (hm.indicator hk.measurableSet),
    spherical_integral (K.indicator (fun x ↦ ENNReal.ofReal (gradSq f x)))
      (((continuous_gradSq hf).measurable.ennreal_ofReal).indicator hk.measurableSet)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro θ
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro φ
  dsimp only
  obtain ⟨R,hR,hRB,he⟩ := ray_terminal hk hc h0 hB hb (direction_unit φ θ)
  simp only [spherePoint_eq]
  rw [radial_indicator he,radial_indicator he]
  have hweight (t : ℝ) : ENNReal.ofReal (t^2*Real.cos φ)=
      ENNReal.ofReal (Real.cos φ)*ENNReal.ofReal (t^2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  simp_rw [hweight,mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
    mul_comm (ENNReal.ofReal (B^3/(3*r))),mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply RayCapacity.ray_lintegral (f := fun t ↦ f (t • direction φ θ))
    (hf.comp (contDiff_id.smul contDiff_const)) hr hR hRB
  · intro t ht
    apply hz
    rw [sqRadius_smul,direction_unit,mul_one]
    exact pow_le_pow_left₀ ht.1 ht.2 2
  · exact (continuous_gradSq hf).comp (continuous_id.smul continuous_const)
  · intro t
    exact gradSq_nonneg f _
  · intro t _
    exact ray_deriv_bound hf (direction_unit φ θ) t

open scoped Topology

lemma translate_set_lintegral {K : Set Point} (hk : MeasurableSet K) (y : Point)
    (H : Point → ℝ≥0∞) :
    (∫⁻ x in {x | y+x∈K}, H (y+x))=∫⁻x in K,H x := by
  classical
  have hK : MeasurableSet {x : Point | y+x∈K} :=
    hk.preimage (show Measurable (fun x : Point ↦ y+x) from measurable_const.add measurable_id)
  rw [← lintegral_indicator hK,
    ← lintegral_indicator hk]
  have he : ({x | y+x∈K}.indicator (fun x ↦ H (y+x)))=fun x ↦ K.indicator H (y+x) := by
    funext x
    by_cases hx : y+x∈K <;> simp [hx]
  have : (volume : Measure Point).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod,Measure.volume_eq_prod]
    apply Measure.prod.instIsAddLeftInvariant
  rw [he,lintegral_add_left_eq_self]

lemma convex_capacity_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {K : Set Point}
    (hk : IsClosed K) (hc : Convex ℝ K) {y : Point} (hy : y∈K)
    {r B : ℝ} (hr : 0<r) (hB : 0≤B) (hb : ∀x∈K,sqRadius (x-y)≤B^2)
    (hz : ∀x, sqRadius (x-y)≤r^2 → f x=0) :
    (∫⁻ x in K, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ x in K, ENNReal.ofReal (gradSq f x)) := by
  let K' : Set Point := {x | y+x∈K}
  have hkc : IsClosed K' := hk.preimage (continuous_const.add continuous_id)
  have hcv : Convex ℝ K' := by
    intro x hx z hz a b ha hb hab
    change y+(a • x+b • z)∈K
    have he : y+(a • x+b • z)=a • (y+x)+b • (y+z) := by
      rw [smul_add,smul_add]
      calc
        y+(a • x+b • z)=(a+b) • y+(a • x+b • z) := by rw [hab,one_smul]
        _ = _ := by rw [add_smul]; abel
    rw [he]
    exact hc hx hz ha hb hab
  have h := convex_capacity (f := fun x ↦ f (y+x)) (K := K') (hf.comp (contDiff_const.add contDiff_id)) hkc hcv
    (by simpa [K'] using hy) hr hB (by
      intro x hx
      simpa only [add_sub_cancel_left] using hb (y+x) hx) (by
      intro x hx
      apply hz (y+x)
      simpa only [add_sub_cancel_left] using hx)
  have hg (x : Point) : gradSq (fun z ↦ f (y+z)) x=gradSq f (y+x) := by
    simp only [gradSq,fderiv_comp_add_left]
  simp_rw [hg] at h
  dsimp only [K'] at h
  rw [translate_set_lintegral hk.measurableSet y (fun x ↦ ENNReal.ofReal (‖f x‖^2)),
    translate_set_lintegral hk.measurableSet y (fun x ↦ ENNReal.ofReal (gradSq f x))] at h
  exact h

def cube (b : Point) (l : ℝ) : Set Point := Icc b (b+(l,(l,l)))

lemma cube_radius {b y x : Point} {l : ℝ} (hl : 0≤l) (hy : y∈cube b l) (hx : x∈cube b l) :
    sqRadius (x-y)≤(Real.sqrt 3*l)^2 := by
  have hc (u v a : ℝ) (hu : a≤u ∧ u≤a+l) (hv : a≤v ∧ v≤a+l) : (u-v)^2≤l^2 := by
    have h := (sq_le_sq₀ (abs_nonneg (u-v)) hl).mpr (abs_le.mpr ⟨by linarith,by linarith⟩)
    simpa only [sq_abs] using h
  have h1 := hc x.1 y.1 b.1 ⟨hx.1.1,hx.2.1⟩ ⟨hy.1.1,hy.2.1⟩
  have h2 := hc x.2.1 y.2.1 b.2.1 ⟨hx.1.2.1,hx.2.2.1⟩ ⟨hy.1.2.1,hy.2.2.1⟩
  have h3 := hc x.2.2 y.2.2 b.2.2 ⟨hx.1.2.2,hx.2.2.2⟩ ⟨hy.1.2.2,hy.2.2.2⟩
  simp only [sqRadius,Prod.fst_sub,Prod.snd_sub,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  linarith

lemma cube_capacity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {b y : Point} {r l : ℝ}
    (hr : 0<r) (hl : 0≤l) (hy : y∈cube b l)
    (hz : ∀x, sqRadius (x-y)≤r^2 → f x=0) :
    (∫⁻ x in cube b l, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*(∫⁻ x in cube b l, ENNReal.ofReal (gradSq f x)) := by
  have h := convex_capacity_center hf isClosed_Icc (convex_Icc _ _) hy hr
    (mul_nonneg (Real.sqrt_nonneg 3) hl) (fun _ hx ↦ cube_radius hl hy hx) hz
  have he : (Real.sqrt 3*l)^3/(3*r)=Real.sqrt 3*l^3/r := by
    rw [mul_pow,pow_succ (Real.sqrt 3) 2,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
    field_simp
  rw [he] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
