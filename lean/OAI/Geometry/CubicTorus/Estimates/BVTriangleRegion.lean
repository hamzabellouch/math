import Mathlib
import OAI.Geometry.CubicTorus.Compactness.BVWeyl

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def coordinateTriangle (b l u : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Ioc 0 b ∧ z.1 ∈ Ioc (z.2*l) (z.2*u)}

lemma measurableSet_coordinateTriangle (b l u : ℝ) : MeasurableSet (coordinateTriangle b l u) := by
  exact (measurable_snd measurableSet_Ioc).inter
    ((measurableSet_lt (measurable_snd.mul_const l) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_snd.mul_const u)))

lemma integralOn_coordinateTriangle {f : ℝ × ℝ → ℝ} {b l u : ℝ}
    (hf : IntegrableOn f (coordinateTriangle b l u)) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinateTriangle b l u, f z) =
      ∫ s in (0 : ℝ)..b, ∫ x in (s*l)..(s*u), f (x,s) := by
  rw [← integral_indicator (measurableSet_coordinateTriangle b l u),Measure.volume_eq_prod]
  have hi := hf.integrable_indicator (measurableSet_coordinateTriangle b l u)
  rw [Measure.volume_eq_prod] at hi
  rw [integral_prod_symm _ hi]
  have he (s : ℝ) : (∫ x : ℝ, (coordinateTriangle b l u).indicator f (x,s)) =
      (Ioc (0 : ℝ) b).indicator (fun s ↦ ∫ x in (s*l)..(s*u), f (x,s)) s := by
    by_cases hs : s ∈ Ioc (0 : ℝ) b
    · rw [indicator_of_mem hs,intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hlu hs.1.le)]
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change (coordinateTriangle b l u).indicator f (x,s) =
        (Ioc (s*l) (s*u)).indicator (fun x ↦ f (x,s)) x
      by_cases hx : x ∈ Ioc (s*l) (s*u)
      · erw [indicator_of_mem (show (x,s) ∈ coordinateTriangle b l u from ⟨hs,hx⟩),indicator_of_mem hx]
      · erw [indicator_of_notMem (show (x,s) ∉ coordinateTriangle b l u from fun h ↦ hx h.2),indicator_of_notMem hx]
    · rw [indicator_of_notMem hs]
      apply integral_eq_zero_of_ae
      exact ae_of_all _ (fun x ↦ indicator_of_notMem
        (show (x,s) ∉ coordinateTriangle b l u from fun h ↦ hs h.1) _)
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le hb]

lemma integral_coordinateTriangle {f : ℝ × ℝ → ℝ} (hf : Integrable f)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinateTriangle b l u, f z) =
      ∫ s in (0 : ℝ)..b, ∫ x in (s*l)..(s*u), f (x,s) :=
  integralOn_coordinateTriangle hf.integrableOn hb hlu

theorem integral_coordinateTriangle_divergence {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinateTriangle b l u, planarCoordinateDivergence X Y z) =
      (∫ s in (0 : ℝ)..b, (X (s*u,s)-u*Y (s*u,s))-(X (s*l,s)-l*Y (s*l,s))) +
      (∫ x in (b*l)..(b*u), Y (x,b)) := by
  have hiX : Integrable (fun z : ℝ × ℝ ↦ fderiv ℝ X z (1,0)) :=
    ((hX.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsX.fderiv_apply ℝ (1,0))
  have hiY : Integrable (fun z : ℝ × ℝ ↦ fderiv ℝ Y z (0,1)) :=
    ((hY.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsY.fderiv_apply ℝ (0,1))
  have hi : Integrable (planarCoordinateDivergence X Y) := hiX.add hiY
  rw [integral_coordinateTriangle hi hb hlu]
  exact triangle_coordinate_divergence hX hY hb hlu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

abbrev PrismCoordinates := ℝ × (ℝ × ℝ)

def prismCoordinateDivergence (T X Y : PrismCoordinates → ℝ) (z : PrismCoordinates) : ℝ :=
  fderiv ℝ T z (1,(0,0)) + fderiv ℝ X z (0,(1,0)) + fderiv ℝ Y z (0,(0,1))

def coordinatePrism (a c b l u : ℝ) : Set PrismCoordinates :=
  Ioc a c ×ˢ coordinateTriangle b l u

lemma hasDerivAt_prism_axial {T : PrismCoordinates → ℝ}
    (hT : Differentiable ℝ T) (t : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun v : ℝ ↦ T (v,z)) (fderiv ℝ T (t,z) (1,(0,0))) t := by
  have h : HasDerivAt (fun v : ℝ ↦ (v,z)) (1,(0,0)) t := by
    convert (hasDerivAt_id t).prodMk (hasDerivAt_const t z) using 1; rfl
  exact (hT (t,z)).hasFDerivAt.comp_hasDerivAt t h

lemma prism_planar_coordinate_derivatives {X Y : PrismCoordinates → ℝ}
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) (t : ℝ) (z : ℝ × ℝ) :
    planarCoordinateDivergence (fun w ↦ X (t,w)) (fun w ↦ Y (t,w)) z =
      fderiv ℝ X (t,z) (0,(1,0)) + fderiv ℝ Y (t,z) (0,(0,1)) := by
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ (t,w))
      (ContinuousLinearMap.prod (0 : (ℝ × ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z := by
    exact (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  erw [planarCoordinateDivergence,((hX (t,z)).hasFDerivAt.comp z h).fderiv,
    ((hY (t,z)).hasFDerivAt.comp z h).fderiv]
  rfl

lemma compact_support_prism_slice {X : PrismCoordinates → ℝ}
    (hsX : HasCompactSupport X) (t : ℝ) : HasCompactSupport (fun z : ℝ × ℝ ↦ X (t,z)) := by
  apply hsX.comp_isClosedEmbedding
  have hi : Isometry (fun z : ℝ × ℝ ↦ (t,z)) := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp
  exact hi.isClosedEmbedding

theorem integral_coordinatePrism_divergence {T X Y : PrismCoordinates → ℝ}
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsT : HasCompactSupport T) (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinatePrism a c b l u, prismCoordinateDivergence T X Y z) =
      (∫ z in coordinateTriangle b l u, T (c,z)-T (a,z)) +
      (∫ t in a..c, (∫ s in (0 : ℝ)..b,
        (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))) +
        (∫ x in (b*l)..(b*u), Y (t,(x,b)))) := by
  let DT : PrismCoordinates → ℝ := fun z ↦ fderiv ℝ T z (1,(0,0))
  let DP : PrismCoordinates → ℝ := fun z ↦ fderiv ℝ X z (0,(1,0)) + fderiv ℝ Y z (0,(0,1))
  have iT : Integrable DT :=
    ((hT.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsT.fderiv_apply ℝ (1,(0,0)))
  have iX : Integrable (fun z ↦ fderiv ℝ X z (0,(1,0))) :=
    ((hX.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsX.fderiv_apply ℝ (0,(1,0)))
  have iY : Integrable (fun z ↦ fderiv ℝ Y z (0,(0,1))) :=
    ((hY.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsY.fderiv_apply ℝ (0,(0,1)))
  have iP : Integrable DP := iX.add iY
  have hid : prismCoordinateDivergence T X Y = fun z ↦ DT z + DP z := by
    funext z; dsimp [prismCoordinateDivergence,DT,DP]; ring
  rw [hid,integral_add iT.integrableOn iP.integrableOn]
  congr 1
  · have hi : IntegrableOn DT ((Ioc a c) ×ˢ coordinateTriangle b l u) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact iT.integrableOn
    change (∫ z in (Ioc a c) ×ˢ coordinateTriangle b l u, DT z) = _
    rw [Measure.volume_eq_prod,setIntegral_prod DT hi]
    have hi' : Integrable DT ((volume.restrict (Ioc a c)).prod (volume.restrict (coordinateTriangle b l u))) := by
      rwa [Measure.prod_restrict]
    rw [integral_integral_swap hi']
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change (∫ t in Ioc a c, DT (t,z)) = T (c,z)-T (a,z)
    rw [← intervalIntegral.integral_of_le hac]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_prism_axial (hT.differentiable (by simp)) t z)
      (((hT.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_id.prodMk continuous_const) |>.intervalIntegrable _ _)
  · have hi : IntegrableOn DP ((Ioc a c) ×ˢ coordinateTriangle b l u) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact iP.integrableOn
    change (∫ z in (Ioc a c) ×ˢ coordinateTriangle b l u, DP z) = _
    rw [Measure.volume_eq_prod,setIntegral_prod DP hi,← intervalIntegral.integral_of_le hac]
    apply intervalIntegral.integral_congr
    intro t _
    have hsX' := compact_support_prism_slice hsX t
    have hsY' := compact_support_prism_slice hsY t
    have hX' : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ ↦ X (t,z)) := by fun_prop
    have hY' : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ ↦ Y (t,z)) := by fun_prop
    have he (z : ℝ × ℝ) : DP (t,z) =
        planarCoordinateDivergence (fun w ↦ X (t,w)) (fun w ↦ Y (t,w)) z :=
      (prism_planar_coordinate_derivatives (hX.differentiable (by simp))
        (hY.differentiable (by simp)) t z).symm
    simp_rw [he]
    exact integral_coordinateTriangle_divergence hX' hY' hsX' hsY' hb hlu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma coordinateTriangle_subset_box {b l u : ℝ} (_hb : 0 ≤ b) :
    coordinateTriangle b l u ⊆
      Icc (-b*max |l| |u|) (b*max |l| |u|) ×ˢ Icc 0 b := by
  intro z hz
  have hs0 : 0 ≤ z.2 := hz.1.1.le
  have hs : z.2 ≤ b := hz.1.2
  have hm : 0 ≤ max |l| |u| := le_trans (abs_nonneg l) (le_max_left _ _)
  have hlo : -max |l| |u| ≤ l := by linarith [neg_abs_le l,le_max_left |l| |u|]
  have hup : u ≤ max |l| |u| := le_trans (le_abs_self u) (le_max_right _ _)
  have hh := mul_le_mul_of_nonneg_right hs hm
  have hl := mul_le_mul_of_nonneg_left hlo hs0
  have hu := mul_le_mul_of_nonneg_left hup hs0
  exact ⟨⟨by nlinarith [hz.2.1],by nlinarith [hz.2.2]⟩,hs0,hs⟩

lemma coordinateTriangle_measure_lt_top {b l u : ℝ} (hb : 0 ≤ b) :
    volume (coordinateTriangle b l u) < ⊤ :=
  (measure_mono (coordinateTriangle_subset_box hb)).trans_lt
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top

theorem volume_real_coordinateTriangle {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    volume.real (coordinateTriangle b l u) = b^2*(u-l)/2 := by
  have hi : IntegrableOn (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (coordinateTriangle b l u) :=
    integrableOn_const (coordinateTriangle_measure_lt_top hb).ne
  have he := integralOn_coordinateTriangle hi hb hlu
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ,
    intervalIntegral.integral_const] at he
  have hf : (fun s : ℝ ↦ s*u-s*l) = fun s ↦ (u-l)*s := by funext s; ring
  rw [hf,intervalIntegral.integral_const_mul,integral_id] at he
  convert he using 1; ring

lemma abs_planar_normal_flux {x y : ℝ} (h : x^2+y^2 ≤ 1) (k : ℝ) :
    |x-k*y| ≤ Real.sqrt (1+k^2) := by
  have hk : 0 ≤ 1+k^2 := by positivity
  have hs := Real.sq_sqrt hk
  have h0 := Real.sqrt_nonneg (1+k^2)
  have he := mul_nonneg hk (show 0 ≤ 1-x^2-y^2 by linarith)
  have hsq : (x-k*y)^2 ≤ 1+k^2 := by nlinarith [sq_nonneg (k*x+y)]
  nlinarith [sq_abs (x-k*y),abs_nonneg (x-k*y)]

lemma abs_planar_second_flux {x y : ℝ} (h : x^2+y^2 ≤ 1) : |y| ≤ 1 := by
  nlinarith [sq_nonneg x,sq_abs y,abs_nonneg y]

theorem abs_integral_coordinateTriangle_divergence_le {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    (hn : ∀ z, (X z)^2+(Y z)^2 ≤ 1)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    |∫ z in coordinateTriangle b l u, planarCoordinateDivergence X Y z| ≤
      b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)+(u-l)) := by
  rw [integral_coordinateTriangle_divergence hX hY hsX hsY hb hlu]
  have hface (s : ℝ) :
      |(X (s*u,s)-u*Y (s*u,s))-(X (s*l,s)-l*Y (s*l,s))| ≤
        Real.sqrt (1+l^2)+Real.sqrt (1+u^2) := by
    have hu := abs_planar_normal_flux (hn (s*u,s)) u
    have hl := abs_planar_normal_flux (hn (s*l,s)) l
    exact (abs_sub _ _).trans (by linarith)
  have hfaceint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := b) (fun s _ ↦ show
      ‖(X (s*u,s)-u*Y (s*u,s))-(X (s*l,s)-l*Y (s*l,s))‖ ≤
        Real.sqrt (1+l^2)+Real.sqrt (1+u^2) by simpa only [Real.norm_eq_abs] using hface s)
  have hcapint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := b*l) (b := b*u) (fun x _ ↦ show ‖Y (x,b)‖ ≤ (1 : ℝ) by
      simpa only [Real.norm_eq_abs] using abs_planar_second_flux (hn (x,b)))
  have hbl : b*l ≤ b*u := mul_le_mul_of_nonneg_left hlu hb
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hb,one_mul,
    abs_of_nonneg (sub_nonneg.mpr hbl)] at hfaceint hcapint
  exact (abs_add_le _ _).trans (by nlinarith)

theorem triangular_chord_margin_pos (l u : ℝ) :
    0 < Real.sqrt (1+l^2)+Real.sqrt (1+u^2)-(u-l) := by
  have hl : |l| < Real.sqrt (1+l^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+l^2 by positivity)
    nlinarith [sq_abs l,abs_nonneg l,Real.sqrt_nonneg (1+l^2)]
  have hu : |u| < Real.sqrt (1+u^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+u^2 by positivity)
    nlinarith [sq_abs u,abs_nonneg u,Real.sqrt_nonneg (1+u^2)]
  linarith [neg_abs_le l,le_abs_self u]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def prismRadialFlux (X Y : PrismCoordinates → ℝ) (a c b l u : ℝ) : ℝ :=
  ∫ t in a..c, ∫ s in (0 : ℝ)..b,
    (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))

def prismClosingFlux (T Y : PrismCoordinates → ℝ) (a c b l u : ℝ) : ℝ :=
  (∫ z in coordinateTriangle b l u, T (c,z)-T (a,z)) +
    (∫ t in a..c, ∫ x in (b*l)..(b*u), Y (t,(x,b)))

lemma integral_coordinatePrism_divergence_split {T X Y : PrismCoordinates → ℝ}
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsT : HasCompactSupport T) (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinatePrism a c b l u, prismCoordinateDivergence T X Y z) =
      prismRadialFlux X Y a c b l u + prismClosingFlux T Y a c b l u := by
  rw [integral_coordinatePrism_divergence hT hX hY hsT hsX hsY hac hb hlu]
  have hr : Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..b,
      (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have hc : Continuous (fun t : ℝ ↦ ∫ x in (b*l)..(b*u), Y (t,(x,b))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  rw [intervalIntegral.integral_add (hr.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  dsimp [prismRadialFlux,prismClosingFlux]
  ring

theorem abs_prismClosingFlux_le {T Y : PrismCoordinates → ℝ}
    (hT : ∀ z, |T z| ≤ 1) (hY : ∀ z, |Y z| ≤ 1)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    |prismClosingFlux T Y a c b l u| ≤
      (c-a)*b*(u-l)+b^2*(u-l) := by
  have hcap := norm_setIntegral_le_of_norm_le_const
    (coordinateTriangle_measure_lt_top (l := l) (u := u) hb)
    (f := fun z : ℝ × ℝ ↦ T (c,z)-T (a,z)) (C := (2 : ℝ)) (fun z _ ↦ ?_)
  · have hchord (t : ℝ) : |∫ x in (b*l)..(b*u), Y (t,(x,b))| ≤ b*(u-l) := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := b*l) (b := b*u) (fun x _ ↦ show ‖Y (t,(x,b))‖ ≤ (1 : ℝ) by
          simpa only [Real.norm_eq_abs] using hY (t,(x,b)))
      simp only [Real.norm_eq_abs,one_mul,
        abs_of_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hlu hb))] at hi
      nlinarith
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := c) (fun t _ ↦ show ‖∫ x in (b*l)..(b*u), Y (t,(x,b))‖ ≤ b*(u-l) by
        simpa only [Real.norm_eq_abs] using hchord t)
    rw [volume_real_coordinateTriangle hb hlu,Real.norm_eq_abs] at hcap
    simp only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hac)] at hi
    dsimp [prismClosingFlux]
    exact (abs_add_le _ _).trans (by nlinarith)
  · rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hT (c,z),hT (a,z)])

theorem exists_strict_prism_replacement_scale {a c l u : ℝ}
    (hac : a < c) (hlu : l < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < ε ∧
      (c-a)*b*(u-l)+b^2*(u-l) <
        (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) := by
  let m := Real.sqrt (1+l^2)+Real.sqrt (1+u^2)-(u-l)
  have hm : 0 < m := triangular_chord_margin_pos l u
  let b := min (ε/2) ((c-a)*m/(2*(u-l)))
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hbe : b < ε := (min_le_left _ _).trans_lt (by linarith)
  have hbs : b*(u-l) ≤ (c-a)*m/2 := by
    have hh := min_le_right (ε/2) ((c-a)*m/(2*(u-l)))
    have hd : 0 < 2*(u-l) := by linarith
    have hh' := (le_div_iff₀ hd).mp hh
    dsimp only [b] at *
    nlinarith
  refine ⟨b,hb,hbe,?_⟩
  have hcm : 0 < (c-a)*m := mul_pos (sub_pos.mpr hac) hm
  have hstrict : b*(u-l) < (c-a)*m := by linarith
  have hmul := mul_lt_mul_of_pos_left hstrict hb
  dsimp only [m] at hmul
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma small_oscillation_boundary_flat {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {R δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ R →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {c : Torus} (hc : c ∈ B) {n : Cover} (hnorm : ‖n‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hr16 : r ≤ 1/16)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hosc : 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8*r) < δ^2*(ε/4)^6) :
    ∀ y ∈ B, dist y c < r → |⟪n,shortestLift (y-c)⟫| < ε*r := by
  let t := ε * r / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t ≤ r := by dsimp [t]; nlinarith
  have htR : t ≤ R := htr.trans hrR
  have hquot : t / r = ε / 4 := by dsimp [t]; field_simp
  have hforbid : ∀ a ∈ B, dist a c < r → ∀ b ∈ B, dist b c < r →
      ¬ 2 * t ≤ ⟪n, shortestLift (b - a)⟫ := by
    intro a ha har b hb hbr hh
    have hh' := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hr hr16 ht htr
      hδ har hbr (hd a ha t ht htR).2 (hd b hb t ht htR).1 hh
    rw [hquot] at hh'
    exact (not_lt_of_ge hh') hosc
  intro y hy hyr
  have hcc : dist c c < r := by simpa only [dist_self] using hr
  have hl : ⟪n, shortestLift (y - c)⟫ < 2 * t := lt_of_not_ge (hforbid c hc hcc y hy hyr)
  have he : shortestLift (c - y) = -shortestLift (y - c) := by
    apply shortestLift_eq_of_lift
    · rw [quotientMap_neg, quotientMap_shortestLift]; abel
    · rw [norm_neg, norm_shortestLift, ← dist_eq_norm]
      linarith
  have hk := lt_of_not_ge (hforbid y hy hyr c hc hcc)
  rw [he, inner_neg_right] at hk
  have habs : |⟪n, shortestLift (y - c)⟫| < 2 * t := abs_lt.mpr ⟨by linarith, hl⟩
  apply habs.trans_le
  dsimp [t]
  nlinarith

theorem isMinimizerAt_quantitative_trapping {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ ∀ μ : FiniteMeasure NormalBundle,
      IsNormalMeasure E μ → ∀ N : Torus → Cover, Measurable N →
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
      (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ c ∈ frontier (openRepresentative E), ∀ n : Cover, ‖n‖ = 1 →
      ∀ r ε : ℝ, 0 < r → r ≤ R → 0 < ε → ε ≤ 1/4 →
        131072*normalOscillation (spatialNormalMeasure μ) N c n (8*r) < δ^2*(ε/4)^6 →
        normalCap c n r (ε*r) ⊆ (closure (openRepresentative E))ᶜ ∧
        normalCap c (-n) r (ε*r) ⊆ openRepresentative E := by
  obtain ⟨R,δ,hR,hδ,hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  refine ⟨min R (1/16),δ,by positivity,hδ,?_⟩
  intro μ hμ N hN hp hn c hc n hnorm r ε hr hrs hε hεs hosc
  have hrR := hrs.trans (min_le_left _ _)
  have hr16 := hrs.trans (min_le_right _ _)
  have hbc : c ∈ volumeSupport E ∩ volumeSupport Eᶜ := by
    rwa [isMinimizerAt_frontier_openRepresentative hV hE hmin] at hc
  have hflat := small_oscillation_boundary_flat hE hμ hN hp hn hδ hd hbc hnorm
    hr hrR hr16 hε (by linarith) hosc
  have hflatU : ∀ y ∈ frontier (openRepresentative E), dist y c < r →
      |⟪n,shortestLift (y-c)⟫| < ε*r := by
    rwa [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  have hthreshold : δ^2*(ε/4)^6 ≤ δ^2*(1/8)^6 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 6
  have hout := small_oscillation_outward_cap hE (isOpen_openRepresentative E)
    (isMinimizerAt_openRepresentative_ae hV hE hmin) hμ hN hp hn hnorm hr hr16 hεs hδ
    (hd c hbc (r/8) (by positivity) (by linarith)).2 hflatU (hosc.trans_le hthreshold)
  have hVc : 1-V ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hminc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hn' : ∀ᵐ x ∂(spatialNormalMeasure (μ.map reverseNormal) : Measure Torus), ‖-N x‖ = 1 := by
    simpa only [spatialNormalMeasure_reverse,norm_neg] using hn
  have heq : frontier (openRepresentative Eᶜ) = frontier (openRepresentative E) := by
    rw [isMinimizerAt_frontier_openRepresentative hVc hE.compl hminc,
      isMinimizerAt_frontier_openRepresentative hV hE hmin,compl_compl,inter_comm]
  have hflatC : ∀ y ∈ frontier (openRepresentative Eᶜ), dist y c < r →
      |⟪-n,shortestLift (y-c)⟫| < ε*r := by
    simpa only [heq,inner_neg_left,abs_neg] using hflatU
  have hosceq : normalOscillation (spatialNormalMeasure (μ.map reverseNormal)) (-N) c (-n) (8*r) =
      normalOscillation (spatialNormalMeasure μ) N c n (8*r) := by
    simp only [normalOscillation,spatialNormalMeasure_reverse,Pi.neg_apply,neg_sub_neg,norm_sub_rev n]
  have hin := small_oscillation_outward_cap hE.compl (isOpen_openRepresentative Eᶜ)
    (isMinimizerAt_openRepresentative_ae hVc hE.compl hminc) (isNormalMeasure_compl hE hμ) hN.neg
    (polar_reverse_normal hN hp) hn' (by simpa only [norm_neg] using hnorm) hr hr16 hεs hδ
    (by simpa only [compl_compl] using (hd c hbc (r/8) (by positivity) (by linarith)).1)
    hflatC (by rw [hosceq]; exact hosc.trans_le hthreshold)
  have he : (closure (openRepresentative Eᶜ))ᶜ = openRepresentative E := by
    rw [isMinimizerAt_closure_openRepresentative hVc hE.compl hminc]
    rfl
  exact ⟨hout,he ▸ hin⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma characteristic_symmDiff_abs (E F : Set Torus) (x : Torus) :
    |characteristic F x - characteristic E x| = characteristic (E ∆ F) x := by
  classical
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;>
    simp [characteristic, Set.mem_symmDiff, he, hf]

theorem cutoff_gluing_flux_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hb : ∀ x, w x ∈ Icc 0 1)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x in fundamentalCube,
      ((1 - w x) * characteristic E (quotientMap x) + w x * characteristic F (quotientMap x)) *
        divergence X x) ≤
      (∫ z, 1 - w z.1 ∂(μ : Measure NormalBundle)) +
      (∫ z, w z.1 ∂(ν : Measure NormalBundle)) +
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
  let Y : Cover → Cover := fun x ↦ (1 - w x) • X x
  let Z : Cover → Cover := fun x ↦ w x • X x
  have hY : AdmissibleField Y := admissible_cutoff (contDiff_const.sub hw)
    (fun n x ↦ by rw [hp]) (fun x ↦ by constructor <;> linarith [(hb x).1, (hb x).2]) hX
  have hZ : AdmissibleField Z := admissible_cutoff hw hp hb hX
  let a : Cover → ℝ := fun x ↦ characteristic E (quotientMap x) * divergence Y x
  let b : Cover → ℝ := fun x ↦ characteristic F (quotientMap x) * divergence Z x
  let c : Cover → ℝ := fun x ↦ (characteristic F (quotientMap x) - characteristic E (quotientMap x)) *
    ⟪gradient w x, X x⟫
  have ha : IntegrableOn a fundamentalCube := integrableOn_characteristic_mul hE.nullMeasurableSet
    (integrableOn_divergence hY.1)
  have hb' : IntegrableOn b fundamentalCube := integrableOn_characteristic_mul hF.nullMeasurableSet
    (integrableOn_divergence hZ.1)
  have hi : IntegrableOn (fun x ↦ ⟪gradient w x, X x⟫) fundamentalCube :=
    integrableOn_periodic_continuous ((gradient_contDiff hw).continuous.inner hX.1.continuous)
      (fun n x ↦ by rw [gradient_periodic hp, hX.2.1])
  have hc : IntegrableOn c fundamentalCube := by
    have hh := (integrableOn_characteristic_mul hF.nullMeasurableSet hi).sub
      (integrableOn_characteristic_mul hE.nullMeasurableSet hi)
    simpa only [Pi.sub_def, ← sub_mul, c] using hh
  have hgn : IntegrableOn (fun x ↦ ‖gradient w x‖) fundamentalCube :=
    integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  have heq (x : Cover) :
      ((1 - w x) * characteristic E (quotientMap x) + w x * characteristic F (quotientMap x)) *
        divergence X x = a x + b x - c x := by
    dsimp [a, b, c, Y, Z]
    rw [divergence_smul_function ((contDiff_const.sub hw).differentiable (by simp)).differentiableAt
      (hX.1.differentiable (by simp)).differentiableAt,
      divergence_smul_function (hw.differentiable (by simp)).differentiableAt
      (hX.1.differentiable (by simp)).differentiableAt,
      gradient_const_sub, inner_neg_left]
    ring
  simp_rw [heq]
  have hab : IntegrableOn (fun x ↦ a x + b x) fundamentalCube := by
    simpa only [Pi.add_def] using ha.add hb'
  rw [integral_sub hab hc, integral_add ha hb']
  have hmassE : (∫ x in fundamentalCube, a x) ≤ ∫ z, 1 - w z.1 ∂(μ : Measure NormalBundle) := by
    dsimp only [a]
    simp_rw [characteristic_mul]
    rw [lift_indicator_integral hE.nullMeasurableSet,
      ← normalMeasure_weighted_flux hμ (contDiff_const.sub hw) (fun n x ↦ by rw [hp]) hX]
    have hh : Continuous (fun z : NormalBundle ↦ 1 - w z.1) := by fun_prop
    apply integral_mono ((hh.mul (normalTest X hX.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      (hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro z
    exact mul_le_of_le_one_right (by linarith [(hb z.1).2]) (normalTest_le_one hX z)
  have hmassF : (∫ x in fundamentalCube, b x) ≤ ∫ z, w z.1 ∂(ν : Measure NormalBundle) := by
    dsimp only [b]
    simp_rw [characteristic_mul]
    rw [lift_indicator_integral hF.nullMeasurableSet, ← normalMeasure_weighted_flux hν hw hp hX]
    have hh : Continuous (fun z : NormalBundle ↦ w z.1) := by fun_prop
    apply integral_mono ((hh.mul (normalTest X hX.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      (hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro z
    exact mul_le_of_le_one_right (hb z.1).1 (normalTest_le_one hX z)
  have herr : -(∫ x in fundamentalCube, c x) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
    rw [← integral_neg, ← lift_indicator_integral (hE.symmDiff hF).nullMeasurableSet]
    have hci := integrableOn_characteristic_mul (hE.symmDiff hF).nullMeasurableSet hgn
    simp_rw [← characteristic_mul] at ⊢ hci
    apply integral_mono hc.neg hci
    intro x
    calc
      -c x ≤ |c x| := neg_le_abs _
      _ = characteristic (E ∆ F) (quotientMap x) * |⟪gradient w x, X x⟫| := by
        dsimp only [c]
        rw [abs_mul, characteristic_symmDiff_abs]
      _ ≤ characteristic (E ∆ F) (quotientMap x) * ‖gradient w x‖ := by
        apply mul_le_mul_of_nonneg_left _ (characteristic_nonneg _ _)
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (hX.2.2 x))
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def gluedRegion (E F B : Set Torus) : Set Torus := (E \ B) ∪ (F ∩ B)

lemma measurableSet_gluedRegion {E F B : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hB : MeasurableSet B) :
    MeasurableSet (gluedRegion E F B) := (hE.diff hB).union (hF.inter hB)

lemma characteristic_gluedRegion (E F B : Set Torus) (x : Torus) :
    characteristic (gluedRegion E F B) x =
      (1 - characteristic B x) * characteristic E x + characteristic B x * characteristic F x := by
  classical
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> by_cases hb : x ∈ B <;>
    simp [characteristic, gluedRegion, he, hf, hb]

lemma cutoff_gluing_flux_tendsto {E F B : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hB : MeasurableSet B)
    {w : ℕ → Cover → ℝ} (hw : ∀ i, Continuous (w i))
    (hb : ∀ i x, w i x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ x, Tendsto (fun i ↦ w i x) atTop (𝓝 (characteristic B (quotientMap x))))
    {X : Cover → Cover} (hX : AdmissibleField X) :
    Tendsto (fun i ↦ ∫ x in fundamentalCube,
      ((1 - w i x) * characteristic E (quotientMap x) + w i x * characteristic F (quotientMap x)) *
        divergence X x) atTop
      (𝓝 (∫ x in fundamentalCube ∩ quotientMap ⁻¹' gluedRegion E F B, divergence X x)) := by
  have hg := measurableSet_gluedRegion hE hF hB
  have he : Measurable (fun x : Cover ↦ characteristic E (quotientMap x)) :=
    (measurable_characteristic hE).comp measurable_quotientMap
  have hf : Measurable (fun x : Cover ↦ characteristic F (quotientMap x)) :=
    (measurable_characteristic hF).comp measurable_quotientMap
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict fundamentalCube) (bound := fun x ↦ |divergence X x|)
    (F := fun i x ↦ ((1 - w i x) * characteristic E (quotientMap x) +
      w i x * characteristic F (quotientMap x)) * divergence X x)
    (f := fun x ↦ characteristic (gluedRegion E F B) (quotientMap x) * divergence X x)
    (fun i ↦ ((((measurable_const.sub (hw i).measurable).mul he).add
      ((hw i).measurable.mul hf)).mul (continuous_divergence hX.1).measurable).aestronglyMeasurable)
    (integrableOn_divergence hX.1).abs (fun i ↦ Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ ?_)
  · simpa only [characteristic_mul, lift_indicator_integral hg.nullMeasurableSet] using hlim
  · rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    have he0 := characteristic_nonneg E (quotientMap x)
    have hf0 := characteristic_nonneg F (quotientMap x)
    have he1 := (le_abs_self _).trans (characteristic_bound E (quotientMap x))
    have hf1 := (le_abs_self _).trans (characteristic_bound F (quotientMap x))
    have hw0 := (hb i x).1
    have hw1 := (hb i x).2
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (1 - w i x) * 1 + w i x * 1 := add_le_add
        (mul_le_mul_of_nonneg_left he1 (by linarith)) (mul_le_mul_of_nonneg_left hf1 hw0)
      _ = 1 := by ring
  · rw [characteristic_gluedRegion]
    exact (((tendsto_const_nhds.sub (ht x)).mul tendsto_const_nhds).add
      ((ht x).mul tendsto_const_nhds)).mul tendsto_const_nhds

lemma normalMeasure_sublevelCutoff_tendsto (μ : FiniteMeasure NormalBundle)
    {q : Cover → ℝ} (hq : Continuous q) (hp : ∀ n x, q (x + latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ ∫ z : NormalBundle, sublevelCutoff q t (ε i) z.1 ∂(μ : Measure NormalBundle))
      atTop (𝓝 ((μ : Measure NormalBundle).real {z | q z.1 < t})) := by
  have hh := tendsto_integral_of_dominated_convergence
    (μ := (μ : Measure NormalBundle)) (bound := fun _ ↦ (1 : ℝ))
    (F := fun i z ↦ sublevelCutoff q t (ε i) z.1)
    (f := {z : NormalBundle | q z.1 < t}.indicator (fun _ ↦ (1 : ℝ)))
    (fun i ↦ (show Continuous (fun z : NormalBundle ↦ sublevelCutoff q t (ε i) z.1) from by
      unfold sublevelCutoff; fun_prop).aestronglyMeasurable)
    (integrable_const 1) (fun i ↦ Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sublevelCutoff_mem_Icc q t (ε i) z.1).1]
      exact (sublevelCutoff_mem_Icc q t (ε i) z.1).2)
    (Eventually.of_forall fun z ↦ ?_)
  · have hm : MeasurableSet {z : NormalBundle | q z.1 < t} :=
      isOpen_lt (by fun_prop) continuous_const |>.measurableSet
    simpa only [integral_indicator hm, integral_const, smul_eq_mul, mul_one,
      Measure.real_def, Measure.restrict_apply_univ] using hh
  · have he : characteristic (sublevelRegion q t) (quotientMap z.1) =
        {z : NormalBundle | q z.1 < t}.indicator (fun _ ↦ (1 : ℝ)) z := by
      classical
      by_cases hz : q z.1 < t <;> simp [characteristic, mem_sublevelRegion_quotient hp, hz]
    rw [← he]
    exact sublevelCutoff_tendsto hp hε hεlim t z.1

lemma normalMeasure_integral_one (μ : FiniteMeasure NormalBundle) :
    (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = (μ.mass : ℝ) := by
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real_def,
    ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

theorem perimeter_glued_sublevel_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x)
    {K M t d : ℝ} (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M)
    (hd : HasDerivAt (sublevelVolume (E ∆ F) q) d t) :
    FinitePerimeter (gluedRegion E F (sublevelRegion q t)) ∧
      (perimeter (gluedRegion E F (sublevelRegion q t))).toReal ≤
        (μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t} +
        (ν : Measure NormalBundle).real {z | q z.1 < t} + K * M * d := by
  let ε : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ) + 1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → Cover → ℝ := fun i ↦ sublevelCutoff q t (ε i)
  have hw (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (w i) := sublevelCutoff_contDiff hq t (ε i)
  have hwp (i : ℕ) : ∀ n x, w i (x + latticeVector n) = w i x := sublevelCutoff_periodic hp t (ε i)
  have hwb (i : ℕ) (x : Cover) : w i x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (ε i) x
  have hB := measurableSet_sublevelRegion hq.continuous.measurable t
  have hG := measurableSet_gluedRegion hE hF hB
  let A : ℝ := (μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t} +
    (ν : Measure NormalBundle).real {z | q z.1 < t} + K * M * d
  have hμlim : Tendsto (fun i ↦ ∫ z : NormalBundle, 1 - w i z.1 ∂(μ : Measure NormalBundle))
      atTop (𝓝 ((μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t})) := by
    have hh := (tendsto_const_nhds (x := (μ.mass : ℝ)) (f := atTop)).sub
      (normalMeasure_sublevelCutoff_tendsto μ hq.continuous hp he helim t)
    convert hh using 1
    funext i
    have hi : Integrable (fun z : NormalBundle ↦ w i z.1) (μ : Measure NormalBundle) :=
      (show Continuous (fun z : NormalBundle ↦ w i z.1) from by fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_sub (integrable_const 1) hi, normalMeasure_integral_one]
  have hνlim := normalMeasure_sublevelCutoff_tendsto ν hq.continuous hp he helim t
  have hdlim := tendsto_backward_quotient_of_hasDerivAt hd he helim
  have hright : Tendsto (fun i ↦
      (∫ z : NormalBundle, 1 - w i z.1 ∂(μ : Measure NormalBundle)) +
      (∫ z : NormalBundle, w i z.1 ∂(ν : Measure NormalBundle)) +
      K * M * ((sublevelVolume (E ∆ F) q t - sublevelVolume (E ∆ F) q (t - ε i)) / ε i))
        atTop (𝓝 A) := (hμlim.add hνlim).add (tendsto_const_nhds.mul hdlim)
  have hbound (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' gluedRegion E F (sublevelRegion q t), divergence X x) ≤ A := by
    have hleft := cutoff_gluing_flux_tendsto hE hF hB (fun i ↦ (hw i).continuous) hwb
      (sublevelCutoff_tendsto hp he helim t) hX
    apply le_of_tendsto_of_tendsto' hleft hright
    intro i
    exact (cutoff_gluing_flux_le hE hF hμ hν (hw i) (hwp i) (hwb i) hX).trans
      (add_le_add_right (sublevelCutoff_gradient_integral_le (hE.symmDiff hF) hq hp hK hgrad (he i)) _)
  have hA : 0 ≤ A := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hb : perimeter (gluedRegion E F (sublevelRegion q t)) ≤ ENNReal.ofReal A := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    exact ENNReal.ofReal_le_ofReal (hbound X hX)
  refine ⟨⟨hG.nullMeasurableSet, hb.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  simpa only [ENNReal.toReal_ofReal hA] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

lemma regionDistance_gluedRegion {E F B : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hF : NullMeasurableSet F torusVolume)
    (hB : NullMeasurableSet B torusVolume) :
    regionDistance E (gluedRegion E F B) = torusVolume.real ((E ∆ F) ∩ B) := by
  have heq (x : Torus) : ‖characteristic E x - characteristic (gluedRegion E F B) x‖ =
      characteristic ((E ∆ F) ∩ B) x := by
    classical
    by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> by_cases hb : x ∈ B <;>
      simp [characteristic, gluedRegion, Set.mem_symmDiff, he, hf, hb]
  unfold regionDistance
  simp_rw [heq]
  exact integral_characteristic ((hE.symmDiff hF).inter hB)

theorem isMinimizerAt_local_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (F : Set Torus), MeasurableSet F →
      ∀ (ν : FiniteMeasure NormalBundle), IsNormalMeasure F ν →
      ∀ (q : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ n x, q (x + latticeVector n) = q x) →
      ∀ K M t d : ℝ, (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
      HasDerivAt (sublevelVolume (E ∆ F) q) d t → sublevelVolume (E ∆ F) q t < η →
      (μ : Measure NormalBundle).real {z | q z.1 < t} ≤
        (ν : Measure NormalBundle).real {z | q z.1 < t} + K * M * d +
          C * sublevelVolume (E ∆ F) q t := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η, C, hη, hC, ?_⟩
  intro F hF ν hν q hq hp K M t d hK hgrad hd ht
  obtain ⟨hG, hbound⟩ := perimeter_glued_sublevel_le hE hF hμ hν hq hp hK hgrad hd
  have hdist : regionDistance E (gluedRegion E F (sublevelRegion q t)) =
      sublevelVolume (E ∆ F) q t := regionDistance_gluedRegion hE.nullMeasurableSet
        hF.nullMeasurableSet (measurableSet_sublevelRegion hq.continuous.measurable t).nullMeasurableSet
  have hcomp := hc _ hG (hdist ▸ ht)
  rw [hdist] at hcomp
  rw [hμ.1] at hbound
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma BoundaryFlatAt.exists_small_cone {B : Set Torus} {c : Torus} {n : Cover}
    (hf : BoundaryFlatAt B c n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ B, dist y c < R →
      |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c := by
  obtain ⟨R, hR, heR⟩ := Metric.mem_nhdsWithin_iff.mp (hf (ε / 2) (by positivity))
  refine ⟨R / 2, by positivity, ?_⟩
  intro y hy hyr
  by_cases hyc : y = c
  · subst y
    have hz : shortestLift (0 : Torus) = 0 := shortestLift_eq_of_lift rfl (by norm_num)
    simp [hz]
  · have hd : 0 < dist y c := dist_pos.mpr hyc
    have hh := heR ⟨(show dist (2 * dist y c) 0 < R by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith),
      (show 2 * dist y c ∈ Ioi (0 : ℝ) by change 0 < 2 * dist y c; positivity)⟩
    have hh' := hh y hy (by linarith)
    nlinarith

lemma BoundaryFlatAt.hasFDerivWithinAt_inner_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → Cover} {K : ℝ≥0} (hf : LipschitzWith K f)
    {B : Set Torus} {S : Set X} {a : Torus} {x : X} {n : Cover}
    (hS : ∀ y ∈ S, a + quotientMap (f y) ∈ B)
    (hflat : BoundaryFlatAt B (a + quotientMap (f x)) n) :
    HasFDerivWithinAt (fun y ↦ ⟪n, f y⟫) (0 : X →L[ℝ] ℝ) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨R, hR, hcone⟩ := hflat.exists_small_cone (div_pos hε hK)
  have hlocal : ∀ᶠ y in 𝓝 x, f y ∈ Metric.ball (f x) (min R (1 / 2)) :=
    hf.continuous.continuousAt.eventually (Metric.ball_mem_nhds _ (lt_min hR (by norm_num)))
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlocal] with y hy hyl
  have hdist : dist (a + quotientMap (f y)) (a + quotientMap (f x)) ≤ dist (f y) (f x) := by
    rw [dist_add_left]
    rw [dist_eq_norm, ← quotientMap_sub, dist_eq_norm]
    exact norm_quotientMap_le (f y - f x)
  have hsub : a + quotientMap (f y) - (a + quotientMap (f x)) = quotientMap (f y - f x) := by
    rw [quotientMap_sub]
    abel
  have hsmall : ‖f y - f x‖ < 1 / 2 := by
    rw [← dist_eq_norm]
    exact (show dist (f y) (f x) < min R (1 / 2) from hyl).trans_le (min_le_right _ _)
  have hh := hcone (a + quotientMap (f y)) (hS y hy)
    (hdist.trans_lt ((show dist (f y) (f x) < min R (1 / 2) from hyl).trans_le (min_le_left _ _)))
  rw [hsub, shortestLift_quotientMap hsmall] at hh
  have hb := hf.dist_le_mul y x
  have hc := mul_le_mul_of_nonneg_left (hdist.trans hb) (le_of_lt (div_pos hε hK))
  simp only [zero_apply, sub_zero, ← inner_sub_right, Real.norm_eq_abs]
  rw [← dist_eq_norm]
  calc
    |⟪n, f y - f x⟫| ≤ ε / ((K : ℝ) + 1) * dist (a + quotientMap (f y))
      (a + quotientMap (f x)) := hh
    _ ≤ ε / ((K : ℝ) + 1) * ((K : ℝ) * dist y x) := hc
    _ ≤ ε * dist y x := by
      have hk : (K : ℝ) / ((K : ℝ) + 1) ≤ 1 := (div_le_one hK).mpr (by linarith)
      have hh' := mul_le_mul_of_nonneg_left hk (mul_nonneg hε.le (dist_nonneg : 0 ≤ dist y x))
      calc
        _ = ε * dist y x * ((K : ℝ) / ((K : ℝ) + 1)) := by ring
        _ ≤ ε * dist y x * 1 := hh'
        _ = _ := mul_one _

lemma lipschitz_boundary_parameter_tangent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [Measure.IsAddHaarMeasure ν]
    {f : X → Cover} {K : ℝ≥0} (hf : LipschitzWith K f)
    {B : Set Torus} {S : Set X} {a : Torus} (N : X → Cover)
    (hS : ∀ y ∈ S, a + quotientMap (f y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (f x)) (N x)) :
    ∀ᵐ x ∂ν, x ∈ S → (innerSL ℝ (N x)).comp (fderiv ℝ f x) = 0 := by
  let T := {x ∈ S | DifferentiableAt ℝ f x}
  let L : X → X →L[ℝ] ℝ := fun x ↦ (innerSL ℝ (N x)).comp (fderiv ℝ f x)
  have hL : ∀ x ∈ T, HasFDerivWithinAt (fun _ : X ↦ (0 : ℝ)) (L x) T x := by
    intro x hx
    have hd : HasFDerivWithinAt (fun y : X ↦ ⟪N x, f y⟫) (L x) T x :=
      ((innerSL ℝ (N x)).hasFDerivAt.comp x hx.2.hasFDerivAt).hasFDerivWithinAt
    have hz := (hflat x hx.1).hasFDerivWithinAt_inner_zero hf
      (fun y hy ↦ hS y hy.1) (S := T)
    convert hd.sub hz using 1
    all_goals first | rfl | (funext y; simp) | simp [L]
  have hae := ae_constant_derivative_eq_zero ν T L hL
  filter_upwards [hae, hf.ae_differentiableAt (μ := ν)] with x hx hd
  exact fun hs ↦ hx ⟨hs, hd⟩

lemma normalGraph_hasFDerivAt {n : Cover} {g : Plane → ℝ} {y : Plane}
    (hg : DifferentiableAt ℝ g y) :
    HasFDerivAt (normalGraph n g)
      ((normalPlaneLinearIsometry n).toContinuousLinearMap + (fderiv ℝ g y).smulRight n) y := by
  exact (normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt.add
    (hg.hasFDerivAt.smul_const n)

lemma normalGraph_tangent_ae {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : Set Torus} {S : Set Plane} {a : Torus} (N : Plane → Cover)
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) (N x)) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S → ∀ v : Plane,
      ⟪N x, normalPlaneEmbedding n v + (fderiv ℝ g x v) • n⟫ = 0 := by
  have hh := lipschitz_boundary_parameter_tangent volume (normalGraph_lipschitz hn hg) N hS hflat
  filter_upwards [hh, hg.ae_differentiableAt (μ := (volume : Measure Plane))] with x hx hd hs v
  have he := congrArg (fun q : Plane →L[ℝ] ℝ ↦ q v) (hx hs)
  rw [(normalGraph_hasFDerivAt hd).fderiv] at he
  exact he

end CubicTorus

end
end

end

end OAI
