import Mathlib
import OAI.Geometry.CubicTorus.Profiles.PlanarProfile

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma rho_rational (k : ℝ) : rho k = 2 * Real.sqrt Real.pi * k / rhoDen k := by
  have hs : rhoRoot k = 2 * Real.sqrt (1 + Real.pi * k ^ 2 / 4) := by
    have h1 := rhoRoot_sq k
    have h2 := Real.sq_sqrt (show 0 ≤ 1 + Real.pi * k ^ 2 / 4 by positivity)
    have h3 := rhoRoot_pos k
    have h4 := Real.sqrt_nonneg (1 + Real.pi * k ^ 2 / 4)
    nlinarith
  have ha := Real.sq_sqrt Real.pi_pos.le
  have hd := ne_of_gt (rhoDen_pos k)
  apply (eq_div_iff hd).2
  unfold rho rhoDen
  rw [hs, show Real.pi / 4 * k ^ 2 = Real.pi * k ^ 2 / 4 by ring]
  have hz := Real.sq_sqrt (show 0 ≤ 1 + Real.pi * k ^ 2 / 4 by positivity)
  linear_combination Real.sqrt Real.pi * k * 2 * hz +
    k ^ 2 * Real.sqrt (1 + Real.pi * k ^ 2 / 4) * ha

lemma hasDerivAt_rhoRoot (k : ℝ) :
    HasDerivAt rhoRoot (Real.pi * k / rhoRoot k) k := by
  convert ((((hasDerivAt_id k).pow 2).const_mul Real.pi).add_const 4).sqrt
    (by positivity : Real.pi * k ^ 2 + 4 ≠ 0) using 1 <;> try rfl
  dsimp [rhoRoot]
  ring

lemma hasDerivAt_rho (k : ℝ) : HasDerivAt rho (rhoSlope k) k := by
  have heq : rho = fun k ↦ 2 * Real.sqrt Real.pi * k / rhoDen k := funext rho_rational
  rw [heq]
  have hh := ((hasDerivAt_id k).const_mul (2 * Real.sqrt Real.pi)).div
    ((hasDerivAt_rhoRoot k).add ((hasDerivAt_id k).const_mul (Real.sqrt Real.pi)))
    (ne_of_gt (rhoDen_pos k))
  convert hh using 1 <;> try rfl
  dsimp [rhoSlope, rhoDen]
  have hs := ne_of_gt (rhoRoot_pos k)
  have hd : rhoRoot k + Real.sqrt Real.pi * k ≠ 0 := ne_of_gt (rhoDen_pos k)
  field_simp
  linear_combination -2 * rhoRoot_sq k

lemma continuous_rho : Continuous rho :=
  continuous_iff_continuousAt.2 (fun k ↦ (hasDerivAt_rho k).continuousAt)

lemma contDiff_rho {n : WithTop ℕ∞} : ContDiff ℝ n rho := by
  unfold rho
  have hs : ContDiff ℝ n (fun k : ℝ ↦ Real.sqrt (1 + Real.pi / 4 * k ^ 2)) :=
    (by fun_prop : ContDiff ℝ n (fun k : ℝ ↦ 1 + Real.pi / 4 * k ^ 2)).sqrt
      (fun k ↦ by positivity)
  exact ((contDiff_const.mul contDiff_id).mul hs).sub
    (contDiff_const.mul (contDiff_id.pow 2))

lemma antitoneOn_rhoSlope : AntitoneOn rhoSlope (Ici 0) := by
  intro k hk K hK hkK
  change 0 ≤ k at hk
  change 0 ≤ K at hK
  have hroot : rhoRoot k ≤ rhoRoot K := Real.sqrt_le_sqrt
    (add_le_add (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hk hK).2 hkK) Real.pi_pos.le) le_rfl)
  have hden : rhoDen k ≤ rhoDen K := add_le_add hroot
    (mul_le_mul_of_nonneg_left hkK (Real.sqrt_nonneg _))
  have hprod : rhoRoot k * rhoDen k ^ 2 ≤ rhoRoot K * rhoDen K ^ 2 :=
    mul_le_mul hroot (pow_le_pow_left₀ (rhoDen_pos k).le hden 2)
      (sq_nonneg _) (rhoRoot_pos K).le
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos (rhoRoot_pos k) (sq_pos_of_pos (rhoDen_pos k))) hprod

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma deriv_rho_eq : deriv rho = rhoSlope := funext (fun k ↦ (hasDerivAt_rho k).deriv)

lemma concaveOn_rho : ConcaveOn ℝ (Ici 0) rho := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuous_rho.continuousOn
    (fun k _ ↦ (hasDerivAt_rho k).differentiableAt.differentiableWithinAt)
  rw [deriv_rho_eq]
  exact antitoneOn_rhoSlope.mono interior_subset

lemma rhoSlope_nonneg (k : ℝ) : 0 ≤ rhoSlope k := by
  unfold rhoSlope
  exact div_nonneg (by positivity) (mul_nonneg (rhoRoot_pos k).le (sq_nonneg _))

lemma mul_rhoSlope_le {k : ℝ} (hk : 0 ≤ k) : k * rhoSlope k ≤ rho k := by
  rcases eq_or_lt_of_le hk with hzero | hpos
  · rw [← hzero, rho_zero, zero_mul]
  · have hs := concaveOn_rho.deriv_le_slope (show 0 ∈ Ici (0 : ℝ) by simp)
      hk hpos (hasDerivAt_rho k).differentiableAt
    rw [slope_def_field, rho_zero, sub_zero, sub_zero, deriv_rho_eq] at hs
    simpa only [mul_comm] using (le_div_iff₀ hpos).1 hs

lemma second_deriv_rho_nonpos {k : ℝ} (hk : 0 < k) : deriv (deriv rho) k ≤ 0 := by
  rw [deriv_rho_eq]
  have hh := antitoneOn_rhoSlope.derivWithin_nonpos (x := k)
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hk)] at hh
  exact hh

lemma hasDerivAt_divParam (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun h ↦ X / h) (-X / h ^ 2) h := by
  convert (hasDerivAt_const h X).div (hasDerivAt_id h) hh using 1 <;> try rfl
  simp

lemma hasDerivAt_divParamSlope (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun h ↦ -X / h ^ 2) (2 * X / h ^ 3) h := by
  convert (hasDerivAt_const h (-X)).div ((hasDerivAt_id h).pow 2) (pow_ne_zero 2 hh) using 1 <;> try rfl
  dsimp
  field_simp
  ring

lemma second_deriv_comp_div {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ f (X / H))) h =
      deriv (deriv f) (X / h) * (X / h ^ 2) ^ 2 + deriv f (X / h) * (2 * X / h ^ 3) := by
  have heq : deriv (fun H ↦ f (X / H)) =ᶠ[𝓝 h]
      (fun H ↦ deriv f (X / H) * (-X / H ^ 2)) := by
    filter_upwards [eventually_ne_nhds hh] with H hH
    exact (((hf.contDiffAt.differentiableAt (by norm_num)).hasDerivAt).comp H
      (hasDerivAt_divParam X hH)).deriv
  rw [heq.deriv_eq]
  have hfd : DifferentiableAt ℝ (deriv f) (X / h) :=
    ((hf.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hd := ((hfd.hasDerivAt.comp h (hasDerivAt_divParam X hh)).mul
    (hasDerivAt_divParamSlope X hh)).deriv
  convert hd using 1 <;> try rfl
  dsimp only [Function.comp_apply]
  ring

lemma rho_comp_div_second_bound {X h : ℝ} (hX : 0 < X) (hh : 0 < h) :
    deriv (deriv (fun H ↦ rho (X / H))) h ≤ 2 / h ^ 2 := by
  rw [second_deriv_comp_div contDiff_rho X (ne_of_gt hh)]
  have hk := div_pos hX hh
  have hn := mul_nonpos_of_nonpos_of_nonneg (second_deriv_rho_nonpos hk) (sq_nonneg (X / h ^ 2))
  have hb := (mul_rhoSlope_le hk.le).trans (rho_spec hk.le).2.1.le
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2 / h ^ 2 by positivity)
  rw [deriv_rho_eq] at hn ⊢
  have heq : X / h * rhoSlope (X / h) * (2 / h ^ 2) = rhoSlope (X / h) * (2 * X / h ^ 3) := by
    field_simp
  rw [heq] at hm
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

lemma second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  rw [hz] at hneg
  exact (lt_irrefl 0) hneg

lemma second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y => f y - g y)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have heq : deriv (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => deriv f y - deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_sub (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_sub
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

structure UpperSupport (I C : ℝ → ℝ) (x : ℝ) : Prop where
  smooth : ContDiffAt ℝ 2 C x
  contact : C x = I x
  above : ∀ᶠ y in 𝓝 x, I y ≤ C y

lemma jet_comparison {I C F : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMin (fun y => I y - F y) x) :
    deriv C x = deriv F x ∧ deriv (deriv F) x ≤ deriv (deriv C) x := by
  have hmc : IsLocalMin (fun y => C y - F y) x := by
    filter_upwards [hm, hs.above] with y hy habove
    change C x - F x ≤ C y - F y
    rw [hs.contact]
    linarith
  have h1 := hmc.deriv_eq_zero
  change deriv (C - F) x = 0 at h1
  rw [deriv_sub (hs.smooth.differentiableAt (by norm_num))
    (hF.differentiableAt (by norm_num))] at h1
  have h2 := second_deriv_nonneg_of_local_min hmc (hs.smooth.continuousAt.sub hF.continuousAt)
  rw [second_deriv_sub hs.smooth hF] at h2
  exact ⟨sub_eq_zero.mp h1, sub_nonneg.mp h2⟩

lemma second_deriv_quadratic (α β γ x : ℝ) :
    deriv (deriv (fun y => α * y ^ 2 + β * y + γ)) x = 2 * α := by
  have hd (y : ℝ) : HasDerivAt (fun z => α * z ^ 2 + β * z + γ) (2 * α * y + β) y := by
    convert! (((hasDerivAt_pow 2 y).const_mul α).add
      ((hasDerivAt_id y).const_mul β)).add_const γ using 1
    ring
  have hdeq : deriv (fun y => α * y ^ 2 + β * y + γ) = (fun y => 2 * α * y + β) := by
    funext y
    exact (hd y).deriv
  rw [hdeq]
  have hd2 : HasDerivAt (fun y : ℝ => 2 * α * y + β) (2 * α) x := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul (2 * α)).add_const β
  exact hd2.deriv

theorem chord_below_of_upper_support {I : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) :
    ∀ x ∈ Icc a b, I a + (x - a) * (I b - I a) / (b - a) ≤ I x := by
  intro c hc
  by_contra! hgap
  let m := (I b - I a) / (b - a)
  let L := fun x : ℝ => I a + (x - a) * m
  have hLa : L a = I a := by simp [L]
  have hLb : L b = I b := by
    dsimp [L, m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hgap' : I c < L c := by simpa [L, m, mul_div_assoc] using hgap
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    intro heq
    subst c
    rw [hLa] at hgap'
    exact (lt_irrefl _ hgap')
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    intro heq
    subst c
    rw [hLb] at hgap'
    exact (lt_irrefl _ hgap')
  let ε := (L c - I c) / (2 * ((c - a) * (b - c)))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap')
    (mul_pos (by norm_num) (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hcb)))
  let F := fun x : ℝ => ε * x ^ 2 + (m - ε * (a + b)) * x +
    (I a - a * m + ε * a * b)
  have hF_eq (x : ℝ) : F x = L x + ε * (x - a) * (x - b) := by dsimp [F, L]; ring
  have hFa : F a = I a := by rw [hF_eq, hLa]; ring
  have hFb : F b = I b := by rw [hF_eq, hLb]; ring
  have hFc : I c < F c := by
    have hprod : ε * (c - a) * (b - c) = (L c - I c) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt (sub_pos.mpr hca), ne_of_gt (sub_pos.mpr hcb)]
    rw [hF_eq]
    nlinarith
  have hF : ContDiff ℝ 2 F := by dsimp [F]; fun_prop
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hI.sub hF.continuous.continuousOn)
  have hneg : I x - F x < 0 := lt_of_le_of_lt (hmin hc) (sub_neg.mpr hFc)
  have hxa : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro heq
    subst x
    rw [hFa, sub_self] at hneg
    exact lt_irrefl _ hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro heq
    subst x
    rw [hFb, sub_self] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨C, hC, hC''⟩ := hsupport x ⟨hxa, hxb⟩
  have hj := (jet_comparison hC hF.contDiffAt
    (hmin.isLocalMin (Icc_mem_nhds hxa hxb))).2
  have hF'' : deriv (deriv F) x = 2 * ε := second_deriv_quadratic _ _ _ _
  rw [hF''] at hj
  linarith

end CubicTorus.Reduction

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

theorem concaveOn_of_upper_support {I : ℝ → ℝ} {a b : ℝ}
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) : ConcaveOn ℝ (Icc a b) I := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hx.1 hz.2
  have hc := chord_below_of_upper_support (hxy.trans hyz) (hI.mono hsub)
    (fun t ht ↦ hsupport t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hz.2⟩) y ⟨hxy.le, hyz.le⟩
  have hdiv : (y - x) * (I z - I x) / (z - x) ≤ I y - I x := by linarith only [hc]
  have hm := (div_le_iff₀ (sub_pos.2 (hxy.trans hyz))).1 hdiv
  apply (div_le_div_iff₀ (sub_pos.2 hyz) (sub_pos.2 hxy)).2
  nlinarith only [hm]

lemma UpperSupport.sub_quadratic {I C : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (K : ℝ) :
    UpperSupport (fun y ↦ I y - K / 2 * y ^ 2) (fun y ↦ C y - K / 2 * y ^ 2) x := by
  refine ⟨hs.smooth.sub (by fun_prop), ?_, ?_⟩
  · rw [hs.contact]
  · filter_upwards [hs.above] with y hy
    exact sub_le_sub_right hy _

lemma second_deriv_half_quadratic (K x : ℝ) :
    deriv (deriv (fun y : ℝ ↦ K / 2 * y ^ 2)) x = K := by
  simp

theorem concaveOn_sub_quadratic_of_support {I : ℝ → ℝ} {a b K : ℝ}
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ K) :
    ConcaveOn ℝ (Icc a b) (fun y ↦ I y - K / 2 * y ^ 2) := by
  apply concaveOn_of_upper_support (hI.sub (by fun_prop))
  intro x hx
  obtain ⟨C, hC, hCK⟩ := hsupport x hx
  refine ⟨_, hC.sub_quadratic K, ?_⟩
  rw [second_deriv_sub hC.smooth (by fun_prop), second_deriv_half_quadratic]
  linarith

end CubicTorus.Reduction

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

def sectionLength (X h : ℝ) : ℝ :=
  min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h)))

lemma continuousOn_sectionLength_h (X : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (sectionLength X) (Icc a b) := by
  have hdiv : ContinuousOn (fun h : ℝ ↦ X / h) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun h hh ↦ ne_of_gt (ha.trans_le hh.1))
  exact (continuousOn_const.mul (hdiv.pow 2)).inf
    (hdiv.inf (continuous_rho.comp_continuousOn hdiv))

lemma contDiffAt_rho_comp_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ContDiffAt ℝ 2 (fun H ↦ rho (X / H)) h :=
  contDiff_rho.contDiffAt.comp h (contDiffAt_const.div contDiffAt_id hh)

lemma second_deriv_quadratic_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ Real.pi * (X / H) ^ 2)) h =
      6 * (Real.pi * (X / h) ^ 2) / h ^ 2 := by
  rw [second_deriv_comp_div (f := fun k : ℝ ↦ Real.pi * k ^ 2) (by fun_prop) X hh]
  have hd : deriv (fun k : ℝ ↦ Real.pi * k ^ 2) (X / h) = 2 * Real.pi * (X / h) := by
    convert ((((hasDerivAt_id (X / h)).pow 2).const_mul Real.pi).deriv) using 1 <;> try rfl
    dsimp
    ring
  have hd2 : deriv (deriv (fun k : ℝ ↦ Real.pi * k ^ 2)) (X / h) = 2 * Real.pi := by
    have := second_deriv_quadratic Real.pi 0 0 (X / h)
    simpa only [zero_mul, add_zero] using this
  rw [hd, hd2]
  ring

lemma second_deriv_linear_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ X / H)) h = 2 * (X / h) / h ^ 2 := by
  have heq : deriv (fun H ↦ X / H) =ᶠ[𝓝 h] (fun H ↦ -X / H ^ 2) := by
    filter_upwards [eventually_ne_nhds hh] with H hH
    exact (hasDerivAt_divParam X hH).deriv
  rw [heq.deriv_eq, (hasDerivAt_divParamSlope X hh).deriv]
  ring

lemma sectionLength_upper_support {X h : ℝ} (hX : 0 ≤ X) (hh : 0 < h) :
    ∃ C : ℝ → ℝ, UpperSupport (sectionLength X) C h ∧
      deriv (deriv C) h ≤ 2 / h ^ 2 := by
  rcases hX.eq_or_lt with hX | hX
  · subst X
    refine ⟨fun _ ↦ 0, ⟨by fun_prop, by simp [sectionLength, rho_zero], ?_⟩, ?_⟩
    · exact Filter.Eventually.of_forall (fun H ↦ by simp [sectionLength, rho_zero])
    · norm_num
      positivity
  let k := X / h
  have hk : 0 < k := div_pos hX hh
  have hne : h ≠ 0 := ne_of_gt hh
  by_cases hquad : Real.pi * k ^ 2 ≤ min k (rho k)
  · refine ⟨fun H ↦ Real.pi * (X / H) ^ 2, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact contDiffAt_const.mul ((contDiffAt_const.div contDiffAt_id hne).pow 2)
    · exact (min_eq_left hquad).symm
    · exact Filter.Eventually.of_forall (fun H ↦ min_le_left _ _)
    · rw [second_deriv_quadratic_div X hne]
      have hqk : Real.pi * k ^ 2 ≤ k := hquad.trans (min_le_left _ _)
      have hpk : Real.pi * k ≤ 1 := by
        have : k * (Real.pi * k) ≤ k * 1 := by nlinarith only [hqk]
        exact (mul_le_mul_iff_right₀ hk).1 this
      have hkp : k ≤ 1 / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by nlinarith only [hpk])
      have hb : 6 * (Real.pi * k ^ 2) ≤ 2 := by
        have hp : (6 : ℝ) / Real.pi < 2 := (div_lt_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
        have hm := mul_le_mul_of_nonneg_left (hqk.trans hkp) (by norm_num : (0 : ℝ) ≤ 6)
        rw [mul_one_div] at hm
        exact hm.trans hp.le
      exact div_le_div_of_nonneg_right hb (sq_nonneg h)
  · by_cases hlin : k ≤ rho k
    · refine ⟨fun H ↦ X / H, ⟨contDiffAt_const.div contDiffAt_id hne, ?_, ?_⟩, ?_⟩
      · change k = min (Real.pi * k ^ 2) (min k (rho k))
        rw [min_eq_right (le_of_not_ge hquad), min_eq_left hlin]
      · exact Filter.Eventually.of_forall (fun H ↦ (min_le_right _ _).trans (min_le_left _ _))
      · rw [second_deriv_linear_div X hne]
        have hk1 := hlin.trans (rho_spec hk.le).2.1.le
        exact div_le_div_of_nonneg_right (by nlinarith only [hk1]) (sq_nonneg h)
    · refine ⟨fun H ↦ rho (X / H), ⟨contDiffAt_rho_comp_div X hne, ?_, ?_⟩,
        rho_comp_div_second_bound hX hh⟩
      · change rho k = min (Real.pi * k ^ 2) (min k (rho k))
        rw [min_eq_right (le_of_not_ge hquad), min_eq_right (le_of_not_ge hlin)]
      · exact Filter.Eventually.of_forall (fun H ↦ (min_le_right _ _).trans (min_le_right _ _))

theorem concaveOn_sectionLength_corrected {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ sectionLength X h - h ^ 2 / a ^ 2) := by
  have hc := concaveOn_sub_quadratic_of_support (a := a) (b := b) (K := 2 / a ^ 2)
    (continuousOn_sectionLength_h X ha) (fun h hh ↦ ?_)
  · convert hc using 1
    funext h
    ring
  · obtain ⟨C, hC, hbound⟩ := sectionLength_upper_support hX (ha.trans hh.1)
    refine ⟨C, hC, hbound.trans ?_⟩
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
      (pow_le_pow_left₀ ha.le hh.1.le 2)

lemma continuous_sectionLength_X (h : ℝ) : Continuous (fun X ↦ sectionLength X h) := by
  unfold sectionLength
  exact ((continuous_const.mul ((continuous_id.div_const h).pow 2)).inf
    ((continuous_id.div_const h).inf (continuous_rho.comp (continuous_id.div_const h))))

lemma concaveOn_rho_div_corrected {X a b : ℝ} (hX : 0 < X) (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ rho (X / h) - h ^ 2 / a ^ 2) := by
  have hc := concaveOn_sub_quadratic_of_support (I := fun h ↦ rho (X / h))
    (a := a) (b := b) (K := 2 / a ^ 2)
    (continuous_rho.comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun h hh ↦ ne_of_gt (ha.trans_le hh.1))))
    (fun h hh ↦ ?_)
  · convert hc using 1
    funext h
    ring
  · refine ⟨fun H ↦ rho (X / H), ⟨contDiffAt_rho_comp_div X (ne_of_gt (ha.trans hh.1)),
      rfl, Filter.Eventually.of_forall (fun _ ↦ le_rfl)⟩, ?_⟩
    exact (rho_comp_div_second_bound hX (ha.trans hh.1)).trans
      (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
        (pow_le_pow_left₀ ha.le hh.1.le 2))

open MeasureTheory

lemma baseline_layer_cake_set {h : ℝ} (hh : 0 < h) :
    baseline h + 1 = lambda * h / Real.pi + ell * t h +
      ∫ X in Icc 0 cutoff, density X * sectionLength X h := by
  have heq := baseline_layer_cake hh
  rw [intervalIntegral.integral_of_le cutoff_pos.le, ← integral_Icc_eq_integral_Ioc] at heq
  exact heq

theorem concaveOn_baseline_corrected {a b : ℝ} (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ baseline h - h ^ 2 / a ^ 2) := by
  have ht : ConcaveOn ℝ (Icc a b) (fun h ↦ t h - h ^ 2 / a ^ 2) :=
    (concaveOn_rho_div_corrected (X := 1) (by norm_num) ha).congr
      (fun h hh ↦ by dsimp; rw [rho_at_inverse (ha.trans_le hh.1)])
  have hint : ConcaveOn ℝ (Icc a b)
      (fun h ↦ ∫ X in Icc 0 cutoff, density X * (sectionLength X h - h ^ 2 / a ^ 2)) := by
    apply integral_concaveOn_of_integrand_ae (convex_Icc a b)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with X hX
      exact (concaveOn_sectionLength_corrected hX.1 ha).smul (density_nonneg hX)
    · intro h _
      exact (continuousOn_density.mul
        ((continuous_sectionLength_X h).continuousOn.sub continuousOn_const)).integrableOn_Icc
  have hlin : ConcaveOn ℝ (Icc a b) (fun h ↦ lambda * h / Real.pi) := by
    convert (concaveOn_id (𝕜 := ℝ) (convex_Icc a b)).smul
      (show 0 ≤ lambda / Real.pi by dsimp [lambda]; positivity) using 1
    funext h
    dsimp
    ring
  have hc := ((hlin.add (ht.smul (show 0 ≤ ell by norm_num [ell]))).add hint).add_const (-1)
  apply hc.congr
  intro h hh
  have hI : IntegrableOn (fun X ↦ density X * sectionLength X h) (Icc 0 cutoff) :=
    (continuousOn_density.mul (continuous_sectionLength_X h).continuousOn).integrableOn_Icc
  have hW : IntegrableOn (fun X ↦ density X * (h ^ 2 / a ^ 2)) (Icc 0 cutoff) :=
    continuousOn_density.integrableOn_Icc.mul_const (h ^ 2 / a ^ 2)
  have hmass : (∫ X in Icc 0 cutoff, density X) = 18 / 25 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le cutoff_pos.le]
    exact integral_density
  have heq := baseline_layer_cake_set (ha.trans_le hh.1)
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_sub]
  rw [integral_sub hI hW, integral_mul_const, hmass]
  dsimp [ell] at *
  linarith only [heq]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

def R (h : ℝ) : ℝ := 2 * h * t h / Real.pi

def RSlope (h : ℝ) : ℝ := 2 * t h ^ 2 / (Real.pi * (2 - t h))

def QRad (h : ℝ) : ℝ := Real.pi + 4 * h ^ 2

lemma contDiff_t {n : WithTop ℕ∞} : ContDiff ℝ n t := by
  have hs : ContDiff ℝ n (fun h : ℝ ↦ Real.sqrt (1 + 4 * h ^ 2 / Real.pi)) :=
    (by fun_prop : ContDiff ℝ n (fun h : ℝ ↦ 1 + 4 * h ^ 2 / Real.pi)).sqrt
      (fun h ↦ ne_of_gt (by positivity))
  exact contDiff_const.div (contDiff_const.add hs) (fun h ↦ ne_of_gt (by positivity))

lemma deriv_t_eq {h : ℝ} (hh : 0 < h) :
    deriv t h = -2 * h * t h ^ 2 / (Real.pi + 2 * h ^ 2 * t h) := by
  have ht := (contDiff_t (n := 1)).differentiable (by norm_num) h
  have hd := (((hasDerivAt_id h).pow 2).mul (ht.hasDerivAt.pow 2)).add
    (ht.hasDerivAt.const_mul Real.pi)
  have heq : (fun H : ℝ ↦ H ^ 2 * t H ^ 2 + Real.pi * t H) =ᶠ[𝓝 h]
      (fun _ ↦ Real.pi) := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    have := (t_spec hH).2.2
    nlinarith only [this]
  have hd' : HasDerivAt (fun H : ℝ ↦ H ^ 2 * t H ^ 2 + Real.pi * t H)
      (2 * h * t h ^ 2 + (Real.pi + 2 * h ^ 2 * t h) * deriv t h) h := by
    convert hd using 1 <;> try rfl
    dsimp
    ring
  have heq' := heq.deriv_eq
  rw [hd'.deriv, deriv_const] at heq'
  have hD : 0 < Real.pi + 2 * h ^ 2 * t h := by have := (t_spec hh).1; positivity
  apply (eq_div_iff hD.ne').2
  nlinarith only [heq']

lemma hasDerivAt_t {h : ℝ} (hh : 0 < h) :
    HasDerivAt t (-2 * h * t h ^ 2 / (Real.pi + 2 * h ^ 2 * t h)) h := by
  rw [← deriv_t_eq hh]
  exact ((contDiff_t (n := 1)).differentiable (by norm_num) h).hasDerivAt

lemma contDiff_R {n : WithTop ℕ∞} : ContDiff ℝ n R :=
  ((contDiff_const.mul contDiff_id).mul contDiff_t).div_const Real.pi

lemma hasDerivAt_R {h : ℝ} (hh : 0 < h) : HasDerivAt R (RSlope h) h := by
  obtain ⟨ht0, ht1, ht⟩ := t_spec hh
  have hD : Real.pi + 2 * h ^ 2 * t h ≠ 0 := ne_of_gt (by positivity)
  have h2 : 2 - t h ≠ 0 := ne_of_gt (by linarith)
  convert ((((hasDerivAt_id h).const_mul 2).mul (hasDerivAt_t hh)).div_const Real.pi) using 1 <;> try rfl
  dsimp [RSlope]
  field_simp [hD, h2]
  nlinarith only [ht]

lemma monotoneOn_R : MonotoneOn R (Ioi 0) := by
  intro h hh H hH hle
  unfold R
  exact div_le_div_of_nonneg_right (by nlinarith only [monotoneOn_ht hh hH hle]) Real.pi_pos.le

lemma antitoneOn_RSlope : AntitoneOn RSlope (Ioi 0) := by
  intro h hh H hH hle
  have htt := antitoneOn_t hh hH hle
  have ht0 := (t_spec hh).1
  have ht1 := (t_spec hh).2.1
  have hT0 := (t_spec hH).1
  unfold RSlope
  apply div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0.le htt 2) (by norm_num))
    (mul_pos Real.pi_pos (by linarith))
  exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le

lemma second_deriv_R_nonpos {h : ℝ} (hh : 0 < h) : deriv (deriv R) h ≤ 0 := by
  have heq : deriv R =ᶠ[𝓝 h] RSlope := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    exact (hasDerivAt_R hH).deriv
  rw [heq.deriv_eq]
  have hn := antitoneOn_RSlope.derivWithin_nonpos (x := h)
  rwa [derivWithin_of_mem_nhds (Ioi_mem_nhds hh)] at hn

lemma lt_t_of_quadratic {h r : ℝ} (hh : 0 < h) (_hr : 0 ≤ r)
    (hp : h ^ 2 * r ^ 2 < Real.pi * (1 - r)) : r < t h := by
  by_contra! hn
  obtain ⟨ht0, _, ht⟩ := t_spec hh
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le hn 2) (sq_nonneg h)
  have hπ := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
  nlinarith only [hp, hm, ht, hπ]

lemma t_lt_of_quadratic {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (hp : Real.pi * (1 - r) < h ^ 2 * r ^ 2) : t h < r := by
  by_contra! hn
  obtain ⟨_, _, ht⟩ := t_spec hh
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hn 2) (sq_nonneg h)
  have hπ := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
  nlinarith only [hp, hm, ht, hπ]

lemma gain_t_bounds {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (16 / 25 : ℝ) < t h ∧ t h < 4 / 5 := by
  have hh0 : 0 < h := by linarith [hh.1]
  have hlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 51 / 50) hh.1 2
  have hhi := pow_le_pow_left₀ hh0.le hh.2 2
  constructor
  · apply lt_t_of_quadratic hh0 (by norm_num)
    nlinarith [Real.pi_gt_d4]
  · apply t_lt_of_quadratic hh0 (by norm_num)
    nlinarith [Real.pi_lt_d4]

lemma gain_R_bounds {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (19 / 100 : ℝ) < RSlope h ∧ RSlope h < 17 / 50 ∧ R h < 671 / 1000 := by
  have hh0 : 0 < h := by linarith [hh.1]
  obtain ⟨htlo, hthi⟩ := gain_t_bounds hh
  have ht0 := (t_spec hh0).1
  have hden : 0 < Real.pi * (2 - t h) := mul_pos Real.pi_pos (by linarith)
  have htend : t (81 / 50 : ℝ) < 13 / 20 := by
    apply t_lt_of_quadratic (by norm_num) (by norm_num)
    nlinarith [Real.pi_lt_d4]
  have hRend := monotoneOn_R hh0 (by norm_num : (0 : ℝ) < 81 / 50) hh.2
  refine ⟨?_, ?_, hRend.trans_lt ?_⟩
  · apply (lt_div_iff₀ hden).2
    have hp : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    have hm := mul_le_mul_of_nonneg_right hp.le (show 0 ≤ 2 - t h by linarith)
    nlinarith
  · apply (div_lt_iff₀ hden).2
    have hp : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
    have hm := mul_le_mul_of_nonneg_right hp.le (show 0 ≤ 2 - t h by linarith)
    nlinarith
  · unfold R
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d4]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma t_positive (h : ℝ) : 0 < t h := by unfold t; positivity
lemma Q_positive (h : ℝ) : 0 < Q h := by unfold Q; have := t_positive h; positivity
lemma QRad_positive (h : ℝ) : 0 < QRad h := by unfold QRad; positivity

lemma contDiff_Q {n : WithTop ℕ∞} : ContDiff ℝ n Q := by
  unfold Q
  apply contDiff_const.mul
  apply ContDiff.sqrt
  · exact contDiff_const.add ((contDiff_const.mul (contDiff_id.pow 2)).mul contDiff_t)
  · intro h
    have := t_positive h
    exact ne_of_gt (by positivity)

lemma Q_fourth {h : ℝ} (hh : 0 < h) : Q h ^ 4 = 16 * QRad h / Real.pi ^ 3 := by
  have ht := (t_spec hh).2.2
  have hE : (Real.pi + 2 * h ^ 2 * t h) ^ 2 = Real.pi * QRad h := by
    calc
      _ = Real.pi ^ 2 + 4 * h ^ 2 * (h ^ 2 * t h ^ 2 + Real.pi * t h) := by ring
      _ = Real.pi * QRad h := by rw [ht]; unfold QRad; ring
  have hroot : Real.sqrt (Real.pi + 2 * h ^ 2 * t h) ^ 4 =
      (Real.pi + 2 * h ^ 2 * t h) ^ 2 := by
    calc
      _ = (Real.sqrt (Real.pi + 2 * h ^ 2 * t h) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by have := t_positive h; positivity)]
  unfold Q
  rw [mul_pow, hroot, hE]
  field_simp
  ring

lemma hasDerivAt_QRad (h : ℝ) : HasDerivAt QRad (8 * h) h := by
  convert (((hasDerivAt_id h).pow 2).const_mul 4).const_add Real.pi using 1 <;> try rfl
  dsimp
  ring

lemma deriv_Q_eq {h : ℝ} (hh : 0 < h) :
    deriv Q h = Q h * (2 * h / QRad h) := by
  have hQd := (contDiff_Q (n := 1)).differentiable (by norm_num) h
  have hdleft : HasDerivAt (fun H ↦ Q H ^ 4) (4 * Q h ^ 3 * deriv Q h) h := by
    convert hQd.hasDerivAt.pow 4 using 1
  have hdright : HasDerivAt (fun H ↦ 16 * QRad H / Real.pi ^ 3)
      (128 * h / Real.pi ^ 3) h := by
    convert ((hasDerivAt_QRad h).const_mul 16).div_const (Real.pi ^ 3) using 1
    ring
  have heq : (fun H ↦ Q H ^ 4) =ᶠ[𝓝 h] (fun H ↦ 16 * QRad H / Real.pi ^ 3) := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    exact Q_fourth hH
  have hd := heq.deriv_eq
  rw [hdleft.deriv, hdright.deriv] at hd
  have hArepr : QRad h = Q h ^ 4 * Real.pi ^ 3 / 16 := by
    rw [Q_fourth hh]
    field_simp
  rw [← mul_div_assoc]
  apply (eq_div_iff (QRad_positive h).ne').2
  calc
    deriv Q h * QRad h = deriv Q h * (Q h ^ 4 * Real.pi ^ 3 / 16) := by rw [hArepr]
    _ = (4 * Q h ^ 3 * deriv Q h) * (Q h * Real.pi ^ 3 / 64) := by ring
    _ = (128 * h / Real.pi ^ 3) * (Q h * Real.pi ^ 3 / 64) := by rw [hd]
    _ = Q h * (2 * h) := by field_simp; ring

lemma hasDerivAt_Q {h : ℝ} (hh : 0 < h) :
    HasDerivAt Q (Q h * (2 * h / QRad h)) h := by
  rw [← deriv_Q_eq hh]
  exact ((contDiff_Q (n := 1)).differentiable (by norm_num) h).hasDerivAt

lemma hasDerivAt_QLogSlope (h : ℝ) :
    HasDerivAt (fun H ↦ 2 * H / QRad H) ((2 * Real.pi - 8 * h ^ 2) / QRad h ^ 2) h := by
  convert ((hasDerivAt_id h).const_mul 2).div (hasDerivAt_QRad h) (QRad_positive h).ne' using 1 <;> try rfl
  dsimp [QRad]
  ring

lemma second_deriv_Q_eq {h : ℝ} (hh : 0 < h) :
    deriv (deriv Q) h = Q h * ((2 * Real.pi - 4 * h ^ 2) / QRad h ^ 2) := by
  have heq : deriv Q =ᶠ[𝓝 h] (fun H ↦ Q H * (2 * H / QRad H)) := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    exact deriv_Q_eq hH
  rw [heq.deriv_eq]
  have hd := ((hasDerivAt_Q hh).mul (hasDerivAt_QLogSlope h)).deriv
  convert hd using 1
  ring

lemma Q_log_bounds {h : ℝ} (hh : 0 < h) :
    0 < 2 * h / QRad h ∧ 2 * h / QRad h ≤ 1 / (2 * h) ∧
      -(1 / (4 * h ^ 2)) ≤ (2 * Real.pi - 4 * h ^ 2) / QRad h ^ 2 := by
  refine ⟨div_pos (by positivity) (QRad_positive h), ?_, ?_⟩
  · apply (div_le_div_iff₀ (QRad_positive h) (by positivity : 0 < 2 * h)).2
    unfold QRad
    nlinarith [Real.pi_pos]
  · rw [← neg_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * h ^ 2) (sq_pos_of_pos (QRad_positive h))).2
    unfold QRad
    nlinarith [sq_nonneg Real.pi, mul_nonneg Real.pi_pos.le (sq_nonneg h)]

end CubicTorus.Scalar

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

lemma second_deriv_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y ↦ f y + g y)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have heq : (fun y ↦ f y + g y) = (fun y ↦ f y - -g y) := by funext y; ring
  rw [heq, second_deriv_sub hf hg.neg]
  simp

lemma second_deriv_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y ↦ f y * g y)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x + f x * deriv (deriv g) x := by
  have heq : deriv (fun y ↦ f y * g y) =ᶠ[𝓝 x]
      (fun y ↦ deriv f y * g y + f y * deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_fun_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfdd := (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd := (hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [heq.deriv_eq]
  have hd := ((hfdd.hasDerivAt.mul hgd.hasDerivAt).add
    (hfd.hasDerivAt.mul hgdd.hasDerivAt)).deriv
  convert hd using 1
  ring

lemma second_deriv_cube {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun y ↦ f y ^ 3)) x =
      6 * f x * deriv f x ^ 2 + 3 * f x ^ 2 * deriv (deriv f) x := by
  have heq : deriv (fun y ↦ f y ^ 3) =ᶠ[𝓝 x] (fun y ↦ 3 * f y ^ 2 * deriv f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    convert ((hy.differentiableAt (by norm_num)).hasDerivAt.pow 3).deriv using 1
  have hfd := hf.differentiableAt (by norm_num)
  have hfdd := (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [heq.deriv_eq]
  have hd := (((hfd.hasDerivAt.pow 2).const_mul 3).mul hfdd.hasDerivAt).deriv
  convert hd using 1
  dsimp
  ring

lemma second_deriv_mul_cube {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y ↦ f y * g y ^ 3)) x =
      deriv (deriv f) x * g x ^ 3 + 6 * deriv f x * g x ^ 2 * deriv g x +
        6 * f x * g x * deriv g x ^ 2 + 3 * f x * g x ^ 2 * deriv (deriv g) x := by
  rw [second_deriv_mul hf (hg.pow 3), second_deriv_cube hg]
  have heq : deriv (fun y ↦ g y ^ 3) x = 3 * g x ^ 2 * deriv g x := by
    convert ((hg.differentiableAt (by norm_num)).hasDerivAt.pow 3).deriv using 1
  rw [heq]
  ring

end CubicTorus.Reduction

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma planar_switch_bound : 1 - 1 / Real.pi < (24 / 35 : ℝ) := by
  have hp : (11 / 35 : ℝ) < 1 / Real.pi := (lt_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_d4])
  linarith

lemma u_upper_support {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ U : ℝ → ℝ, UpperSupport u U h ∧
      -(49 / 100 : ℝ) ≤ deriv U h ∧ deriv U h ≤ 0 ∧
      0 ≤ deriv (deriv U) h ∧ deriv (deriv U) h ≤ 7 / 10 := by
  have hh0 : 0 < h := by linarith [hh.1]
  by_cases hb : 1 - 1 / Real.pi ≤ (24 / 25 : ℝ) / h
  · refine ⟨fun _ ↦ 1 - 1 / Real.pi, ⟨by fun_prop, (min_eq_left hb).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_left _ _)⟩, ?_⟩
    norm_num
  · have hh14 : (7 / 5 : ℝ) < h := by
      have hr := (lt_of_not_ge hb).trans planar_switch_bound
      have := (div_lt_iff₀ hh0).1 hr
      linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 5) hh14.le 2
    have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 5) hh14.le 3
    refine ⟨fun H ↦ (24 / 25 : ℝ) / H, ⟨contDiffAt_const.div contDiffAt_id hh0.ne',
      (min_eq_right (le_of_not_ge hb)).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_right _ _)⟩, ?_⟩
    rw [(hasDerivAt_divParam (24 / 25) hh0.ne').deriv, second_deriv_linear_div _ hh0.ne']
    refine ⟨?_, div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg h), by positivity, ?_⟩
    · apply (le_div_iff₀ (sq_pos_of_pos hh0)).2
      nlinarith only [hsq]
    · have heq : 2 * ((24 / 25 : ℝ) / h) / h ^ 2 = (48 / 25 : ℝ) / h ^ 3 := by ring
      rw [heq]
      apply (div_le_iff₀ (pow_pos hh0 3)).2
      nlinarith only [hcube]

lemma C₀_upper_support {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ C : ℝ → ℝ, UpperSupport C₀ C h ∧
      0 ≤ deriv C h ∧ deriv C h ≤ 27 / 25 ∧
      0 ≤ deriv (deriv C) h ∧ deriv (deriv C) h ≤ 54 / 25 := by
  have hh0 : 0 < h := by linarith [hh.1]
  by_cases hc : (67 / 500 : ℝ) * h ^ 3 ≤ 9 / 25
  · refine ⟨fun H ↦ (67 / 500 : ℝ) * H ^ 3, ⟨by fun_prop, (min_eq_left hc).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_left _ _)⟩, ?_⟩
    have hd : deriv (fun H : ℝ ↦ (67 / 500 : ℝ) * H ^ 3) = fun H ↦ (201 / 500 : ℝ) * H ^ 2 := by
      funext H
      convert (((hasDerivAt_id H).pow 3).const_mul (67 / 500)).deriv using 1 <;> try rfl
      dsimp
      ring
    rw [hd]
    have hd2 : deriv (fun H : ℝ ↦ (201 / 500 : ℝ) * H ^ 2) h = (201 / 250 : ℝ) * h := by
      convert (((hasDerivAt_id h).pow 2).const_mul (201 / 500)).deriv using 1 <;> try rfl
      dsimp
      ring
    rw [hd2]
    have hsq := pow_le_pow_left₀ hh0.le hh.2 2
    refine ⟨by positivity, ?_, by positivity, ?_⟩ <;> nlinarith [hh.2]
  · refine ⟨fun _ ↦ (9 / 25 : ℝ), ⟨by fun_prop, (min_eq_right (le_of_not_ge hc)).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_right _ _)⟩, ?_⟩
    norm_num

lemma gain_cubic_jet_bound {C C' C'' w w' w'' : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hCmax : C ≤ 9 / 25) (hC'max : C' ≤ 27 / 25)
    (hC''max : C'' ≤ 54 / 25) (hw : 0 ≤ w) (hwmax : w ≤ dm)
    (hw'lo : -(1 / 2 : ℝ) ≤ w') (hw'hi : w' ≤ 17 / 50) (hw'' : w'' ≤ 4 / 5) :
    C'' * w ^ 3 + 6 * C' * w ^ 2 * w' + 6 * C * w * w' ^ 2 + 3 * C * w ^ 2 * w'' ≤ 2 / 5 := by
  have hdm : 0 ≤ dm := by norm_num [dm]
  have hw2 := pow_le_pow_left₀ hw hwmax 2
  have hw3 := pow_le_pow_left₀ hw hwmax 3
  have hdw : w' ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (w' + 1 / 2), mul_nonneg (by linarith : 0 ≤ w' + 1 / 2)
      (by linarith : 0 ≤ 1 / 2 - w')]
  have h1 : C'' * w ^ 3 ≤ (54 / 25 : ℝ) * dm ^ 3 := by
    exact (mul_le_mul_of_nonneg_right hC''max (pow_nonneg hw 3)).trans
      (mul_le_mul_of_nonneg_left hw3 (by norm_num))
  have h2 : 6 * C' * w ^ 2 * w' ≤ 6 * (27 / 25 : ℝ) * dm ^ 2 * (17 / 50) := by
    apply (mul_le_mul_of_nonneg_left hw'hi (by positivity : 0 ≤ 6 * C' * w ^ 2)).trans
    gcongr
  have h3 : 6 * C * w * w' ^ 2 ≤ 6 * (9 / 25 : ℝ) * dm * (1 / 4) := by
    gcongr
  have h4 : 3 * C * w ^ 2 * w'' ≤ 3 * (9 / 25 : ℝ) * dm ^ 2 * (4 / 5) := by
    apply (mul_le_mul_of_nonneg_left hw'' (by positivity : 0 ≤ 3 * C * w ^ 2)).trans
    gcongr
  norm_num [dm] at h1 h2 h3 h4
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma gain_P_lt {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    P h < 9 / 25 := by
  have hu := (min_le_left (1 - 1 / Real.pi) ((24 / 25 : ℝ) / h)).trans_lt planar_switch_bound
  have hR := (gain_R_bounds hh).2.2
  change u h < _ at hu
  change u h - 1 + R h < _
  linarith

lemma gain_le_cappedEnergy {h y : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hy : 0 ≤ y) : gain h ≤ cappedEnergy ell (C₀ h) dm (P h) (Q h) y := by
  have hc := (gain_parameters_pos hh).2.2
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact cappedEnergy_nonneg (by norm_num [ell]) hc.le (by norm_num [dm])
  · exact ⟨y, hy, rfl⟩

lemma continuous_C₀ : Continuous C₀ := by unfold C₀; fun_prop

lemma continuousOn_u {a b : ℝ} (ha : 0 < a) : ContinuousOn u (Icc a b) := by
  exact continuousOn_const.inf (continuousOn_const.div continuousOn_id
    (fun h hh ↦ ne_of_gt (ha.trans_le hh.1)))

lemma continuousOn_P {a b : ℝ} (ha : 0 < a) : ContinuousOn P (Icc a b) := by
  exact ((continuousOn_u ha).sub continuousOn_const).add (contDiff_R (n := 0)).continuous.continuousOn

lemma continuousOn_critical {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun h ↦ critical ell (C₀ h) (P h) (Q h)) (Icc a b) := by
  unfold critical
  apply (continuousOn_const.mul (continuousOn_P ha)).div
  · apply continuousOn_const.add
    exact Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.add ((((continuousOn_const.mul continuous_C₀.continuousOn).mul
        ((contDiff_Q (n := 0)).continuous.continuousOn.pow 2)).mul (continuousOn_P ha)).div_const ell))
  · intro h _
    have := Real.sqrt_nonneg (1 + 6 * C₀ h * Q h ^ 2 * P h / ell)
    linarith

end CubicTorus.Scalar
end
end
end
end ReusedScalar205
end
end

end OAI
