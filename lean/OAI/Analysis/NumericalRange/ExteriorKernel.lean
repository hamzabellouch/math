import OAI.Analysis.NumericalRange.OuterNeighborhood

namespace OAI

section
section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace CompleteCrouzeix

theorem exteriorCorrection_analytic_right {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) {w : ℂ} (hw : w ∈ U) :
    AnalyticOnNhd ℂ (exteriorCorrection G w) U := by
  have hq := analyticOnNhd_dslope hU hG hw
  intro t ht
  exact (analyticAt_id.mul (hq.deriv t ht)).div (hq t ht)
    (dslope_ne_zero_of_injOn hi hw ht (hd w hw))

theorem exteriorCorrection_eq {G : ℂ → ℂ} {w t : ℂ}
    (htw : t ≠ w) (hG : DifferentiableAt ℂ G t) (hne : G t ≠ G w) :
    exteriorCorrection G w t =
      t * deriv G t / (G t - G w) - t / (t-w) := by
  have he := dslope_eventuallyEq_slope_of_ne G htw
  have hd : deriv (dslope G w) t =
      (deriv G t * (t-w) - (G t-G w)) / (t-w)^2 := by
    rw [he.deriv_eq]
    rw [show slope G w = (fun z => (G z-G w)/(z-w)) from
      funext (fun z => slope_def_field G w z)]
    simpa only [id_eq, mul_one] using
      ((hG.hasDerivAt.sub_const (G w)).fun_div
        ((hasDerivAt_id t).sub_const w) (sub_ne_zero.mpr htw)).deriv
  rw [exteriorCorrection, hd, dslope_of_ne _ htw, slope_def_field]
  field_simp

lemma exteriorCorrection_eq_left {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ z ∈ U, deriv G z ≠ 0) {w t : ℂ} (hw : w ∈ U) (ht : t ∈ U) :
    exteriorCorrection G w t =
      -t * dslope (fun z => deriv G t / dslope G t z) t w := by
  have hdt := hd t ht
  have hq := analyticOnNhd_dslope hU hG ht
  by_cases hwt : w = t
  · subst w
    rw [dslope_same]
    have he : deriv (fun z => deriv G t / dslope G t z) t =
        -(deriv G t) * deriv (dslope G t) t / (deriv G t)^2 := by
      simpa using ((hasDerivAt_const t (deriv G t)).fun_div
        (hq t ht).differentiableAt.hasDerivAt (by simpa using hdt)).deriv
    rw [he, exteriorCorrection, dslope_same]
    field_simp
  · rw [exteriorCorrection_eq (Ne.symm hwt) (hG t ht).differentiableAt
      (fun he => hwt (hi hw ht he.symm)), dslope_of_ne _ hwt,
      slope_def_field, dslope_same, div_self hdt, dslope_of_ne _ hwt,
      slope_def_field]
    have hne : G w - G t ≠ 0 := sub_ne_zero.mpr (fun he => hwt (hi hw ht he))
    have hdist : w-t ≠ 0 := sub_ne_zero.mpr hwt
    have hne' : G t - G w ≠ 0 := sub_ne_zero.mpr (fun he => hwt (hi hw ht he.symm))
    have hdist' : t-w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwt)
    field_simp
    ring

theorem exteriorCorrection_analytic_left {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) {t : ℂ} (ht : t ∈ U) :
    AnalyticOnNhd ℂ (fun w => exteriorCorrection G w t) U := by
  have hq := analyticOnNhd_dslope hU hG ht
  have hh : AnalyticOnNhd ℂ (fun z => deriv G t / dslope G t z) U := by
    intro z hz
    exact analyticAt_const.div (hq z hz)
      (dslope_ne_zero_of_injOn hi ht hz (hd t ht))
  have hs := analyticOnNhd_dslope hU hh ht
  intro w hw
  apply (analyticAt_const.mul (hs w hw)).congr
  filter_upwards [hU.mem_nhds hw] with z hz
  exact (exteriorCorrection_eq_left hU hG hi hd hz ht).symm

lemma dslope_comm (f : ℂ → ℂ) (x y : ℂ) : dslope f x y = dslope f y x := by
  by_cases h : x = y
  · subst y; rfl
  · rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h, slope_def_field,
      slope_def_field, div_eq_div_iff (sub_ne_zero.mpr (Ne.symm h)) (sub_ne_zero.mpr h)]
    ring

lemma deriv_dslope_eq_iterated {H : ℂ → ℂ} {x y : ℂ}
    (hH : DifferentiableAt ℂ H y) :
    deriv (dslope H x) y = dslope (dslope H y) y x := by
  by_cases h : x = y
  · subst x; simp
  · rw [dslope_of_ne _ h, slope_def_field, dslope_same,
      dslope_of_ne _ h, slope_def_field]
    rw [(dslope_eventuallyEq_slope_of_ne H (Ne.symm h)).deriv_eq]
    rw [show slope H x = (fun z => (H z-H x)/(z-x)) from
      funext (fun z => slope_def_field H x z)]
    have hd := ((hH.hasDerivAt.sub_const (H x)).fun_div
      ((hasDerivAt_id y).sub_const x) (sub_ne_zero.mpr (Ne.symm h))).deriv
    simp only [id_eq, mul_one] at hd
    rw [hd]
    have hxy : x-y ≠ 0 := sub_ne_zero.mpr h
    have hyx : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp
    ring

def exteriorDividedDifference (a : ℂ) (h : ℂ → ℂ) (x y : ℂ) : ℂ :=
  a-x*y*dslope h x y

def reciprocalCorrection (a : ℂ) (h : ℂ → ℂ) (x y : ℂ) : ℂ :=
  x*y*dslope (dslope (fun z => z*h z) y) y x / exteriorDividedDifference a h x y

@[simp] lemma reciprocalCorrection_zero_left (a : ℂ) (h : ℂ → ℂ) (y : ℂ) :
    reciprocalCorrection a h 0 y = 0 := by simp [reciprocalCorrection]

@[simp] lemma reciprocalCorrection_zero_right (a : ℂ) (h : ℂ → ℂ) (x : ℂ) :
    reciprocalCorrection a h x 0 = 0 := by simp [reciprocalCorrection]

lemma reciprocalCorrection_eq_deriv {a : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hy : DifferentiableAt ℂ h y) :
    reciprocalCorrection a h x y =
      x*y*deriv (dslope (fun z => z*h z) x) y / exteriorDividedDifference a h x y := by
  have hh : DifferentiableAt ℂ (fun z => z*h z) y := by fun_prop
  rw [deriv_dslope_eq_iterated hh]
  rfl

lemma reciprocalCorrection_analytic_left {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0)
    {y : ℂ} (hy : y ∈ U) :
    AnalyticOnNhd ℂ (fun x => reciprocalCorrection a h x y) U := by
  have hh' : AnalyticOnNhd ℂ (fun z => z*h z) U := analyticOnNhd_id.mul hh
  have hs := analyticOnNhd_dslope hU (analyticOnNhd_dslope hU hh' hy) hy
  have hq := analyticOnNhd_dslope hU hh hy
  intro x hx
  have hqa : AnalyticAt ℂ (fun x => exteriorDividedDifference a h x y) x := by
    have he : (fun x => exteriorDividedDifference a h x y) =
        (fun x => a-x*y*dslope h y x) := by
      funext z; rw [exteriorDividedDifference, dslope_comm h z y]
    rw [he]
    exact analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).mul (hq x hx))
  exact ((analyticAt_id.mul analyticAt_const).mul (hs x hx)).div hqa (hne x hx y hy)

lemma reciprocalCorrection_analytic_right {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0)
    {x : ℂ} (hx : x ∈ U) :
    AnalyticOnNhd ℂ (reciprocalCorrection a h x) U := by
  have hh' : AnalyticOnNhd ℂ (fun z => z*h z) U := analyticOnNhd_id.mul hh
  have hs := analyticOnNhd_dslope hU hh' hx
  have hq := analyticOnNhd_dslope hU hh hx
  intro y hy
  have hqa : AnalyticAt ℂ (exteriorDividedDifference a h x) y :=
    analyticAt_const.sub ((analyticAt_const.mul analyticAt_id).mul (hq y hy))
  apply (((analyticAt_const.mul analyticAt_id).mul (hs.deriv y hy)).div hqa
    (hne x hx y hy)).congr
  filter_upwards [hU.mem_nhds hy] with z hz
  exact (reciprocalCorrection_eq_deriv (hh z hz).differentiableAt).symm

lemma hasDerivAt_exteriorMap {a b : ℂ} {h : ℂ → ℂ} {t : ℂ}
    (ht : t ≠ 0) (hh : DifferentiableAt ℂ h t⁻¹) :
    HasDerivAt (exteriorMap a b h) (a - (t^2)⁻¹ * deriv h t⁻¹) t := by
  convert! (((hasDerivAt_id t).const_mul a).add_const b).fun_add
      (hh.hasDerivAt.comp t (hasDerivAt_inv ht)) using 1
  ring

lemma dslope_exteriorMap {a b : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hh : DifferentiableAt ℂ h x) :
    dslope (exteriorMap a b h) x⁻¹ y⁻¹ = exteriorDividedDifference a h x y := by
  by_cases hxy : x = y
  · subst y
    rw [dslope_same, (hasDerivAt_exteriorMap (inv_ne_zero hx) (by simpa using hh)).deriv]
    simp [exteriorDividedDifference, sq]
  · have hyx : y⁻¹ ≠ x⁻¹ := fun he => hxy (inv_injective he).symm
    rw [dslope_of_ne _ hyx, slope_def_field, exteriorDividedDifference,
      dslope_of_ne _ (Ne.symm hxy), slope_def_field]
    simp only [exteriorMap, inv_inv]
    have hdist : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hinvdist : y⁻¹-x⁻¹ ≠ 0 := sub_ne_zero.mpr hyx
    field_simp
    ring

lemma dividedDifference_ne_zero {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hR : 0 < R) :
    ∀ x ∈ ball (0 : ℂ) R, ∀ y ∈ ball (0 : ℂ) R,
      exteriorDividedDifference a h x y ≠ 0 := by
  intro x hx y hy
  by_cases hx0 : x = 0
  · subst x; simpa [exteriorDividedDifference] using ha
  by_cases hy0 : y = 0
  · subst y; simpa [exteriorDividedDifference] using ha
  have hix : R⁻¹ < ‖x⁻¹‖ := by
    rw [norm_inv]
    exact inv_lt_inv₀ hR (norm_pos_iff.mpr hx0) |>.mpr (by simpa using hx)
  have hiy : R⁻¹ < ‖y⁻¹‖ := by
    rw [norm_inv]
    exact inv_lt_inv₀ hR (norm_pos_iff.mpr hy0) |>.mpr (by simpa using hy)
  rw [← dslope_exteriorMap hx0 hy0 (hh x hx).differentiableAt]
  exact dslope_ne_zero_of_injOn hi hix hiy (hd _ hix)

lemma analyticOnNhd_unit_circleAverage {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    Real.circleAverage f 0 1 = f 0 := by
  have hd : DiffContOnCl ℂ f (ball 0 |(1:ℝ)|) := by
    constructor
    · simp only [abs_one]
      exact hf.differentiableOn.mono ball_subset_closedBall
    · simpa only [abs_one, closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] using hf.continuousOn
  exact hd.circleAverage

lemma reciprocalCorrection_circleAverage_right {a : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hne : ∀ x ∈ ball (0 : ℂ) R, ∀ y ∈ ball (0 : ℂ) R,
      exteriorDividedDifference a h x y ≠ 0) {x : ℂ} (hx : x ∈ ball 0 R) :
    Real.circleAverage (fun t => reciprocalCorrection a h x t⁻¹) 0 1 = 0 := by
  rw [Real.circleAverage_zero_one_congr_inv]
  have hs : closedBall (0:ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR
  rw [analyticOnNhd_unit_circleAverage
    ((reciprocalCorrection_analytic_right isOpen_ball hh hne hx).mono hs)]
  simp

lemma reciprocalCorrection_circleAverage_left {a : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hne : ∀ x ∈ ball (0 : ℂ) R, ∀ y ∈ ball (0 : ℂ) R,
      exteriorDividedDifference a h x y ≠ 0) {y : ℂ} (hy : y ∈ ball 0 R) :
    Real.circleAverage (fun w => reciprocalCorrection a h w⁻¹ y) 0 1 = 0 := by
  rw [Real.circleAverage_zero_one_congr_inv (f := fun w => reciprocalCorrection a h w y)]
  have hs : closedBall (0:ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR
  rw [analyticOnNhd_unit_circleAverage
    ((reciprocalCorrection_analytic_left isOpen_ball hh hne hy).mono hs)]
  simp

lemma dslope_id_mul {h : ℂ → ℂ} {x : ℂ} (hh : DifferentiableAt ℂ h x) :
    dslope (fun z => z*h z) x = fun z => z*dslope h x z+h x := by
  funext y
  by_cases hy : y = x
  · subst y
    simp only [dslope_same]
    have hd := (hasDerivAt_id x).fun_mul hh.hasDerivAt
    simpa only [id_eq, one_mul, mul_one, add_comm] using hd.deriv
  · rw [dslope_of_ne _ hy, dslope_of_ne _ hy, slope_def_field, slope_def_field]
    have hdist : y-x ≠ 0 := sub_ne_zero.mpr hy
    field_simp
    ring

lemma reciprocalCorrection_eq_logDeriv {a : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hx : DifferentiableAt ℂ h x) (hy : DifferentiableAt ℂ h y)
    (hs : DifferentiableAt ℂ (dslope h x) y) :
    reciprocalCorrection a h x y = x*y*(dslope h x y+y*deriv (dslope h x) y) /
      exteriorDividedDifference a h x y := by
  rw [reciprocalCorrection_eq_deriv hy, dslope_id_mul hx]
  have hd := ((hasDerivAt_id y).fun_mul hs.hasDerivAt).add_const (h x)
  have he : deriv (fun z => z*dslope h x z+h x) y =
      dslope h x y+y*deriv (dslope h x) y := by simpa using hd.deriv
  rw [he]

theorem exteriorCorrection_eq_reciprocal {a b : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : DifferentiableAt ℂ h x) (hy : DifferentiableAt ℂ h y)
    (hs : DifferentiableAt ℂ (dslope h x) y) :
    exteriorCorrection (exteriorMap a b h) x⁻¹ y⁻¹ = reciprocalCorrection a h x y := by
  have he : dslope (exteriorMap a b h) x⁻¹ =ᶠ[𝓝 y⁻¹]
      fun t => exteriorDividedDifference a h x t⁻¹ := by
    filter_upwards [eventually_ne_nhds (inv_ne_zero hy0)] with t ht
    simpa using dslope_exteriorMap (a := a) (b := b) hx0 (inv_ne_zero ht) hx
  have hq : HasDerivAt (exteriorDividedDifference a h x)
      (-x*(dslope h x y+y*deriv (dslope h x) y)) y := by
    have hd := (((hasDerivAt_id y).fun_mul hs.hasDerivAt).const_mul x).const_sub a
    convert! hd using 1
    · funext z; simp [exteriorDividedDifference, mul_assoc]
    · simp only [id_eq, one_mul]; ring
  have hq' : HasDerivAt (exteriorDividedDifference a h x)
      (-x*(dslope h x y+y*deriv (dslope h x) y)) y⁻¹⁻¹ := by
    simpa only [inv_inv] using hq
  have hi := hq'.comp y⁻¹ (hasDerivAt_inv (inv_ne_zero hy0))
  have hd : deriv (dslope (exteriorMap a b h) x⁻¹) y⁻¹ =
      x*(dslope h x y+y*deriv (dslope h x) y)*y^2 := by
    rw [he.deriv_eq]
    convert! hi.deriv using 1
    simp only [inv_pow, inv_inv]
    ring
  rw [exteriorCorrection, hd, dslope_exteriorMap hx0 hy0 hx,
    reciprocalCorrection_eq_logDeriv hx hy hs]
  congr 1
  field_simp

theorem continuousOn_of_analytic_left_offDiagonal {B : ℂ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hB : ∀ y ∈ U, AnalyticOnNhd ℂ (fun x => B x y) U)
    (hc : ContinuousOn (Function.uncurry B)
      {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}) :
    ContinuousOn (Function.uncurry B) (U ×ˢ U) := by
  have ho : IsOpen {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2} := by
    exact (hU.preimage continuous_fst).inter
      ((hU.preimage continuous_snd).inter (isOpen_ne_fun continuous_fst continuous_snd))
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  by_cases hxy : x = y
  · subst y
    obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    let r := ε / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrc : closedBall x r ⊆ U := by
      intro z hz
      apply hεU
      have hz' : dist z x ≤ r := hz
      exact lt_of_le_of_lt hz' (by dsimp [r]; linarith)
    let V := ball x (r/2) ×ˢ ball x (r/2)
    have hxV : (x,x) ∈ V := by simp [V, hr]
    have hVU : ∀ p : V, p.val.1 ∈ U ∧ p.val.2 ∈ U := by
      intro p
      have hs : ball x (r/2) ⊆ closedBall x r :=
        (ball_subset_ball (by linarith : r/2 ≤ r)).trans ball_subset_closedBall
      exact ⟨hrc (hs p.property.1),hrc (hs p.property.2)⟩
    have hcircleU (θ : ℝ) : circleMap x r θ ∈ U :=
      hrc (sphere_subset_closedBall (circleMap_mem_sphere x hr.le θ))
    have hcircle_ne (p : V) (θ : ℝ) :
        circleMap x r θ ≠ p.val.1 ∧ circleMap x r θ ≠ p.val.2 := by
      have hz : dist (circleMap x r θ) x = r := (circleMap_mem_sphere x hr.le θ)
      constructor
      · intro he
        rw [he] at hz
        have hp := p.property.1
        change dist p.val.1 x < r/2 at hp
        linarith
      · intro he
        rw [he] at hz
        have hp := p.property.2
        change dist p.val.2 x < r/2 at hp
        linarith
    have hk : Continuous (fun q : V × ℝ =>
        ((circleMap x r q.2-x)/(circleMap x r q.2-q.1.val.1)) *
          B (circleMap x r q.2) q.1.val.2) := by
      apply Continuous.mul
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro q
          exact sub_ne_zero.mpr (hcircle_ne q.1 q.2).1
      · apply hc.comp_continuous (f := fun q : V × ℝ =>
          (circleMap x r q.2,q.1.val.2))
        · fun_prop
        · intro q
          exact ⟨hcircleU q.2,(hVU q.1).2,(hcircle_ne q.1 q.2).2⟩
    have hi : Continuous (fun p : V =>
        Real.circleAverage (fun z => ((z-x)/(z-p.val.1))*B z p.val.2) x r) := by
      exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hk 0 (2*Real.pi)).const_smul _
    have he (p : V) :
        Real.circleAverage (fun z => ((z-x)/(z-p.val.1))*B z p.val.2) x r =
          B p.val.1 p.val.2 := by
      have ha := (hB p.val.2 (hVU p).2).mono hrc
      have hd : DiffContOnCl ℂ (fun z => B z p.val.2) (ball x |r|) := by
        constructor
        · rw [abs_of_pos hr]
          exact ha.differentiableOn.mono ball_subset_closedBall
        · simpa only [abs_of_pos hr, closure_ball x (ne_of_gt hr)] using ha.continuousOn
      have hp : p.val.1 ∈ ball x |r| := by
        rw [abs_of_pos hr]
        exact ball_subset_ball (by linarith : r/2 ≤ r) p.property.1
      exact hd.circleAverage_smul_div hp
    have hv : ContinuousOn (Function.uncurry B) V := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hi.congr he
    exact (hv.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hxV)).continuousWithinAt
  · exact ((hc (x,y) ⟨hx,hy,hxy⟩).continuousAt
      (ho.mem_nhds ⟨hx,hy,hxy⟩)).continuousWithinAt

theorem exteriorCorrection_continuousOn {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) :
    ContinuousOn (Function.uncurry (exteriorCorrection G)) (U ×ˢ U) := by
  apply continuousOn_of_analytic_left_offDiagonal hU
    (fun t ht => exteriorCorrection_analytic_left hU hG hi hd ht)
  let V := {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}
  have hg1 : ContinuousOn (fun p : ℂ × ℂ => G p.1) V :=
    hG.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have hg2 : ContinuousOn (fun p : ℂ × ℂ => G p.2) V :=
    hG.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have hd2 : ContinuousOn (fun p : ℂ × ℂ => deriv G p.2) V :=
    hG.deriv.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have hc : ContinuousOn (fun p : ℂ × ℂ =>
      p.2 * deriv G p.2 / (G p.2-G p.1) - p.2/(p.2-p.1)) V := by
    apply ContinuousOn.sub
    · exact (continuousOn_snd.mul hd2).div (hg2.sub hg1)
        (fun p hp => sub_ne_zero.mpr (fun he => hp.2.2 (hi hp.1 hp.2.1 he.symm)))
    · exact continuousOn_snd.div (continuousOn_snd.sub continuousOn_fst)
        (fun p hp => sub_ne_zero.mpr (Ne.symm hp.2.2))
  apply hc.congr
  intro p hp
  exact exteriorCorrection_eq (Ne.symm hp.2.2) (hG p.2 hp.2.1).differentiableAt
    (fun he => hp.2.2 (hi hp.1 hp.2.1 he.symm))

def exteriorMarkovKernel (G : ℂ → ℂ) (w t : Circle) : ℝ :=
  1 + 2 * (exteriorCorrection G w t).re

lemma two_re_circle_div (w t : Circle) (hne : w ≠ t) :
    2 * ((t : ℂ) / ((t : ℂ)-w)).re = 1 := by
  have hn : normSq ((t : ℂ)-w) ≠ 0 :=
    normSq_eq_zero.not.mpr (sub_ne_zero.mpr (fun he => hne (Circle.ext he).symm))
  have hw := Circle.normSq_coe w
  have ht := Circle.normSq_coe t
  rw [div_re]
  field_simp
  simp only [normSq_apply, sub_re, sub_im] at *
  nlinarith

lemma re_div_eq_support (N z : ℂ) :
    (N/z).re = (conj N*z).re / normSq z := by
  simp only [div_re, mul_re, conj_re, conj_im]
  ring

theorem exteriorMarkovKernel_nonneg {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ z ∈ U, deriv G z ≠ 0) (hTU : ∀ t : Circle, (t : ℂ) ∈ U)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv G t)*(G t-G w)).re) (w t : Circle) :
    0 ≤ exteriorMarkovKernel G w t := by
  have hoff (v : Circle) (hvt : v ≠ t) : 0 ≤ exteriorMarkovKernel G v t := by
    have hne : (t : ℂ) ≠ v := fun he => hvt (Circle.ext he).symm
    have hg : G (t : ℂ) ≠ G v := fun he => hne (hi (hTU t) (hTU v) he)
    rw [exteriorMarkovKernel, exteriorCorrection_eq hne (hG t (hTU t)).differentiableAt hg,
      sub_re]
    have hunit := two_re_circle_div v t hvt
    have hpos : 0 ≤ (((t : ℂ)*deriv G t)/(G t-G v)).re := by
      rw [re_div_eq_support]
      exact div_nonneg (hsupport v t) (normSq_nonneg _)
    linarith
  let : Nontrivial Circle := ⟨⟨-1,1,Circle.neg_ne_self 1⟩⟩
  have hc : Continuous (fun v : Circle => exteriorMarkovKernel G v t) := by
    have hb : Continuous (fun v : Circle => exteriorCorrection G v t) :=
      (exteriorCorrection_continuousOn hU hG hi hd).comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun v => ⟨hTU v,hTU t⟩)
    exact continuous_const.add (continuous_const.mul (continuous_re.comp hb))
  exact closure_minimal (fun v hv => hoff v hv) (isClosed_le continuous_const hc)
    ((dense_compl_singleton t) w)

end CompleteCrouzeix
end
end
end

end OAI
