import OAI.Geometry.Kahler.Definitions

namespace OAI

universe uKahler69_1

open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace PinchedHartogs

lemma ball_eq : ball = Metric.ball (0 : Base) 1 := by
  ext z
  simp [ball, Metric.mem_ball, dist_zero_right]

lemma isOpen_ball : IsOpen ball := by
  rw [ball_eq]
  exact Metric.isOpen_ball

lemma zero_mem_ball : (0 : Base) ∈ ball := by simp [ball]

lemma simplyConnected_ball : IsSimplyConnected ball := by
  let : ContractibleSpace ball := by
    rw [ball_eq]
    exact (convex_ball (0 : Base) 1).contractibleSpace ⟨0, by simp⟩
  change SimplyConnectedSpace ball
  infer_instance

lemma zeroSection_mem (φ : Base → ℝ) {z : Base} (hz : z ∈ ball) :
    (z, 0) ∈ hartogs φ := by simp [hartogs, hz]

lemma analyticAt_of_exp_eq {E : Type uKahler69_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {x : E} (hf : ContinuousAt f x) (hg : AnalyticAt ℂ g x)
    (he : (fun y ↦ Complex.exp (f y)) =ᶠ[𝓝 x] g) : AnalyticAt ℂ f x := by
  have he0 : Complex.exp (f x) = g x := he.self_of_nhds
  have hu : g x / Complex.exp (f x) ∈ Complex.slitPlane := by
    rw [← he0, div_self (Complex.exp_ne_zero _)]
    exact Complex.one_mem_slitPlane
  have hlog : AnalyticAt ℂ (fun y ↦ f x + Complex.log (g y / Complex.exp (f x))) x :=
    analyticAt_const.add (hg.div_const.clog hu)
  apply hlog.congr
  have hcont : ContinuousAt (fun y ↦ (f y - f x).im) x :=
    Complex.continuous_im.continuousAt.comp (hf.sub continuousAt_const)
  have hsmall : ∀ᶠ y in 𝓝 x, (f y - f x).im ∈ Ioo (-Real.pi) Real.pi :=
    hcont (by simpa using Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)
  filter_upwards [he, hsmall] with y hey hy
  rw [← hey, ← Complex.exp_sub, Complex.log_exp hy.1 hy.2.le]
  simp

lemma exists_holomorphic_log {d : Base → ℂ} (hd : AnalyticOnNhd ℂ d ball)
    (h0 : ∀ z ∈ ball, d z ≠ 0) :
    ∃ ℓ : Base → ℂ, AnalyticOnNhd ℂ ℓ ball ∧
      ∀ z ∈ ball, Complex.exp (ℓ z) = d z := by
  obtain ⟨ℓ, hℓc, hℓ⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    simplyConnected_ball isOpen_ball hd.continuousOn (by
      rintro ⟨z, hz, he⟩
      exact h0 z hz he)
  refine ⟨ℓ, ?_, hℓ⟩
  intro z hz
  refine analyticAt_of_exp_eq (hℓc.continuousAt (isOpen_ball.mem_nhds hz)) (hd z hz) ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with y hy
  exact hℓ hy

lemma norm_deriv_le_on_open_disk {f : ℂ → ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hB : ∀ ζ ∈ Metric.ball (0 : ℂ) R, ‖f ζ‖ ≤ B) :
    ‖deriv f 0‖ ≤ B / R := by
  have hlim : Tendsto (fun r : ℝ ↦ B / r) (𝓝[<] R) (𝓝 (B / R)) :=
    ((continuousAt_const.div continuousAt_id hR.ne').tendsto).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hR] with r hr
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr.1
  · exact DiffContOnCl.mk_ball (hf.mono (Metric.ball_subset_ball hr.2.le))
      (hf.continuousOn.mono (Metric.closedBall_subset_ball hr.2))
  · intro ζ hζ
    exact hB ζ (Metric.closedBall_subset_ball hr.2 (Metric.sphere_subset_closedBall hζ))

lemma cauchy_direction {φ : Base → ℝ} {F : Ambient → Target} {p v : Ambient}
    {R B : ℝ} (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (hartogs φ))
    (hB : ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B)
    (hline : ∀ ζ ∈ Metric.ball (0 : ℂ) R, p + ζ • v ∈ hartogs φ) (i : Fin 3) :
    ‖(fderiv ℂ F p v) i‖ ≤ B / R := by
  have hp : p ∈ hartogs φ := by
    simpa using hline 0 (Metric.mem_ball_self hR)
  have ha : Differentiable ℂ (fun ζ : ℂ ↦ p + ζ • v) := by fun_prop
  let π : Target →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have hcomp : DifferentiableOn ℂ (fun ζ : ℂ ↦ F (p + ζ • v) i) (Metric.ball 0 R) :=
    π.differentiable.comp_differentiableOn
      (hF.differentiableOn.comp ha.differentiableOn hline)
  have hlin0 : HasDerivAt (fun ζ : ℂ ↦ p + ζ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have hDF : HasFDerivAt F (fderiv ℂ F p) (p + (0 : ℂ) • v) := by
    simpa using (hF p hp).differentiableAt.hasFDerivAt
  have hder : HasDerivAt (fun ζ : ℂ ↦ F (p + ζ • v) i) ((fderiv ℂ F p v) i) 0 :=
    π.hasFDerivAt.comp_hasDerivAt 0
      (hDF.comp_hasDerivAt 0 hlin0)
  rw [← hder.deriv]
  exact norm_deriv_le_on_open_disk hR hcomp (fun ζ hζ ↦ hB _ (hline ζ hζ) i)

lemma analytic_jacobian_zero {φ : Base → ℝ} {F : Ambient → Target}
    (hF : AnalyticOnNhd ℂ F (hartogs φ)) :
    AnalyticOnNhd ℂ (fun z : Base ↦ (jacobian F (z, 0)).det) ball := by
  have hc (i j : Fin 3) : AnalyticOnNhd ℂ
      (fun z : Base ↦ (fderiv ℂ F (z, 0) (coordVector j)) i) ball := by
    intro z hz
    have hd : AnalyticAt ℂ (fun z : Base ↦ fderiv ℂ F (z, 0)) z :=
      (hF.fderiv (z, 0) (zeroSection_mem φ hz)).comp (f := fun z : Base ↦ (z, (0 : ℂ)))
        (analyticAt_id.prod analyticAt_const)
    let π : Target →L[ℂ] ℂ := ContinuousLinearMap.proj i
    let ev : (Ambient →L[ℂ] Target) →L[ℂ] Target :=
      ContinuousLinearMap.apply ℂ Target (coordVector j)
    exact ((π.comp ev).analyticAt _).comp hd
  intro z hz
  simp only [Matrix.det_fin_three, jacobian]
  exact (((((hc 0 0 z hz).mul (hc 1 1 z hz)).mul (hc 2 2 z hz)).sub
    (((hc 0 0 z hz).mul (hc 1 2 z hz)).mul (hc 2 1 z hz))).sub
    (((hc 0 1 z hz).mul (hc 1 0 z hz)).mul (hc 2 2 z hz))).add
    (((hc 0 1 z hz).mul (hc 1 2 z hz)).mul (hc 2 0 z hz)) |>.add
    (((hc 0 2 z hz).mul (hc 1 0 z hz)).mul (hc 2 1 z hz)) |>.sub
    (((hc 0 2 z hz).mul (hc 1 1 z hz)).mul (hc 2 0 z hz))

lemma base_line_mem {φ : Base → ℝ} {z : Base} (hz : z ∈ ball) (j : Fin 2)
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) :
    (z, 0) + ζ • (EuclideanSpace.single j 1, 0) ∈ hartogs φ := by
  have hζ' : ‖ζ‖ < 1 - ‖z‖ := by simpa [Metric.mem_ball] using hζ
  change ‖z + ζ • EuclideanSpace.single j 1‖ < 1 ∧ _
  constructor
  · calc
      ‖z + ζ • EuclideanSpace.single j 1‖ ≤ ‖z‖ + ‖ζ • EuclideanSpace.single j 1‖ :=
        norm_add_le _ _
      _ = ‖z‖ + ‖ζ‖ := by simp [norm_smul]
      _ < ‖z‖ + (1 - ‖z‖) := by linarith only [hζ']
      _ = 1 := add_tsub_cancel_of_le (le_of_lt hz)
  · simp

lemma jacobian_base_bound {φ : Base → ℝ} {F : Ambient → Target} {B : ℝ}
    (hF : AnalyticOnNhd ℂ F (hartogs φ)) (hB : ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B)
    {z : Base} (hz : z ∈ ball) (i j : Fin 3) (hj : j.val < 2) :
    ‖jacobian F (z, 0) i j‖ ≤ B / (1 - ‖z‖) := by
  have hδ : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have hh (j : Fin 2) :
      ‖(fderiv ℂ F (z, 0) (EuclideanSpace.single j 1, 0)) i‖ ≤ B / (1 - ‖z‖) :=
    cauchy_direction hδ hF hB (fun ζ hζ ↦ base_line_mem hz j hζ) i
  fin_cases j
  · simpa [jacobian, coordVector] using hh 0
  · simpa [jacobian, coordVector] using hh 1
  · norm_num at hj

lemma exp_fiber_identity (a : ℝ) : Real.exp a * Real.exp (-(a / 2)) ^ 2 = 1 := by
  rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  convert Real.exp_zero using 1; congr 1; ring

lemma fiber_line_mem {φ : Base → ℝ} {z : Base} (hz : z ∈ ball)
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) (Real.exp (-(φ z / 2)))) :
    (z, 0) + ζ • (0, 1) ∈ hartogs φ := by
  have hζ' : ‖ζ‖ < Real.exp (-(φ z / 2)) := by simpa [Metric.mem_ball] using hζ
  have hh : Real.exp (φ z) * ‖ζ‖ ^ 2 < 1 := by
    calc
      Real.exp (φ z) * ‖ζ‖ ^ 2 < Real.exp (φ z) * Real.exp (-(φ z / 2)) ^ 2 := by
        apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
        nlinarith [norm_nonneg ζ, Real.exp_pos (-(φ z / 2))]
      _ = 1 := exp_fiber_identity _
  simpa [hartogs, smul_eq_mul] using And.intro hz hh

lemma jacobian_fiber_bound {φ : Base → ℝ} {F : Ambient → Target} {B : ℝ}
    (hF : AnalyticOnNhd ℂ F (hartogs φ)) (hB : ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B)
    {z : Base} (hz : z ∈ ball) (i : Fin 3) :
    ‖jacobian F (z, 0) i 2‖ ≤ B * Real.exp (φ z / 2) := by
  have hh := cauchy_direction (Real.exp_pos (-(φ z / 2))) hF hB
    (fun ζ hζ ↦ fiber_line_mem hz hζ) i
  simpa [jacobian, coordVector, Real.exp_neg, div_inv_eq_mul] using hh

lemma det_bound_columns {M : Matrix (Fin 3) (Fin 3) ℂ} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h0 : ∀ i, ‖M i 0‖ ≤ a) (h1 : ∀ i, ‖M i 1‖ ≤ b) (h2 : ∀ i, ‖M i 2‖ ≤ c) :
    ‖M.det‖ ≤ 6 * a * b * c := by
  let t (i j k : Fin 3) := M i 0 * M j 1 * M k 2
  have ht (i j k : Fin 3) : ‖t i j k‖ ≤ a * b * c := by
    simp only [t, norm_mul]
    calc
      _ ≤ |a| * |b| * |c| := by
        gcongr
        · exact (h0 i).trans (le_abs_self a)
        · exact (h1 j).trans (le_abs_self b)
        · exact (h2 k).trans (le_abs_self c)
      _ = _ := by rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc]
  have he : M.det = t 0 1 2 - t 0 2 1 - t 1 0 2 + t 2 0 1 + t 1 2 0 - t 2 1 0 := by
    rw [Matrix.det_fin_three]
    dsimp [t]
    ring
  rw [he]
  calc
    ‖t 0 1 2 - t 0 2 1 - t 1 0 2 + t 2 0 1 + t 1 2 0 - t 2 1 0‖ ≤
        ‖t 0 1 2 - t 0 2 1 - t 1 0 2 + t 2 0 1 + t 1 2 0‖ + ‖t 2 1 0‖ :=
      norm_sub_le _ _
    _ ≤ (‖t 0 1 2 - t 0 2 1 - t 1 0 2 + t 2 0 1‖ + ‖t 1 2 0‖) + ‖t 2 1 0‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ ((‖t 0 1 2 - t 0 2 1 - t 1 0 2‖ + ‖t 2 0 1‖) + ‖t 1 2 0‖) + ‖t 2 1 0‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ (((‖t 0 1 2 - t 0 2 1‖ + ‖t 1 0 2‖) + ‖t 2 0 1‖) + ‖t 1 2 0‖) + ‖t 2 1 0‖ := by
      gcongr; exact norm_sub_le _ _
    _ ≤ ((((‖t 0 1 2‖ + ‖t 0 2 1‖) + ‖t 1 0 2‖) + ‖t 2 0 1‖) + ‖t 1 2 0‖) + ‖t 2 1 0‖ := by
      gcongr; exact norm_sub_le _ _
    _ ≤ 6 * a * b * c := by
      have := ht 0 1 2
      have := ht 0 2 1
      have := ht 1 0 2
      have := ht 2 0 1
      have := ht 1 2 0
      have := ht 2 1 0
      linarith

lemma jacobian_det_bound {φ : Base → ℝ} {F : Ambient → Target} {B : ℝ}
    (hF : AnalyticOnNhd ℂ F (hartogs φ)) (hB0 : 0 ≤ B)
    (hB : ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B) {z : Base} (hz : z ∈ ball) :
    ‖(jacobian F (z, 0)).det‖ ≤ 6 * B ^ 3 / (1 - ‖z‖) ^ 2 * Real.exp (φ z / 2) := by
  have hδ : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  calc
    ‖(jacobian F (z, 0)).det‖ ≤
        6 * (B / (1 - ‖z‖)) * (B / (1 - ‖z‖)) * (B * Real.exp (φ z / 2)) :=
      det_bound_columns (by positivity) (by positivity) (by positivity)
        (fun i ↦ jacobian_base_bound hF hB hz i 0 (by decide))
        (fun i ↦ jacobian_base_bound hF hB hz i 1 (by decide))
        (fun i ↦ jacobian_fiber_bound hF hB hz i)
    _ = 6 * B ^ 3 / (1 - ‖z‖) ^ 2 * Real.exp (φ z / 2) := by
      field_simp

lemma jacobian_log_bound {φ : Base → ℝ} {F : Ambient → Target} {B : ℝ}
    (hF : AnalyticOnNhd ℂ F (hartogs φ)) (hB1 : 1 ≤ B)
    (hB : ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B) {z : Base} (hz : z ∈ ball)
    (hdet : (jacobian F (z, 0)).det ≠ 0) :
    Real.log (‖(jacobian F (z, 0)).det‖ ^ 2) ≤
      2 * Real.log 6 + 6 * Real.log B + 4 * Real.log (1 / (1 - ‖z‖)) + φ z := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hδ : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have hn : 0 < ‖(jacobian F (z, 0)).det‖ := norm_pos_iff.mpr hdet
  have hh := Real.log_le_log hn (jacobian_det_bound hF hB0.le hB hz)
  have hlog : Real.log (6 * B ^ 3 / (1 - ‖z‖) ^ 2 * Real.exp (φ z / 2)) =
      Real.log 6 + 3 * Real.log B + 2 * Real.log (1 / (1 - ‖z‖)) + φ z / 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp,
      Real.log_div one_ne_zero hδ.ne', Real.log_one]
    ring
  rw [hlog] at hh
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem map_obstruction : MapObstruction := by
  intro φ _hφ hn F ⟨hF, B, hB⟩ hnever
  let B' := max B 1
  have hB1 : 1 ≤ B' := le_max_right _ _
  have hB' : ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B' :=
    fun p hp i ↦ (hB p hp i).trans (le_max_left _ _)
  have hzero : ∀ z ∈ ball, (jacobian F (z, 0)).det ≠ 0 :=
    fun z hz ↦ hnever (z, 0) (zeroSection_mem φ hz)
  obtain ⟨ℓ, hℓ, he⟩ := exists_holomorphic_log (analytic_jacobian_zero hF) hzero
  apply hn
  refine ⟨fun z ↦ 2 * ℓ z, 2 * Real.log 6 + 6 * Real.log B', ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (hℓ z hz)
  · intro z hz
    have hid : (2 * ℓ z).re = Real.log (‖(jacobian F (z, 0)).det‖ ^ 2) := by
      rw [← he z hz, Complex.norm_exp, Real.log_pow, Real.log_exp]
      simp
    rw [hid]
    exact jacobian_log_bound hF hB1 hB' hz (hzero z hz)

end PinchedHartogs

end

end OAI
