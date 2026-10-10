import OAI.InformationTheory.AmplitudeDamping.ThermalEntropy

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators
open Set Filter Topology

namespace GAD

def radius (s : ℝ) : ℝ := Real.sqrt (1 - 4 * s ^ 2)
def logRatio (t : ℝ) : ℝ := Real.log (1 + t) - Real.log (1 - t)
def wootters (s : ℝ) : ℝ := g (s ^ 2)
def woottersSlope (s : ℝ) : ℝ := 2 * s / radius s * logRatio (radius s)

theorem continuous_g : Continuous g := by
  unfold g
  fun_prop

theorem continuous_wootters : Continuous wootters := by
  unfold wootters
  exact continuous_g.comp (continuous_id.pow 2)

theorem radius_pos_lt_one {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < radius s ∧ radius s < 1 := by
  have hx : 0 < 1 - 4 * s ^ 2 := by nlinarith [hs.1, hs.2]
  have hx' : 1 - 4 * s ^ 2 < 1 := by nlinarith [hs.1]
  unfold radius
  exact ⟨Real.sqrt_pos.2 hx, (Real.sqrt_lt' (by norm_num)).2 (by simpa using hx')⟩

theorem radius_sq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    radius s ^ 2 = 1 - 4 * s ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hs.1, hs.2]

theorem logRatio_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ logRatio t := by
  have h := Real.sum_range_le_log_div ht0 ht1 1
  norm_num at h
  have hplus : 1 + t ≠ 0 := by linarith
  have hminus : 1 - t ≠ 0 := by linarith
  rw [Real.log_div hplus hminus] at h
  unfold logRatio
  linarith

theorem hasDerivAt_radius {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt radius (-4 * s / radius s) s := by
  have hx : 1 - 4 * s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  have hd := (Real.hasDerivAt_sqrt hx).comp s
    ((hasDerivAt_const s (1 : ℝ)).sub (((hasDerivAt_id s).pow 2).const_mul 4))
  convert! hd using 1
  simp [radius]
  ring

theorem binEntropy_derivative_radius {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Real.log (1 - (1 + radius s) / 2) - Real.log ((1 + radius s) / 2) =
      -logRatio (radius s) := by
  have ht := radius_pos_lt_one hs
  have hm : 1 - radius s ≠ 0 := by linarith
  have hp : 1 + radius s ≠ 0 := by linarith
  rw [show 1 - (1 + radius s) / 2 = (1 - radius s) / 2 by ring,
    Real.log_div hm (by norm_num), Real.log_div hp (by norm_num)]
  unfold logRatio
  ring

theorem hasDerivAt_wootters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt wootters (woottersSlope s) s := by
  have ht := radius_pos_lt_one hs
  have hx0 : (1 + radius s) / 2 ≠ 0 := by linarith
  have hx1 : (1 + radius s) / 2 ≠ 1 := by linarith
  have hd := (Real.hasDerivAt_binEntropy hx0 hx1).comp s
    (((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_radius hs)).div_const 2)
  rw [binEntropy_derivative_radius hs] at hd
  convert! hd using 1
  unfold woottersSlope
  ring

theorem hasDerivAt_logRatio {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    HasDerivAt logRatio (2 / (1 - t ^ 2)) t := by
  have hp : 1 + t ≠ 0 := by linarith
  have hm : 1 - t ≠ 0 := by linarith
  have hd := (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).log hp).sub
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log hm)
  convert! hd using 1
  simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub, neg_div]
  have he : 1 - t ^ 2 = (1 + t) * (1 - t) := by ring
  rw [he]
  field_simp
  ring

theorem hasDerivAt_woottersSlope {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt woottersSlope
      (2 * (logRatio (radius s) - 2 * radius s) / radius s ^ 3) s := by
  have ht := radius_pos_lt_one hs
  have ht0 : radius s ≠ 0 := ne_of_gt ht.1
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have ht2 : 1 - radius s ^ 2 = 4 * s ^ 2 := by
    nlinarith [radius_sq ⟨hs.1.le, hs.2.le⟩]
  have hd := (((hasDerivAt_id s).const_mul 2).div (hasDerivAt_radius hs) ht0).mul
    ((hasDerivAt_logRatio (by linarith [ht.1]) ht.2).comp s (hasDerivAt_radius hs))
  convert! hd using 1
  simp only [Pi.div_apply, Function.comp_apply, id_eq, mul_one, ht2]
  field_simp
  have he : radius s ^ 2 + 4 * s ^ 2 - 1 = 0 := by linarith
  linear_combination -logRatio (radius s) * he

theorem deriv_wootters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    deriv wootters s = woottersSlope s := (hasDerivAt_wootters hs).deriv

theorem deriv2_wootters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    deriv^[2] wootters s =
      2 * (logRatio (radius s) - 2 * radius s) / radius s ^ 3 := by
  have he : deriv wootters =ᶠ[𝓝 s] woottersSlope := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
    exact deriv_wootters hx
  exact he.deriv_eq.trans (hasDerivAt_woottersSlope hs).deriv

theorem convexOn_wootters : ConvexOn ℝ (Icc (0 : ℝ) (1 / 2)) wootters := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) continuous_wootters.continuousOn
  · intro s hs
    rw [interior_Icc] at hs
    exact (hasDerivAt_wootters hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have he : deriv wootters =ᶠ[𝓝 s] woottersSlope := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
      exact deriv_wootters hx
    exact ((hasDerivAt_woottersSlope hs).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [deriv2_wootters hs]
    have ht := radius_pos_lt_one hs
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 (logRatio_lower ht.1.le ht.2)))
      (pow_nonneg ht.1.le _)

theorem monotoneOn_wootters : MonotoneOn wootters (Icc (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    continuous_wootters.continuousOn
  · intro s hs
    rw [interior_Icc] at hs
    exact (hasDerivAt_wootters hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have ht := radius_pos_lt_one hs
    unfold woottersSlope
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hs.1.le) ht.1.le)
      (le_trans (mul_nonneg (by norm_num) ht.1.le) (logRatio_lower ht.1.le ht.2))

theorem v_nonneg {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) (p : ℝ) : 0 ≤ v γ ν p := by
  unfold v
  exact add_nonneg (mul_nonneg (mul_nonneg hγ.1 hν.1) (sub_nonneg.2 hν.2))
    (mul_nonneg (mul_nonneg hγ.1 (sub_nonneg.2 hγ.2)) (sq_nonneg _))

theorem v_population_form (γ ν p : ℝ) :
    v γ ν p = ((1 - γ) * p + γ * ν) * (1 - ((1 - γ) * p + γ * ν)) -
      (1 - γ) * p * (1 - p) := by
  unfold v
  ring

theorem v_le_quarter {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (_hν : ν ∈ Icc (0 : ℝ) 1) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    v γ ν p ≤ 1 / 4 := by
  rw [v_population_form]
  have hsub : 0 ≤ (1 - γ) * p * (1 - p) :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hγ.2) hp.1) (sub_nonneg.2 hp.2)
  nlinarith [sq_nonneg (((1 - γ) * p + γ * ν) - 1 / 2)]

theorem sqrt_v_mem {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Real.sqrt (v γ ν p) ∈ Icc (0 : ℝ) (1 / 2) := by
  refine ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left (by norm_num)).2 ?_⟩
  convert v_le_quarter hγ hν hp using 1
  norm_num

theorem convexOn_sqrt_v {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun p ↦ Real.sqrt (v γ ν p)) := by
  let z : ℝ → ℂ := fun p ↦ ⟨Real.sqrt (γ * ν * (1 - ν)),
    Real.sqrt (γ * (1 - γ)) * (p - ν)⟩
  have hA : 0 ≤ γ * ν * (1 - ν) :=
    mul_nonneg (mul_nonneg hγ.1 hν.1) (sub_nonneg.2 hν.2)
  have hB : 0 ≤ γ * (1 - γ) := mul_nonneg hγ.1 (sub_nonneg.2 hγ.2)
  have hz (p : ℝ) : ‖z p‖ = Real.sqrt (v γ ν p) := by
    rw [Complex.norm_def]
    congr 1
    dsimp [z]
    calc
      _ = Real.sqrt (γ * ν * (1 - ν)) ^ 2 +
          Real.sqrt (γ * (1 - γ)) ^ 2 * (p - ν) ^ 2 := by ring
      _ = v γ ν p := by rw [Real.sq_sqrt hA, Real.sq_sqrt hB]; rfl
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  change Real.sqrt (v γ ν (a * x + b * y)) ≤
    a * Real.sqrt (v γ ν x) + b * Real.sqrt (v γ ν y)
  rw [← hz, ← hz, ← hz]
  have he : z (a * x + b * y) = a • z x + b • z y := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    apply Complex.ext <;> simp [z] <;> ring
  rw [he]
  calc
    _ ≤ ‖a • z x‖ + ‖b • z y‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hb]

theorem wootters_sqrt {u : ℝ} (hu : 0 ≤ u) : wootters (Real.sqrt u) = g u := by
  unfold wootters
  rw [Real.sq_sqrt hu]


theorem convexOn_output_entropy {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun p ↦ g (v γ ν p)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hx' := sqrt_v_mem hγ hν hx
  have hy' := sqrt_v_mem hγ hν hy
  have hxy' := sqrt_v_mem hγ hν hxy
  have hc := (convex_Icc (0 : ℝ) (1 / 2)) hx' hy' ha hb hab
  have hm := monotoneOn_wootters hxy' hc ((convexOn_sqrt_v hγ hν).2 hx hy ha hb hab)
  have hh := hm.trans (convexOn_wootters.2 hx' hy' ha hb hab)
  simpa only [wootters_sqrt (v_nonneg hγ hν _)] using hh

theorem continuous_objective (γ ν : ℝ) : Continuous (objective γ ν) := by
  unfold objective v
  exact (Real.binEntropy_continuous.comp (by fun_prop)).sub
    (continuous_g.comp (by fun_prop))

/-- Existence of the genuine scalar maximum rather than a supremum surrogate. -/
theorem exists_maximizer (γ ν : ℝ) :
    ∃ p ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, objective γ ν q ≤ objective γ ν p := by
  exact isCompact_Icc.exists_isMaxOn (by norm_num) (continuous_objective γ ν).continuousOn

end GAD

end

end OAI
