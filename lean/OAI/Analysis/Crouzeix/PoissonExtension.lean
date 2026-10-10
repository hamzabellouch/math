import Mathlib

namespace OAI

/-! Poisson Extension. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

def poissonExtension (R : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  circleAverage (fun ζ => poissonKernel 0 w ζ * u ζ) 0 R

def schwarzExtension (R : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  circleAverage (fun ζ => herglotzRieszKernel 0 w ζ * (u ζ : ℂ)) 0 R

theorem schwarzExtension_re {R : ℝ} {u : ℂ → ℝ} (hu : CircleIntegrable u 0 R)
    {w : ℂ} (hw : w ∈ ball 0 R) : (schwarzExtension R u w).re = poissonExtension R u w := by
  simpa only [schwarzExtension, poissonExtension, poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.mul_def] using
    re_circleAverage_herglotzRieszKernel_smul hu (by
      rw [mem_sphere]
      exact ne_of_lt ((mem_ball.mp hw).trans_le (le_abs_self R)))

theorem analyticOnNhd_schwarzExtension {R : ℝ} {u : ℂ → ℝ} (hR : 0 ≤ R)
    (hu : ContinuousOn u (sphere 0 R)) : AnalyticOnNhd ℂ (schwarzExtension R u) (ball 0 R) := by
  intro w hw
  exact analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    (ContinuousOn.circleIntegrable hR (continuous_ofReal.comp_continuousOn hu)) w (by
      rw [mem_compl_iff, mem_sphere]
      exact ne_of_lt ((mem_ball.mp hw).trans_le (le_abs_self R)))

theorem harmonicOnNhd_poissonExtension {R : ℝ} {u : ℂ → ℝ} (hR : 0 ≤ R)
    (hu : ContinuousOn u (sphere 0 R)) : HarmonicOnNhd (poissonExtension R u) (ball 0 R) := by
  intro w hw
  have he : (fun z => (schwarzExtension R u z).re) =ᶠ[𝓝 w] poissonExtension R u := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    exact schwarzExtension_re (ContinuousOn.circleIntegrable hR hu) hz
  exact (harmonicAt_congr_nhds he).mp (analyticOnNhd_schwarzExtension hR hu w hw).harmonicAt_re

theorem poissonKernel_nonneg {R : ℝ} {w ζ : ℂ} (hw : w ∈ ball 0 R)
    (hζ : ζ ∈ sphere 0 R) : 0 ≤ poissonKernel 0 w ζ := by
  have hR := pos_of_mem_ball hw
  have hwN := mem_ball_zero_iff.mp hw
  have hζN := mem_sphere_zero_iff_norm.mp hζ
  simp only [poissonKernel, sub_zero, hζN]
  exact div_nonneg (by nlinarith [norm_nonneg w]) (sq_nonneg _)

theorem continuousOn_poissonKernel {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere (by
    rw [mem_sphere]
    exact ne_of_lt ((mem_ball.mp hw).trans_le (le_abs_self R))))

theorem circleAverage_poissonKernel {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    circleAverage (poissonKernel 0 w) 0 R = 1 := by
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, mul_one, Pi.one_apply, Pi.mul_def] using
    (harmonicContOnCl_const (c := (1 : ℝ)) (s := ball (0 : ℂ) R)).circleAverage_poissonKernel_smul hw

theorem tendsto_poissonExtension_at_sphere {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {p : ℂ} (hp : p ∈ sphere 0 R) :
    Tendsto (poissonExtension R u) (𝓝[ball 0 R] p) (𝓝 (u p)) := by
  have hpN : ‖p‖ = R := mem_sphere_zero_iff_norm.mp hp
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hu.sub continuousOn_const : ContinuousOn (fun t => u t - u p) (sphere 0 R))
  have hB0 : 0 ≤ B := (norm_nonneg (u p - u p)).trans (hB p hp)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousWithinAt_iff.mp (hu p hp) (ε / 2) (by positivity)
  let c : ℂ → ℝ := fun w => B * (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2
  have hc : Tendsto c (𝓝 p) (𝓝 0) := by
    have hc' : Continuous c := by dsimp [c]; fun_prop
    simpa only [c, hpN, sub_self, mul_zero, zero_div] using hc'.continuousAt.tendsto (x := p)
  filter_upwards [Filter.mem_inf_of_left (ball_mem_nhds p (half_pos hδ)),
      Filter.mem_inf_of_left (hc.eventually (gt_mem_nhds (half_pos hε))),
      self_mem_nhdsWithin] with w hwp hcε hw
  have hc0 : 0 ≤ c w := by
    have hwn := mem_ball_zero_iff.mp hw
    dsimp [c]
    exact div_nonneg (mul_nonneg hB0 (by nlinarith [norm_nonneg w])) (sq_nonneg _)
  have hPc := continuousOn_poissonKernel hw
  rw [abs_of_pos hR] at hPc
  have huP : ContinuousOn (fun t => poissonKernel 0 w t * (u t - u p)) (sphere 0 R) :=
    hPc.mul (hu.sub continuousOn_const)
  have hpoint : ∀ t ∈ sphere (0 : ℂ) R,
      |poissonKernel 0 w t * (u t - u p)| ≤ poissonKernel 0 w t * (ε / 2) + c w := by
    intro t ht
    have hPn := poissonKernel_nonneg hw ht
    rw [abs_mul, abs_of_nonneg hPn]
    by_cases htp : dist t p < δ
    · have hm := hmod ht htp
      rw [Real.dist_eq] at hm
      exact (mul_le_mul_of_nonneg_left hm.le hPn).trans (le_add_of_nonneg_right hc0)
    · have hdist : δ / 2 ≤ ‖t - w‖ := by
        have htδ := le_of_not_gt htp
        have hd := dist_triangle t w p
        rw [mem_ball] at hwp
        rw [dist_eq_norm t w] at hd
        linarith
      have hn : 0 ≤ R ^ 2 - ‖w‖ ^ 2 := by
        have := mem_ball_zero_iff.mp hw
        nlinarith [norm_nonneg w]
      have hPK : poissonKernel 0 w t ≤ (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2 := by
        simp only [poissonKernel, sub_zero, mem_sphere_zero_iff_norm.mp ht]
        apply div_le_div_of_nonneg_left hn (sq_pos_of_pos (half_pos hδ))
        exact pow_le_pow_left₀ (le_of_lt (half_pos hδ)) hdist 2
      have htB : |u t - u p| ≤ B := by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hB t ht
      calc
        _ ≤ poissonKernel 0 w t * B := mul_le_mul_of_nonneg_left htB hPn
        _ ≤ (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2 * B := mul_le_mul_of_nonneg_right hPK hB0
        _ = c w := by dsimp [c]; ring
        _ ≤ poissonKernel 0 w t * (ε / 2) + c w := le_add_of_nonneg_left (by positivity)
  have hint : CircleIntegrable (fun t => poissonKernel 0 w t * (u t - u p)) 0 R :=
    ContinuousOn.circleIntegrable hR.le huP
  have hiabs : CircleIntegrable (fun t => |poissonKernel 0 w t * (u t - u p)|) 0 R :=
    ContinuousOn.circleIntegrable hR.le huP.abs
  have hiup : CircleIntegrable (fun t => poissonKernel 0 w t * (ε / 2) + c w) 0 R :=
    ContinuousOn.circleIntegrable hR.le ((hPc.mul_const _).add continuousOn_const)
  have heq : poissonExtension R u w - u p =
      circleAverage (fun t => poissonKernel 0 w t * (u t - u p)) 0 R := by
    simp_rw [mul_sub]
    rw [circleAverage_fun_sub (f₁ := fun t => poissonKernel 0 w t * u t)
      (f₂ := fun t => poissonKernel 0 w t * u p)
      (ContinuousOn.circleIntegrable hR.le (hPc.mul hu))
      (ContinuousOn.circleIntegrable hR.le (hPc.mul_const _))]
    have hm : circleAverage (fun t => poissonKernel 0 w t * u p) 0 R = u p := by
      simp_rw [mul_comm _ (u p), ← smul_eq_mul]
      rw [circleAverage_fun_smul, circleAverage_poissonKernel hw, smul_eq_mul, mul_one]
    rw [hm]
    rfl
  have hupeq : circleAverage (fun t => poissonKernel 0 w t * (ε / 2) + c w) 0 R = ε / 2 + c w := by
    rw [circleAverage_fun_add (ContinuousOn.circleIntegrable hR.le (hPc.mul_const _))
      (ContinuousOn.circleIntegrable hR.le continuousOn_const), circleAverage_const]
    simp_rw [mul_comm _ (ε / 2), ← smul_eq_mul]
    rw [circleAverage_fun_smul, circleAverage_poissonKernel hw, smul_eq_mul, mul_one]
  rw [Real.dist_eq, heq]
  calc
    _ ≤ circleAverage (fun t => |poissonKernel 0 w t * (u t - u p)|) 0 R :=
      abs_circleAverage_le_circleAverage_abs
    _ ≤ circleAverage (fun t => poissonKernel 0 w t * (ε / 2) + c w) 0 R :=
      circleAverage_mono hiabs hiup (by simpa only [abs_of_pos hR] using hpoint)
    _ = ε / 2 + c w := hupeq
    _ < ε := by linarith

def dirichletExtension (R : ℝ) (u : ℂ → ℝ) : ℂ → ℝ :=
  (ball (0 : ℂ) R).piecewise (poissonExtension R u) u

theorem dirichletExtension_eq_on_sphere {R : ℝ} {u : ℂ → ℝ} :
    EqOn (dirichletExtension R u) u (sphere 0 R) := by
  intro p hp
  exact piecewise_eq_of_notMem _ _ _ (not_lt.mpr (mem_sphere.mp hp).ge)

theorem dirichletExtension_eventuallyEq {R : ℝ} {u : ℂ → ℝ} {p : ℂ}
    (hp : p ∈ ball 0 R) : dirichletExtension R u =ᶠ[𝓝 p] poissonExtension R u := by
  filter_upwards [isOpen_ball.mem_nhds hp] with z hz
  exact piecewise_eq_of_mem _ _ _ hz

theorem harmonicContOnCl_dirichletExtension {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    HarmonicContOnCl (dirichletExtension R u) (ball 0 R) := by
  refine HarmonicContOnCl.mk_ball (fun p hp => ?_) ?_
  · exact (harmonicAt_congr_nhds (dirichletExtension_eventuallyEq hp)).mpr
      (harmonicOnNhd_poissonExtension hR.le hu p hp)
  · intro p hp
    rcases lt_or_eq_of_le (mem_closedBall.mp hp) with hi | hb
    · exact ((harmonicOnNhd_poissonExtension hR.le hu p hi).1.continuousAt.congr
        (dirichletExtension_eventuallyEq hi).symm).continuousWithinAt
    · have hs : p ∈ sphere (0 : ℂ) R := hb
      have he := dirichletExtension_eq_on_sphere (u := u) hs
      have hball : ContinuousWithinAt (dirichletExtension R u) (ball 0 R) p := by
        rw [ContinuousWithinAt, he]
        apply (tendsto_poissonExtension_at_sphere hR hu hs).congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (piecewise_eq_of_mem _ _ _ hz).symm
      have hsphere : ContinuousWithinAt (dirichletExtension R u) (sphere 0 R) p :=
        (hu p hs).congr dirichletExtension_eq_on_sphere he
      simpa only [ball_union_sphere] using hball.union hsphere

theorem circleAverage_comp_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) : circleAverage (fun z => f (conj z)) 0 R = circleAverage f 0 R := by
  rw [circleAverage_eq_circleAverage_zero_one, circleAverage_eq_circleAverage_zero_one (f := f)]
  calc
    _ = circleAverage (fun z => f ((R : ℂ) * z⁻¹ + 0)) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have hzN : ‖z‖ = 1 := by simpa only [abs_one] using mem_sphere_zero_iff_norm.mp hz
      simp only [Complex.inv_eq_conj hzN, map_add, map_mul, Complex.conj_ofReal, map_zero]
    _ = _ := circleAverage_zero_one_congr_inv (f := fun z => f ((R : ℂ) * z + 0))

theorem poissonExtension_conj {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ∀ z ∈ sphere 0 R, u (conj z) = -u z) (w : ℂ) :
    poissonExtension R u (conj w) = -poissonExtension R u w := by
  unfold poissonExtension
  rw [← circleAverage_comp_conj (fun z => poissonKernel 0 (conj w) z * u z) R]
  calc
    _ = circleAverage (fun z => (-1 : ℝ) • (poissonKernel 0 w z * u z)) 0 R := by
      apply circleAverage_congr_sphere
      intro z hz
      have he : poissonKernel 0 (conj w) (conj z) = poissonKernel 0 w z := by
        simp only [poissonKernel, sub_zero, ← map_sub, Complex.norm_conj]
      dsimp only
      rw [he, hu z (by simpa only [abs_of_nonneg hR] using hz)]
      simp
    _ = _ := by rw [circleAverage_fun_smul, neg_one_smul]

end CrouzeixHilbert.Conformal

end

end OAI
