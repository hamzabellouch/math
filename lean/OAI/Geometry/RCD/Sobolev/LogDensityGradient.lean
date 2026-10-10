import OAI.Geometry.RCD.Transport.RenyiEnergyIntegrability

namespace OAI

/-! # The relative gradient bound of a bounded log-Lipschitz density -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem exp_comp_lipschitz_of_bounded {g : X → ℝ} {L M : ℝ≥0}
    (hg : LipschitzWith L g) (hb : ∀ x, Real.exp (g x)≤M) :
    LipschitzWith (M*L) (fun x => Real.exp (g x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : Real.exp (max (g y) (g x))≤M := by
    rcases le_total (g y) (g x) with h|h
    · simpa only [max_eq_right h] using hb x
    · simpa only [max_eq_left h] using hb y
  have hi := exp_increment_bound (g y) (g x)
  have hL := hg.dist_le_mul x y
  rw [Real.dist_eq] at hL ⊢
  have hh := mul_le_mul he hL (abs_nonneg _) M.coe_nonneg
  exact hi.trans (by simpa only [NNReal.coe_mul,mul_assoc] using hh)

theorem localSlope_exp_comp_le {g : X → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : X) :
    localSlope (fun y => Real.exp (g y)) x≤ENNReal.ofReal ((L:ℝ)*Real.exp (g x)) := by
  have hc : Continuous (fun r : ℝ => ENNReal.ofReal ((L:ℝ)*Real.exp (g x+(L:ℝ)*r))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht := (hc.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  simp only [mul_zero,add_zero] at ht
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0<r at hr
  unfold localSlope
  apply iInf_le_of_le r
  apply iInf_le_of_le hr
  refine iSup_le fun y => iSup_le fun hyr => iSup_le fun hyx => ?_
  apply ENNReal.ofReal_le_ofReal
  have hd : 0<dist x y := dist_pos.mpr (Ne.symm hyx)
  apply (div_le_iff₀ hd).mpr
  have hL : |g y-g x|≤(L:ℝ)*dist x y := by
    simpa only [Real.dist_eq,abs_sub_comm (g x) (g y)] using hg.dist_le_mul x y
  have hgy : g y≤g x+(L:ℝ)*r := by
    have hh := mul_le_mul_of_nonneg_left hyr.le L.coe_nonneg
    linarith [le_abs_self (g y-g x)]
  have hgx : g x≤g x+(L:ℝ)*r := by nlinarith [L.coe_nonneg,le_of_lt hr]
  calc
    _ ≤ Real.exp (max (g x) (g y))*|g y-g x| := exp_increment_bound _ _
    _ ≤ Real.exp (g x+(L:ℝ)*r)*((L:ℝ)*dist x y) :=
      mul_le_mul (Real.exp_le_exp.mpr (max_le hgx hgy)) hL (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem SobolevSpace.relative_gradient_of_log_lipschitz (ρ : SobolevSpace μ hQ)
    {g : X → ℝ} {L M : ℝ≥0} (hg : LipschitzWith L g) (hb : ∀ x, Real.exp (g x)≤M)
    (hρ : SobolevSpace.toLp μ hQ ρ =ᵐ[μ] fun x => Real.exp (g x)) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ ρ x≤(L:ℝ)*SobolevSpace.toLp μ hQ ρ x := by
  have hLip := exp_comp_lipschitz_of_bounded hg hb
  have hs (x : X) : (localSlope (fun y => Real.exp (g y)) x).toReal≤(L:ℝ)*Real.exp (g x) := by
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (localSlope_exp_comp_le hg x)
    simpa only [ENNReal.toReal_ofReal (mul_nonneg L.coe_nonneg (Real.exp_pos _).le)] using he
  have hm : MemLp (fun x => (localSlope (fun y => Real.exp (g y)) x).toReal) 2 μ := by
    apply ((Lp.memLp (SobolevSpace.toLp μ hQ ρ)).const_mul (L:ℝ)).mono'
      (localSlope_measurable hLip.continuous).ennreal_toReal.aestronglyMeasurable
    filter_upwards [hρ] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,hx] using hs x
  filter_upwards [SobolevSpace.minimalSlope_le_localSlope μ hQ ρ hLip hρ hm,hρ] with x hx hr
  rw [hr]
  exact hx.trans (hs x)

end RegularPointCoordinates

end

end OAI
