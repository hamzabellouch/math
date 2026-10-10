import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeRadius

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma spherical_flux_norm_le {F : Vec → Vec} {ε C : ℝ} (hε : 0<ε)
    (hF : ∀ z : Vec, ‖z‖=ε → ‖F z‖≤C/ε) :
    ‖∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure‖ ≤ C*ε*(4*Real.pi) := by
  have hb (n : Sphere) : ‖ε^2*dot n.1 (F (ε • n.1))‖≤C*ε := by
    have hn : ‖ε • n.1‖=ε := by rw [norm_smul,Real.norm_of_nonneg hε.le,sphere_norm,mul_one]
    have hd : ‖dot n.1 (F (ε • n.1))‖≤C/ε := by
      calc
        _ ≤ ‖n.1‖*‖F (ε • n.1)‖ := by
          simpa only [dot_eq_inner,Real.norm_eq_abs] using abs_real_inner_le_norm (n.1 : Vec) (F (ε • n.1))
        _ ≤ C/ε := by rw [sphere_norm,one_mul]; exact hF _ hn
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg ε)]
    calc
      ε^2*‖dot n.1 (F (ε • n.1))‖≤ε^2*(C/ε) := mul_le_mul_of_nonneg_left hd (sq_nonneg ε)
      _ = C*ε := by field_simp [hε.ne']
  simpa only [sphere_area] using (norm_integral_le_of_norm_le_const (μ := sphereMeasure) (ae_of_all _ hb))

lemma spherical_flux_tendsto_zero {F : Vec → Vec} {R C : ℝ} (hR : 0<R)
    (hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → ‖F z‖≤C/‖z‖) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun ε => C*ε*(4*Real.pi))
  · filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    apply spherical_flux_norm_le hε.1
    intro z hz
    simpa only [hz] using hF z (by rw [hz]; exact hε.1) (by rw [hz]; exact hε.2)
  · simpa using ((tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const (4*Real.pi) :
      Tendsto (fun ε : ℝ => C*ε*(4*Real.pi)) (𝓝[>] (0:ℝ)) (𝓝 (C*0*(4*Real.pi))))

lemma fderiv_norm_apply_rvm {z : Vec} (hz : z≠0) (w : Vec) :
    fderiv ℝ (fun y : Vec => ‖y‖) z w=dot z w/‖z‖ := by
  have hc : HasDerivAt (fun r : ℝ => z+r • w) w 0 := by
    have hh := (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id (0:ℝ)).smul_const w)
    change HasDerivAt (fun r : ℝ => z+r • w) (0+(1:ℝ) • w) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hd : HasFDerivAt (fun y : Vec => ‖y‖) (fderiv ℝ (fun y : Vec => ‖y‖) z) (z+(0:ℝ) • w) := by
    simpa using (differentiableAt_id.norm ℝ hz).hasFDerivAt
  have hn := hd.comp_hasDerivAt (0:ℝ) hc
  have hm := hasDerivAt_norm_nonzero hc (by simpa using hz)
  simpa using hn.unique hm

lemma fderiv_conePotential_apply {ρ : ℝ × Vec → ℝ} {t : ℝ} {x z : Vec}
    (hρ : DifferentiableAt ℝ ρ (t-‖z‖,x+z)) (hz : z≠0) (w : Vec) :
    fderiv ℝ (fun y : Vec => ρ (t-‖y‖,x+y)/‖y‖) z w =
      fderiv ℝ ρ (t-‖z‖,x+z) (0,w)/‖z‖ -
      dot z w/‖z‖^2 * dirD ρ (1,0) (t-‖z‖,x+z) -
      dot z w/‖z‖^3 * ρ (t-‖z‖,x+z) := by
  have hn : DifferentiableAt ℝ (fun y : Vec => ‖y‖) z := differentiableAt_id.norm ℝ hz
  have hi := ((hasFDerivAt_const t z).sub hn.hasFDerivAt).prodMk
    ((hasFDerivAt_const x z).add (hasFDerivAt_id z))
  have hp := hρ.hasFDerivAt.comp z hi
  have hh := hp.mul ((hasFDerivAt_inv (norm_ne_zero_iff.mpr hz)).comp z hn.hasFDerivAt)
  change HasFDerivAt (fun y : Vec => ρ (t-‖y‖,x+y)*‖y‖⁻¹) _ z at hh
  simp_rw [div_eq_mul_inv] at ⊢
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    add_apply,ContinuousLinearMap.id_apply,
    smul_eq_mul,zero_sub,zero_add,neg_apply,fderiv_norm_apply_rvm hz,ContinuousLinearMap.toSpanSingleton_apply]
  have he : (- (dot z w/‖z‖),w) = ((0:ℝ),w)-(dot z w/‖z‖) • ((1:ℝ),(0:Vec)) := by ext <;> simp
  rw [he,map_sub,map_smul]
  unfold dirD
  simp only [smul_eq_mul,Function.comp_apply,Pi.add_apply,Pi.sub_apply,id_eq]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma divergence_conePotential {ρ : ℝ × Vec → ℝ} {t : ℝ} {x z : Vec}
    (hρ : DifferentiableAt ℝ ρ (t-‖z‖,x+z)) (hz : z≠0) (i : Fin 3) :
    divergence (fun y : Vec => (ρ (t-‖y‖,x+y)/‖y‖) • basis i) z =
      dirD ρ (0,basis i) (t-‖z‖,x+z)/‖z‖ -
      z i/‖z‖^2 * dirD ρ (1,0) (t-‖z‖,x+z) -
      z i/‖z‖^3 * ρ (t-‖z‖,x+z) := by
  have hn : DifferentiableAt ℝ (fun y : Vec => ‖y‖) z := differentiableAt_id.norm ℝ hz
  have harg : DifferentiableAt ℝ (fun y : Vec => (t-‖y‖,x+y)) z :=
    ((differentiableAt_const t).sub hn).prodMk ((differentiableAt_const x).add differentiableAt_id)
  have hg : DifferentiableAt ℝ (fun y : Vec => ρ (t-‖y‖,x+y)/‖y‖) z :=
    by
      have hp : DifferentiableAt ℝ (fun y : Vec => ρ (t-‖y‖,x+y)) z := hρ.comp z harg
      exact (hp.hasFDerivAt.mul ((hasFDerivAt_inv (norm_ne_zero_iff.mpr hz)).comp z hn.hasFDerivAt)).differentiableAt
  rw [divergence_smul hg (differentiableAt_const _),divergence_const_rvm,mul_zero,add_zero,
    dot_gradient_direction,fderiv_conePotential_apply hρ hz]
  simp [dot,basis,dirD]

lemma integrableOn_ball_div_norm_pow {g : Vec → ℝ} (hg : Continuous g)
    (k : ℕ) (hk : k<3) (R : ℝ) :
    IntegrableOn (fun z : Vec => g z/‖z‖^k) (ball (0:Vec) R) := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vec) R).image hg).isBounded.exists_norm_le
  apply integrableOn_ball_of_norm_le_rpow (by simp) (α:=(k:ℝ)) (C:=C) (by simpa using hk)
  · apply ae_restrict_of_forall_mem measurableSet_ball
    intro z hz
    have hh := hC _ ⟨z,ball_subset_closedBall hz,rfl⟩
    rw [norm_div,norm_pow,norm_norm,Real.rpow_neg (norm_nonneg z),Real.rpow_natCast,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) k))
  · exact (hg.measurable.div (continuous_norm.pow k).measurable).aestronglyMeasurable

lemma norm_direction_coord_le (z : Vec) (i : Fin 3) : ‖z i/‖z‖‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  rw [norm_div,norm_norm,div_le_one (norm_pos_iff.mpr hz)]
  exact PiLp.norm_apply_le z i

lemma integrableOn_ball_direction_div_norm_pow {g : Vec → ℝ} (hg : Continuous g)
    (k : ℕ) (hk : k<3) (R : ℝ) (i : Fin 3) :
    IntegrableOn (fun z : Vec => z i/‖z‖^(k+1)*g z) (ball (0:Vec) R) := by
  have hm : Measurable (fun z : Vec => z i/‖z‖) := (PiLp.continuous_apply 2 _ i).measurable.div continuous_norm.measurable
  have hi := (integrableOn_ball_div_norm_pow hg k hk R).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun z => norm_direction_coord_le z i))
  apply hi.congr
  filter_upwards [] with z
  simp only [pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

lemma contDiffAt_conePotential {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t : ℝ) (x : Vec) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ ∞ (fun y : Vec => ρ (t-‖y‖,x+y)/‖y‖) z := by
  have hn : ContDiffAt ℝ ∞ (fun y : Vec => ‖y‖) z := contDiffAt_id.norm ℝ hz
  have hp : ContDiffAt ℝ ∞ (fun y : Vec => ρ (t-‖y‖,x+y)) z :=
    hρ.contDiffAt.comp z ((contDiffAt_const.sub hn).prodMk (contDiffAt_const.add contDiffAt_id))
  exact hp.div hn (norm_ne_zero_iff.mpr hz)

lemma integrable_conePotential_divergence {ρ : ℝ × Vec → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (t : ℝ) (x : Vec) (i : Fin 3) :
    IntegrableOn (divergence (fun y : Vec => (ρ (t-‖y‖,x+y)/‖y‖) • basis i))
      (ball (0:Vec) t) := by
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi₁ := integrableOn_ball_div_norm_pow ((contDiff_dirD hρ (0,basis i)).continuous.comp harg)
    1 (by norm_num) t
  have hi₂ := integrableOn_ball_direction_div_norm_pow ((contDiff_dirD hρ (1,0)).continuous.comp harg)
    1 (by norm_num) t i
  have hi₃ := integrableOn_ball_direction_div_norm_pow (hρ.continuous.comp harg) 2 (by norm_num) t i
  apply ((hi₁.sub hi₂).sub hi₃).congr
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz
  simpa only [pow_one,Function.comp_apply,Pi.sub_apply] using
    (divergence_conePotential (hρ.differentiable (by simp) _) hz i).symm

lemma conePotential_tip_flux {ρ : ℝ × Vec → ℝ} (hρ : Continuous ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1
      ((ρ (t-‖ε • n.1‖,x+ε • n.1)/‖ε • n.1‖) • basis i) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun z : Vec => ρ (t-‖z‖,x+z)) :=
    hρ.comp ((continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vec) t).image hc).isBounded.exists_norm_le
  apply spherical_flux_tendsto_zero (F:=fun z : Vec => (ρ (t-‖z‖,x+z)/‖z‖) • basis i)
    (C:=C*‖basis i‖) ht
  intro z hz hzt
  have hh := hC _ ⟨z,(by simpa only [mem_closedBall_zero_iff] using hzt.le),rfl⟩
  rw [norm_smul,norm_div,norm_norm]
  calc
    ‖ρ (t-‖z‖,x+z)‖/‖z‖*‖basis i‖ ≤ C/‖z‖*‖basis i‖ :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh hz.le) (norm_nonneg _)
    _ = C*‖basis i‖/‖z‖ := by ring

lemma conePotential_spatial_ibp {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) t, dirD ρ (0,basis i) (t-‖z‖,x+z)/‖z‖) =
      (∫ z in ball (0:Vec) t,
        z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) + z i/‖z‖^3*ρ (t-‖z‖,x+z)) +
      ∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure := by
  have hg := divergence_ball_singular ht (show t<t+1 by linarith)
    (F:=fun z : Vec => (ρ (t-‖z‖,x+z)/‖z‖) • basis i)
    (fun z hz _ => ((contDiffAt_conePotential hρ t x (norm_ne_zero_iff.mp hz.ne')).of_le (by simp)).smul contDiffAt_const)
    (integrable_conePotential_divergence hρ t x i) (conePotential_tip_flux hρ.continuous ht x i)
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi₁ := integrableOn_ball_div_norm_pow ((contDiff_dirD hρ (0,basis i)).continuous.comp harg)
    1 (by norm_num) t
  have hi₂ := integrableOn_ball_direction_div_norm_pow ((contDiff_dirD hρ (1,0)).continuous.comp harg)
    1 (by norm_num) t i
  have hi₃ := integrableOn_ball_direction_div_norm_pow (hρ.continuous.comp harg) 2 (by norm_num) t i
  have he : (∫ z in ball (0:Vec) t, divergence (fun y : Vec => (ρ (t-‖y‖,x+y)/‖y‖) • basis i) z) =
      (∫ z in ball (0:Vec) t, dirD ρ (0,basis i) (t-‖z‖,x+z)/‖z‖) -
      (∫ z in ball (0:Vec) t, z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z)) -
      (∫ z in ball (0:Vec) t, z i/‖z‖^3*ρ (t-‖z‖,x+z)) := by
    rw [← integral_sub (by simpa [IntegrableOn] using hi₁) (by simpa [IntegrableOn] using hi₂),
      ← integral_sub (by simpa [IntegrableOn] using Integrable.sub' hi₁ hi₂) (by simpa [IntegrableOn] using hi₃)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz
    exact divergence_conePotential (hρ.differentiable (by simp) _) hz i
  have hb : (∫ n : Sphere, t^2*dot n.1 ((ρ (t-‖t • n.1‖,x+t • n.1)/‖t • n.1‖) • basis i) ∂sphereMeasure) =
      ∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure := by
    apply integral_congr_ae
    filter_upwards [] with n
    have hn : ‖t • n.1‖=t := by rw [norm_smul,Real.norm_of_nonneg ht.le,sphere_norm,mul_one]
    rw [hn,sub_self,dot_smul_right]
    have hd : dot n.1 (basis i)=n.1 i := by simp [dot,basis]
    rw [hd]
    field_simp
  rw [he,hb] at hg
  rw [integral_add (by simpa [IntegrableOn] using hi₂) (by simpa [IntegrableOn] using hi₃)]
  linarith
end RVM

end

end OAI
