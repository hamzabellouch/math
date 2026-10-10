import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.NullConeFlux
import OAI.Analysis.VlasovMaxwell.Retarded.RetardedPhaseDomain

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
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
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace RVM.EnergyPrefix

lemma deriv_moving_energy {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {U : Set ℝ} (hU : IsOpen U) (hpos : U ⊆ Ioo 0 T)
    {g : ℝ × Vec → ℝ} {K : Set Vec} (hK : IsCompact K)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ (univ : Set Vec)))
    (hz : ∀ r ∈ U, ∀ x ∉ K, g (r,x)=0)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x))
      (∫ x : Vec, fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) +
        fderiv ℝ g (t,x) (0,totalFlux s (t,x))) t := by
  have hE := (total_energy_regular hs).mono (prod_mono_left hpos)
  have hF : ContDiffOn ℝ 1 (fun p => g p * totalEnergy s p)
      (U ×ˢ (univ : Set Vec)) := hg.mul hE
  have hzF : ∀ r ∈ U, ∀ x ∉ K, g (r,x)*totalEnergy s (r,x)=0 := by
    intro r hr x hx
    rw [hz r hr x hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support hU hK ht hF hzF
  have hi := fderiv_integral_uniform_support_apply hU hK ht hF hzF (1:ℝ)
  have hgg : ContDiff ℝ 1 (fun x => g (t,x)) := by
    apply ContDiffOn.comp_contDiff hg (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : ContDiff ℝ 1 (fun x => totalFlux s (t,x)) := by
    apply ContDiffOn.comp_contDiff ((total_flux_regular hs).mono (prod_mono_left hpos))
      (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hEc : Continuous (fun x => totalEnergy s (t,x)) := by
    apply hE.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hgD : Continuous (fun x => fderiv ℝ g (t,x)) := by
    apply (hg.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hDc : HasCompactSupport (fun x => fderiv ℝ g (t,x)) :=
    compactSupport_param_fderiv hU hK ht hz
  have hgC : HasCompactSupport (fun x => g (t,x)) :=
    compactSupport_of_zero_off hK (hz t ht)
  have hgDapply (v : ℝ × Vec) : HasCompactSupport (fun x => fderiv ℝ g (t,x) v) := by
    apply compactSupport_of_zero_off hDc
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]
  have hIt : Integrable (fun x => fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x)) :=
    ((hgD.clm_apply continuous_const).mul hEc).integrable_of_hasCompactSupport
      (hgDapply (1,0)).mul_right
  have hIa : Integrable (fun x => g (t,x) * divergence (fun y => totalFlux s (t,y)) x) :=
    (hgg.continuous.mul (continuous_divergence hS)).integrable_of_hasCompactSupport hgC.mul_right
  have hIs : Integrable (fun x => fderiv ℝ (fun y => g (t,y)) x (totalFlux s (t,x))) :=
    ((hgg.continuous_fderiv (by simp)).clm_apply hS.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hgC.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]))
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p => g p * totalEnergy s p) (t,x) (1,0) =
        fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) -
          g (t,x) * divergence (fun y => totalFlux s (t,y)) x := by
    intro x
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hg' := (hg.contDiffAt hn).differentiableAt (by simp)
    have hE' := (hE.contDiffAt hn).differentiableAt (by simp)
    change fderiv ℝ (g * totalEnergy s) (t,x) (1,0) = _
    rw [fderiv_mul hg' hE',add_apply,
      smul_apply,smul_apply,
      smul_eq_mul,smul_eq_mul,← deriv_time_slice hE']
    have hl := local_energy_conservation hs (hpos ht) x
    rw [show deriv (fun r => totalEnergy s (r,x)) t =
      -divergence (fun y => totalFlux s (t,y)) x by linarith]
    ring
  have hxder (x v : Vec) : fderiv ℝ (fun y => g (t,y)) x v = fderiv ℝ g (t,x) (0,v) := by
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hh := ((hg.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun y => g (t,y)) _ x at hh
    rw [hh.fderiv]
    simp
  have hh : deriv (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x)) t =
      ∫ x : Vec, fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) +
        fderiv ℝ g (t,x) (0,totalFlux s (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
    rw [integral_sub hIt hIa,integral_mul_divergence hS hgg hgC,sub_neg_eq_add]
    simp_rw [← hxder]
    exact (integral_add hIt hIs).symm
  exact hh ▸ hd.differentiableAt.hasDerivAt

lemma coneShellFlux_nonneg {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T) (x x₀ : Vec) :
    0 ≤ coneShellFlux s T ε x₀ (t,x) := by
  by_cases hr : ‖x-x₀‖ ≤ T-t
  · apply mul_nonneg (mul_nonneg (by positivity) (deriv_transition_nonneg _))
    have hb := total_flux_bound hs ht x
    have he := total_energy_nonneg hs ht x
    have hc := real_inner_le_norm (-(x-x₀)) (totalFlux s (t,x))
    simp only [inner_neg_left,norm_neg] at hc
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (x-x₀)),
      mul_le_mul_of_nonneg_right hr he]
  · have hn : coneArgument T ε x₀ (t,x) < 0 := by
      dsimp [coneArgument]
      apply div_neg_of_neg_of_pos _ hε
      have := norm_nonneg (x-x₀)
      push Not at hr
      have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
      nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr hr]
    simp [coneShellFlux,deriv_transition_zero_neg hn]

lemma deriv_cone_energy {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Ioo 0 T) (x₀ : Vec) :
    HasDerivAt (fun r => ∫ x : Vec, coneCutoff T ε x₀ (r,x)*totalEnergy s (r,x))
      (-(∫ x : Vec, coneShellFlux s T ε x₀ (t,x))) t := by
  have hh := deriv_moving_energy hs isOpen_Ioo Subset.rfl
    (isCompact_closedBall x₀ T) (contDiff_coneCutoff T ε x₀ (k := 1)).contDiffOn
    (fun r hr x hx => coneCutoff_zero_outside hε ⟨hr.1.le,hr.2.le⟩ hx) ht
  convert hh using 1
  rw [← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [coneCutoff_fderiv,coneCutoff_fderiv]
  simp only [inner_zero_right,mul_zero,mul_one,sub_zero,zero_sub]
  dsimp [coneShellFlux]
  ring

lemma particle_flux_continuous_slab {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (_hT : 0 ≤ T) :
    ContinuousOn (particleFlux s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, s.f (p.1,p.2,v) • v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => s.f (z.1.1,z.1.2,z.2) • z.2) (hK.image continuous_snd)
  · have hf : ContinuousOn (fun z : (ℝ × Vec) × Vec => s.f (z.1.1,z.1.2,z.2))
        ((Icc 0 T ×ˢ univ) ×ˢ univ) := by
      apply hs.f_smooth.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      intro z hz
      exact ⟨hz.1.1,mem_univ _⟩
    exact hf.smul continuous_snd.continuousOn
  · intro p hp v hv
    have hf : s.f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hf,zero_smul]

lemma total_flux_continuous_slab {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) :
    ContinuousOn (totalFlux s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  exact ((contDiff_cross (k := 1)).continuous.comp_continuousOn
    (hs.E_smooth.continuousOn.prodMk hs.B_smooth.continuousOn)).add
      (particle_flux_continuous_slab hs hT)

lemma coneShellFlux_continuous_slab {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {ε : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    ContinuousOn (coneShellFlux s T ε x₀) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hθ : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by simp)
  exact ((continuous_const.mul (hθ.comp (contDiff_coneArgument T ε x₀ (k := 1)).continuous)).continuousOn).mul
    (((continuous_const.sub continuous_fst).continuousOn.mul
      (total_energy_continuous_slab hs)).add
        ((continuous_snd.sub continuous_const).continuousOn.inner
          (total_flux_continuous_slab hs hT)))

lemma coneShellFlux_integral_continuous {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    ContinuousOn (fun t => ∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ T)
    (coneShellFlux_continuous_slab hs hT x₀)
  intro t ht x hx
  exact coneShellFlux_zero_outside s hε ht hx

lemma cone_energy_continuous {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {ε : ℝ} (_hT : 0 ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    ContinuousOn (fun t => ∫ x : Vec, coneCutoff T ε x₀ (t,x)*totalEnergy s (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ T)
    ((contDiff_coneCutoff T ε x₀ (k := 1)).continuous.continuousOn.mul
      (total_energy_continuous_slab hs))
  intro t ht x hx
  change coneCutoff T ε x₀ (t,x)*totalEnergy s (t,x)=0
  simp only [coneCutoff_zero_outside hε ht hx,zero_mul]

lemma coneShellFlux_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    (∫ t in 0..b, ∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
  have hT := hb.trans hbT
  have hsub : Icc (0:ℝ) b ⊆ Icc 0 T := Icc_subset_Icc_right hbT
  have hc := (cone_energy_continuous hs hT hε x₀).mono hsub
  have hi := ((coneShellFlux_integral_continuous hs hT hε x₀).mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hc
    (fun t ht => deriv_cone_energy hs hε ⟨ht.1,ht.2.trans_le hbT⟩ x₀) hi.neg
  rw [intervalIntegral.integral_neg] at hf
  have hbpos : 0 ≤ ∫ x : Vec, coneCutoff T ε x₀ (b,x)*totalEnergy s (b,x) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (Real.smoothTransition.nonneg _) (total_energy_nonneg hs ⟨hb,hbT⟩ x)
  have hzero : (∫ x : Vec, coneCutoff T ε x₀ (0,x)*totalEnergy s (0,x)) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
    refine integral_mono ?_ (total_energy_integrable hs ⟨le_rfl,hT⟩) ?_
    · apply Continuous.integrable_of_hasCompactSupport
      · apply Continuous.mul ((contDiff_coneCutoff T ε x₀ (k := 1)).continuous.comp
          (continuous_const.prodMk continuous_id))
        apply (total_energy_continuous_slab hs).comp_continuous
          (continuous_const.prodMk continuous_id)
        intro x
        exact ⟨⟨le_rfl,hT⟩,mem_univ x⟩
      · apply HasCompactSupport.mul_right
        apply compactSupport_of_zero_off (isCompact_closedBall x₀ T)
        exact fun x hx => coneCutoff_zero_outside hε ⟨le_rfl,hT⟩ hx
    · intro x
      exact mul_le_of_le_one_left (total_energy_nonneg hs ⟨le_rfl,hT⟩ x)
        (Real.smoothTransition.le_one _)
  linarith

lemma continuous_radialConeProfile {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (R : ℝ) (x₀ : Vec) :
    Continuous (fun p : ℝ × Sphere => radialConeProfile s t R x₀ p.1 p.2) := by
  have hU : Continuous (fun x => totalEnergy s (t,x)) := by
    apply (total_energy_continuous_slab hs).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : Continuous (fun x => totalFlux s (t,x)) := by
    apply (total_flux_continuous_slab hs (ht.1.trans ht.2)).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hx : Continuous (fun p : ℝ × Sphere => x₀ + p.1 • p.2.1) := by fun_prop
  exact continuous_fst.mul ((continuous_const.mul (hU.comp hx)).add
    (continuous_fst.mul ((continuous_subtype_val.comp continuous_snd).inner (hS.comp hx))))

lemma continuous_spherical_radialConeProfile {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (R : ℝ) (x₀ : Vec) :
    Continuous (fun r => ∫ n : Sphere, radialConeProfile s t R x₀ r n ∂sphereMeasure) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    (continuous_radialConeProfile hs ht R x₀).continuousOn
  intro r n _ hn
  exact (hn (mem_univ n)).elim

lemma coneShellFlux_polar {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε t : ℝ} (ht : t ∈ Icc 0 T) (hε : 0 < ε) (x₀ : Vec) :
    (∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) =
      ∫ r in 0..(T-t), radialConeWeight (T-t) ε r *
        (∫ n : Sphere, radialConeProfile s t (T-t) x₀ r n ∂sphereMeasure) := by
  have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
  have hC : Continuous (fun x => coneShellFlux s T ε x₀ (t,x₀+x)) := by
    apply (coneShellFlux_continuous_slab hs (ht.1.trans ht.2) x₀).comp_continuous
      (continuous_const.prodMk (continuous_const.add continuous_id))
    intro x
    exact ⟨ht,mem_univ _⟩
  have hK : HasCompactSupport (fun x => coneShellFlux s T ε x₀ (t,x₀+x)) := by
    apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) T)
    intro x hx
    apply coneShellFlux_zero_outside s hε ht
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have htrans := integral_add_left_eq_self (μ := (volume : Measure Vec))
    (fun x => coneShellFlux s T ε x₀ (t,x)) x₀
  rw [← htrans,integral_polar (hC.integrable_of_hasCompactSupport hK)]
  simp_rw [coneShellFlux_polar_kernel,radialConeWeight_integral_Ioi hR hε]
  have hcont : Continuous (fun p : ℝ × Sphere =>
      radialConeWeight (T-t) ε p.1 * radialConeProfile s t (T-t) x₀ p.1 p.2) :=
    ((continuous_radialConeWeight (T-t) ε).comp continuous_fst).mul
      (continuous_radialConeProfile hs ht (T-t) x₀)
  have hi : Integrable (fun p : ℝ × Sphere => radialConeWeight (T-t) ε p.1 *
      radialConeProfile s t (T-t) x₀ p.1 p.2)
        ((volume.restrict (uIoc 0 (T-t))).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le hR,Measure.restrict_prod_eq_prod_univ]
    exact (hcont.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact integral_const_mul _ _

lemma coneShellFlux_tendsto {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (htT : t < T) (x₀ : Vec) :
    Filter.Tendsto (fun ε => ∫ x : Vec, coneShellFlux s T ε x₀ (t,x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure)) := by
  have hh := radialConeWeight_tendsto (sub_pos.mpr htT)
    (continuous_spherical_radialConeProfile hs ht (T-t) x₀).continuousOn
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (coneShellFlux_polar hs ht hε x₀).symm

lemma light_cone_flux {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    IntegrableOn (fun t => ∫ n : Sphere,
      radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure) (Ioo 0 T) ∧
    (∫ t in 0..T, ∫ n : Sphere,
      radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure) ≤
        ∫ x : Vec, totalEnergy s (0,x) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heps : Filter.Tendsto ε Filter.atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall hε⟩
  let G : ℕ → ℝ → ℝ := fun n t => ∫ x : Vec, coneShellFlux s T (ε n) x₀ (t,x)
  have hGi (n : ℕ) : Integrable (G n) (volume.restrict (Ioo 0 T)) := by
    exact ((coneShellFlux_integral_continuous hs hT (hε n) x₀).integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hGn (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioo 0 T), 0 ≤ G n t := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    apply integral_nonneg
    intro x
    exact coneShellFlux_nonneg hs (hε n) ⟨ht.1.le,ht.2.le⟩ x x₀
  have hconv : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      Filter.Tendsto (fun n => G n t) Filter.atTop
        (𝓝 (∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact (coneShellFlux_tendsto hs (Ioo_subset_Icc_self ht) ht.2 x₀).comp heps
  have hb (n : ℕ) : (∫ t in Ioo 0 T, G n t) ≤ ∫ x : Vec, totalEnergy s (0,x) := by
    rw [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hT]
    exact coneShellFlux_bound hs hT le_rfl (hε n) x₀
  obtain ⟨hi,hb⟩ := integral_limit_nonneg_le
    (integral_nonneg (total_energy_nonneg hs ⟨le_rfl,hT⟩)) hGi hGn hconv hb
  refine ⟨hi, ?_⟩
  rwa [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hT] at hb

open scoped Pointwise

lemma null_cone_flux {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    IntegrableOn (fun t => ∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) (Ioo 0 T) ∧
    (∫ t in 0..T, ∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
  simp_rw [nullConeFlux_spherical_eq]
  exact light_cone_flux hs hT x₀

lemma particle_cone_identity {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x n : Vec) :
    (∫ v : Vec, q v * (1-dot n (velocity v)) * s.f (t,x,v)) =
      particleEnergy s (t,x) - dot n (particleFlux s (t,x)) := by
  obtain ⟨hf,hc⟩ := velocity_slice hs ht x
  have hi : Integrable (fun v : Vec => s.f (t,x,v) • v) :=
    (hf.continuous.smul continuous_id).integrable_of_hasCompactSupport hc.smul_right
  have hqi : Integrable (fun v : Vec => q v * s.f (t,x,v)) :=
    ((contDiff_q (k := 1)).continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hni := (innerSL ℝ n).integrable_comp hi
  have hh := (innerSL ℝ n).integral_comp_comm hi
  simp only [innerSL_apply_apply] at hh hni
  simp only [particleEnergy,particleFlux,dot_eq_inner]
  rw [← hh,← integral_sub hqi hni]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  simp only [inner_smul_right,← dot_eq_inner]
  have hq : q v * dot n (velocity v) = dot n v := by
    simp only [dot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm,q_mul_velocity]
  rw [← hq]
  ring

lemma particle_cone_nonneg {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) {n : Vec} (hn : ‖n‖ = 1) :
    0 ≤ particleEnergy s (t,x) - dot n (particleFlux s (t,x)) := by
  have hh := dot_le_norm n (particleFlux s (t,x))
  rw [hn,one_mul] at hh
  linarith [particle_flux_bound hs ht x]

lemma goodConeDensity_bounds {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) {n : Vec} (hn : ‖n‖=1) :
    0 ≤ goodConeDensity s (t,x) n ∧
      goodConeDensity s (t,x) n ≤ 4*(totalEnergy s (t,x)-dot n (totalFlux s (t,x))) := by
  have hG := good_field_square_le_flux (s.E (t,x)) (s.B (t,x)) n hn
  have hP := particle_cone_nonneg hs ht x hn
  dsimp [goodConeDensity,totalEnergy,totalFlux]
  rw [dot_add_right]
  constructor
  · positivity
  · linarith

lemma goodConeDensity_continuousOn {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) :
    ContinuousOn (fun p : (ℝ × Vec) × Vec => goodConeDensity s p.1 p.2)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) := by
  have hE : ContinuousOn (fun p : (ℝ × Vec) × Vec => s.E p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    hs.E_smooth.continuousOn.comp continuous_fst.continuousOn (by
      intro p hp; exact hp.1)
  have hB : ContinuousOn (fun p : (ℝ × Vec) × Vec => s.B p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    hs.B_smooth.continuousOn.comp continuous_fst.continuousOn (by
      intro p hp; exact hp.1)
  have hF : ContinuousOn (fun p : (ℝ × Vec) × Vec => particleFlux s p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    (particle_flux_continuous_slab hs hT).comp
      continuous_fst.continuousOn (fun _ h => h.1)
  have hP : ContinuousOn (fun p : (ℝ × Vec) × Vec => particleEnergy s p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    (particle_energy_continuous_slab hs).comp
      continuous_fst.continuousOn (fun _ h => h.1)
  have hc := (contDiff_cross (k := 1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hB)
  simp only [goodConeDensity,dot_eq_inner]
  exact (((hE.add hc).norm.add (continuous_snd.continuousOn.inner hB).abs).pow 2).add
    (hP.sub (continuous_snd.continuousOn.inner hF))

lemma goodConeDensity_cone_continuous {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    ContinuousOn (fun p : ℝ × Sphere =>
      (T-p.1)^2 * goodConeDensity s (p.1,x₀-(T-p.1) • p.2.1) p.2.1) (Icc 0 T ×ˢ univ) := by
  have hn : Continuous (fun p : ℝ × Sphere => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hx : Continuous (fun p : ℝ × Sphere => x₀-(T-p.1) • p.2.1) :=
    continuous_const.sub ((continuous_const.sub continuous_fst).smul hn)
  have hmap : Continuous (fun p : ℝ × Sphere => ((p.1,x₀-(T-p.1) • p.2.1),p.2.1)) :=
    (continuous_fst.prodMk hx).prodMk hn
  have hg : ContinuousOn (fun p : ℝ × Sphere =>
      goodConeDensity s (p.1,x₀-(T-p.1) • p.2.1) p.2.1) (Icc 0 T ×ˢ univ) := by
    apply (goodConeDensity_continuousOn hs hT).comp hmap.continuousOn
    intro p hp
    exact ⟨⟨hp.1,mem_univ _⟩,mem_univ _⟩
  have hw : Continuous (fun p : ℝ × Sphere => (T-p.1)^2) :=
    (continuous_const.sub continuous_fst).pow 2
  convert! hw.continuousOn.mul hg using 1

lemma nullConeFlux_sphere_continuous {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (R : ℝ) (x₀ : Vec) :
    Continuous (fun n : Sphere => nullConeFlux s R x₀ t n) := by
  have hc : Continuous (fun n : Sphere => radialConeProfile s t (R-t) x₀ (R-t) n) :=
    (continuous_radialConeProfile hs ht (R-t) x₀).comp
      (continuous_const.prodMk continuous_id)
  convert! hc.comp continuous_neg using 1
  funext n
  simp only [Function.comp_apply,nullConeFlux,radialConeProfile,coe_neg_sphere,smul_neg,
    ← sub_eq_add_neg,dot_eq_inner,inner_neg_left]
  ring

lemma goodConeDensity_sphere_integral_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x₀ : Vec) :
    (∫ n : Sphere, (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure) ≤
      4*(∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) := by
  rw [← integral_const_mul]
  apply integral_mono
  · have hc := (goodConeDensity_cone_continuous hs (ht.1.trans ht.2) x₀).comp_continuous
      (continuous_const.prodMk continuous_id) (fun n => ⟨ht,mem_univ n⟩)
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  · exact integrableOn_univ.mp (((nullConeFlux_sphere_continuous hs ht T x₀).const_mul 4).continuousOn.integrableOn_compact isCompact_univ)
  · intro n
    have hn := (goodConeDensity_bounds hs ht (x₀-(T-t) • n.1) (sphere_norm n)).2
    dsimp [nullConeFlux]
    nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg (T-t))]

lemma goodConeDensity_time_integral_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    (∫ t in 0..T, ∫ n : Sphere,
      (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure) ≤
        4*(∫ x : Vec, totalEnergy s (0,x)) := by
  let F : ℝ → ℝ := fun t => ∫ n : Sphere,
    (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure
  have hFi : ContinuousOn F (Icc 0 T) := by
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
      (goodConeDensity_cone_continuous hs hT x₀)
    intro t n _ hn
    exact (hn (mem_univ n)).elim
  have hNi := (null_cone_flux hs hT x₀).1
  have hFint : IntegrableOn F (Ioo 0 T) :=
    (hFi.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hle : (∫ t in Ioo 0 T, F t) ≤
      ∫ t in Ioo 0 T, 4*(∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) := by
    apply integral_mono_ae hFint (hNi.const_mul 4)
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact goodConeDensity_sphere_integral_bound hs ⟨ht.1.le,ht.2.le⟩ x₀
  rw [integral_const_mul] at hle
  simp only [restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le hT] at hle
  have hbound := (null_cone_flux hs hT x₀).2
  exact le_trans hle (by linarith)

theorem good_cone_energy {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    (∫ t in 0..T, ∫ n : Sphere, (T-t)^2 *
      ((‖s.E (t,x₀-(T-t) • n.1)+cross n.1 (s.B (t,x₀-(T-t) • n.1))‖+
          |dot n.1 (s.B (t,x₀-(T-t) • n.1))|)^2 +
        ∫ v : Vec, q v*(1-dot n.1 (velocity v))*s.f (t,x₀-(T-t) • n.1,v))
          ∂sphereMeasure) ≤ 4*(∫ x : Vec, totalEnergy s (0,x)) := by
  convert! goodConeDensity_time_integral_bound hs hT x₀ using 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  apply integral_congr_ae
  apply ae_of_all
  intro n
  dsimp only
  rw [particle_cone_identity hs ht]
  rfl

end RVM.EnergyPrefix

end

end OAI
