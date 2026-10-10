import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.EnergyBump

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology NNReal

namespace RVM
abbrev Sphere := sphere (0 : Vec) 1
abbrev sphereMeasure : Measure Sphere := (volume : Measure Vec).toSphere

lemma integral_radial_measure {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) :
    (∫ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2) = ∫ r in Ioi (0 : ℝ), r^2 • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r => Real.toNNReal (r^2) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change (r^2).toNNReal • f r = r^2 • f r
    rw [NNReal.smul_def,Real.coe_toNNReal _ (sq_nonneg r)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma integrable_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Vec → W} (hf : Integrable f) :
    Integrable (fun p : Sphere × Ioi (0 : ℝ) => f (p.2.1 • p.1.1))
      (sphereMeasure.prod (Measure.volumeIoiPow 2)) := by
  have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
  simp only [Function.comp_def,Homeomorph.symm_apply_apply] at h
  have hi : Integrable (fun z : ({0}ᶜ : Set Vec) => f z.1) (volume.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have := h.mp hi
  simpa only [homeomorphUnitSphereProd_symm_apply_coe,finrank_euclideanSpace_fin,
    Nat.reduceSub] using this

lemma integral_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Vec → W} (hf : Integrable f) :
    (∫ y : Vec, f y) = ∫ n : Sphere, ∫ r in Ioi (0 : ℝ), r^2 • f (r • n.1) ∂volume ∂sphereMeasure := by
  calc
    _ = ∫ z : ({0}ᶜ : Set Vec), f z.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,restrict_compl_singleton]
    _ = ∫ p : Sphere × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
      simpa only [Homeomorph.symm_apply_apply,homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin,Nat.reduceSub] using h
    _ = ∫ n : Sphere, ∫ r : Ioi (0 : ℝ), f (r.1 • n.1) ∂Measure.volumeIoiPow 2
        ∂sphereMeasure := integral_prod _ (integrable_polar hf)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun n => integral_radial_measure (fun r => f (r • n.1)))
end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff

namespace RVM

lemma deriv_moving_energy {d : Datum} {s : Solution} (hs : Classical d s)
    {U : Set ℝ} (hU : IsOpen U) (hpos : U ⊆ Ioi 0)
    {g : ℝ × Vec → ℝ} {K : Set Vec} (hK : IsCompact K)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ (univ : Set Vec)))
    (hz : ∀ r ∈ U, ∀ x ∉ K, g (r,x)=0)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x))
      (∫ x : Vec, fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) +
        fderiv ℝ g (t,x) (0,totalFlux s (t,x))) t := by
  have hE := (classical_total_energy_regular hs).mono (prod_mono_left hpos)
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
    apply ContDiffOn.comp_contDiff ((classical_total_flux_regular hs).mono (prod_mono_left hpos))
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
    have hl := classical_local_energy_conservation hs (hpos ht) x
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
end RVM

end

end OAI
