import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ParticleBySpacetime

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma deriv_time_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : ℝ × Vec → W} {t : ℝ} {x : Vec} (hG : DifferentiableAt ℝ G (t,x)) :
    deriv (fun r => G (r,x)) t = fderiv ℝ G (t,x) (1,0) :=
  (hG.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

lemma spatialPartial_time_slice {G : ℝ × Vec → ℝ} {t : ℝ} {x : Vec}
    (hG : DifferentiableAt ℝ G (t,x)) (i : Fin 3) :
    spatialPartial (fun y => G (t,y)) x i = fderiv ℝ G (t,x) (0,basis i) := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

lemma classical_particleFlux_component {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 < t) (x : Vec) (i : Fin 3) :
    particleFlux s (t,x) i = ∫ v : Vec, v i * s.f (t,x,v) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    particle_spacetime_local_data x hs.1 hs.2.2.2.2.2.2.1 ht
  exact param_moment_component hK hp hF.continuousOn hzero i

lemma classical_particle_energy_local {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 < t) (x : Vec) :
    deriv (fun r => particleEnergy s (r,x)) t +
      divergence (fun y => particleFlux s (t,y)) x =
        dot (s.E (t,x)) (current (fun z => s.f (t,z)) x) := by
  obtain ⟨henergy,hflux⟩ := classical_particle_energy_flux_regular hs ht x
  rw [deriv_time_slice (henergy.differentiableAt (by simp))]
  apply Eq.trans _ (classical_particle_energy_balance hs ht x)
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hcomp : DifferentiableAt ℝ (fun p => particleFlux s p i) (t,x) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
      (hflux.differentiableAt (by simp))
  rw [spatialPartial_time_slice hcomp]
  have he : (fun p : ℝ × Vec => particleFlux s p i) =ᶠ[𝓝 (t,x)]
      (fun p => ∫ v : Vec, v i * s.f (p.1,p.2,v)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
    exact classical_particleFlux_component hs hp p.2 i
  rw [he.fderiv_eq (𝕜 := ℝ)]

lemma field_differentiableAt_positive {F : Field}
    (hF : ContDiffOn ℝ 1 F fieldHalfSpace) {t : ℝ} (ht : 0 < t) (x : Vec) :
    DifferentiableAt ℝ F (t,x) := by
  apply (hF.contDiffAt _).differentiableAt (by simp)
  apply Filter.mem_of_superset
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  intro z hz
  change 0 ≤ z.1
  exact le_of_lt hz

lemma divergence_add {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y+G y) x = divergence F x + divergence G x := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  have ha (i : Fin 3) := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (fderiv_add (hf i) (hg i))
  change ∀ i : Fin 3, fderiv ℝ (fun y => F y i + G y i) x (basis i) =
    fderiv ℝ (fun y => F y i) x (basis i) + fderiv ℝ (fun y => G y i) x (basis i) at ha
  simp only [divergence, PiLp.add_apply, spatialPartial, ha, Finset.sum_add_distrib]

lemma classical_local_energy_conservation {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 < t) (x : Vec) :
    deriv (fun r => totalEnergy s (r,x)) t +
      divergence (fun y => totalFlux s (t,y)) x = 0 := by
  have hE := field_differentiableAt_positive hs.2.1 ht x
  have hB := field_differentiableAt_positive hs.2.2.1 ht x
  obtain ⟨henergy,hflux⟩ := classical_particle_energy_flux_regular hs ht x
  have heq := hs.2.2.2.2.2.2.2.1 t ht.le
  have he := heq.2.1 x
  have hb := heq.2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he hb
  have hm := maxwell_energy_balance hE hB he hb
  have hp := classical_particle_energy_local hs ht x
  have heT : DifferentiableAt ℝ (fun r => s.E (r,x)) t :=
    hE.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hbT : DifferentiableAt ℝ (fun r => s.B (r,x)) t :=
    hB.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hfluxX : DifferentiableAt ℝ (fun y => particleFlux s (t,y)) x :=
    (hflux.differentiableAt (by simp)).comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hcrossX : DifferentiableAt ℝ (fun y => cross (s.E (t,y)) (s.B (t,y))) x :=
    (contDiff_cross (k := 1)).differentiable (by simp) _ |>.comp x
      ((hE.comp x ((differentiableAt_const t).prodMk differentiableAt_id)).prodMk
        (hB.comp x ((differentiableAt_const t).prodMk differentiableAt_id)))
  change deriv (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2 + particleEnergy s (r,x)) t +
    divergence (fun y => cross (s.E (t,y)) (s.B (t,y)) + particleFlux s (t,y)) x = 0
  have hpT : DifferentiableAt ℝ (fun r => particleEnergy s (r,x)) t :=
    DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := particleEnergy s)
      (henergy.differentiableAt (by simp))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hfT : DifferentiableAt ℝ (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2) t :=
    ((heT.norm_sq (𝕜 := ℝ)).add (hbT.norm_sq (𝕜 := ℝ))).div_const 2
  have hd := deriv_add hfT hpT
  change deriv (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2 + particleEnergy s (r,x)) t =
    deriv (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2) t +
      deriv (fun r => particleEnergy s (r,x)) t at hd
  rw [hd, divergence_add hcrossX hfluxX]
  linarith

lemma classical_velocity_slice {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => s.f (t,x,v)) ∧
      HasCompactSupport (fun v : Vec => s.f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hs.1.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ht)
  · obtain ⟨K,hK,hzero⟩ := hs.2.2.2.2.2.2.1 t ht
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hzero t ⟨ht,le_rfl⟩ (subset_tsupport _ hn),rfl⟩

lemma classical_particle_energy_nonneg {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.2.2.2.1 t ht (x,v))

lemma classical_particle_flux_bound {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ‖particleFlux s (t,x)‖ ≤ particleEnergy s (t,x) := by
  obtain ⟨hf,hc⟩ := classical_velocity_slice hs ht x
  have hi : Integrable (fun v : Vec => s.f (t,x,v) • v) :=
    (hf.continuous.smul continuous_id).integrable_of_hasCompactSupport hc.smul_right
  have hqi : Integrable (fun v : Vec => q v * s.f (t,x,v)) :=
    ((contDiff_q (k := 1)).continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  calc
    _ ≤ ∫ v : Vec, ‖s.f (t,x,v) • v‖ := norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono hi.norm hqi
      intro v
      have hp := hs.2.2.2.1 t ht (x,v)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
      nlinarith [norm_lt_q v]

lemma classical_total_energy_nonneg {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := classical_particle_energy_nonneg hs ht x
  positivity

lemma classical_total_flux_bound {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ‖totalFlux s (t,x)‖ ≤ totalEnergy s (t,x) := by
  exact (norm_add_le _ _).trans
    (add_le_add (poynting_norm_le_energy (s.E (t,x)) (s.B (t,x)))
      (classical_particle_flux_bound hs ht x))

lemma continuousOn_integral_uniform_support
    {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hK : IsCompact K) (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContinuousOn (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := continuousOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) continuousOn_const (g := fun x v => F (x,v))
    hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

lemma TimeContinuousL2.memLp {F : Field} (hF : TimeContinuousL2 F)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (fun x => F (t,x)) 2 volume := by
  obtain ⟨F₂,hc,heq⟩ := hF
  exact (Lp.memLp (F₂ t)).ae_eq (heq t ht)

lemma TimeContinuousL2.integrable_norm_sq {F : Field} (hF : TimeContinuousL2 F)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => ‖F (t,x)‖^2) := by
  have hm := hF.memLp ht
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma TimeContinuousL2.continuous_integral_norm_sq {F : Field} (hF : TimeContinuousL2 F) :
    ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Ici 0) := by
  obtain ⟨F₂,hc,heq⟩ := hF
  have hh : ∀ t ∈ Ici (0:ℝ), (∫ x : Vec, ‖F (t,x)‖^2) = ‖F₂ t‖^2 := by
    intro t ht
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq t ht] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  exact (hc.norm.pow 2).congr (fun t ht => hh t ht)

lemma classical_particle_energy_continuous_slab {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (particleEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hs.2.2.2.2.2.2.1 T hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, q v * s.f (p.1,p.2,v)) _
  apply continuousOn_integral_uniform_support (F := fun z : (ℝ × Vec) × Vec => q z.2 * s.f (z.1.1,z.1.2,z.2)) (hK.image continuous_snd)
  · apply ((contDiff_q (k := 1)).continuous.comp continuous_snd).continuousOn.mul
    apply hs.1.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
    intro z hz
    exact hz.1.1.1
  · intro p hp v hv
    have hf : s.f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hf,mul_zero]

lemma classical_particle_energy_compact {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x ∉ K, particleEnergy s (t,x) = 0 := by
  obtain ⟨K,hK,hzero⟩ := hs.2.2.2.2.2.2.1 T hT
  refine ⟨Prod.fst '' K,hK.image continuous_fst,?_⟩
  intro t ht x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  have hf : s.f (t,x,v) = 0 := by
    by_contra hn
    exact hx ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩
  simp only [hf,mul_zero, Pi.zero_apply]

lemma classical_particle_energy_integrable {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec => particleEnergy s (t,x)) := by
  obtain ⟨K,hK,hz⟩ := classical_particle_energy_compact hs ht
  have hc := (classical_particle_energy_continuous_slab hs ht).comp_continuous
    (continuous_const.prodMk continuous_id)
    (fun x : Vec => show (t,x) ∈ Icc 0 t ×ˢ (univ : Set Vec) from ⟨⟨ht,le_rfl⟩,mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))

lemma classical_total_energy_integrable {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec => totalEnergy s (t,x)) := by
  exact ((hs.2.2.2.2.1.integrable_norm_sq ht).add
    (hs.2.2.2.2.2.1.integrable_norm_sq ht)).div_const 2 |>.add
      (classical_particle_energy_integrable hs ht)

lemma classical_integrated_energy_continuous {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, totalEnergy s (t,x)) (Icc 0 T) := by
  obtain ⟨K,hK,hz⟩ := classical_particle_energy_compact hs hT
  have hp : ContinuousOn (fun t => ∫ x : Vec, particleEnergy s (t,x)) (Icc 0 T) :=
    continuousOn_integral_uniform_support hK
      (classical_particle_energy_continuous_slab hs hT) hz
  have he := hs.2.2.2.2.1.continuous_integral_norm_sq.mono (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hb := hs.2.2.2.2.2.1.continuous_integral_norm_sq.mono (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2+particleEnergy s (t,x)) =
    ((∫ x : Vec, ‖s.E (t,x)‖^2)+(∫ x : Vec, ‖s.B (t,x)‖^2))/2+
      (∫ x : Vec, particleEnergy s (t,x))
  calc
    _ = (∫ x : Vec, (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2)+
        (∫ x : Vec, particleEnergy s (t,x)) :=
      integral_add (((hs.2.2.2.2.1.integrable_norm_sq ht.1).add
        (hs.2.2.2.2.2.1.integrable_norm_sq ht.1)).div_const 2)
        (classical_particle_energy_integrable hs ht.1)
    _ = _ := by
      rw [integral_div, integral_add (hs.2.2.2.2.1.integrable_norm_sq ht.1)
        (hs.2.2.2.2.2.1.integrable_norm_sq ht.1)]

lemma classical_total_energy_regular {d : Datum} {s : Solution}
    (hs : Classical d s) : ContDiffOn ℝ 1 (totalEnergy s) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have hE := hs.2.1.mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun z hz => show 0 ≤ z.1 from le_of_lt hz.1)
  have hB := hs.2.2.1.mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun z hz => show 0 ≤ z.1 from le_of_lt hz.1)
  have hp : ContDiffOn ℝ 1 (particleEnergy s) (Ioi 0 ×ˢ (univ : Set Vec)) := by
    intro p hp
    exact (classical_particle_energy_flux_regular hs hp.1 p.2).1.contDiffWithinAt
  exact ((hE.norm_sq ℝ).add (hB.norm_sq ℝ)).div_const 2 |>.add hp

lemma classical_total_flux_regular {d : Datum} {s : Solution}
    (hs : Classical d s) : ContDiffOn ℝ 1 (totalFlux s) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have hE := hs.2.1.mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun z hz => show 0 ≤ z.1 from le_of_lt hz.1)
  have hB := hs.2.2.1.mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun z hz => show 0 ≤ z.1 from le_of_lt hz.1)
  have hp : ContDiffOn ℝ 1 (particleFlux s) (Ioi 0 ×ˢ (univ : Set Vec)) := by
    intro p hp
    exact (classical_particle_energy_flux_regular hs hp.1 p.2).2.contDiffWithinAt
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (hE.prodMk hB)
    (fun _ _ => mem_univ _)).add hp

lemma integral_mul_divergence {F : Vec → Vec} {g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    (∫ x, g x * divergence F x) = -(∫ x, fderiv ℝ g x (F x)) := by
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  have hI (i : Fin 3) : Integrable (fun x => g x * spatialPartial (fun y => F y i) x i) :=
    (hg.continuous.mul (((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport hc.mul_right
  have hJ (i : Fin 3) : Integrable (fun x => F x i * spatialPartial g x i) :=
    ((hFi i).continuous.mul ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis i)).mul_left
  simp only [divergence, Finset.mul_sum]
  conv_rhs => enter [1,2,x]; rw [clm_sum_basis]
  change (∫ x, ∑ i : Fin 3, g x * spatialPartial (fun y => F y i) x i) =
    -(∫ x, ∑ i : Fin 3, F x i * spatialPartial g x i)
  rw [integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i)]
  simp_rw [mul_comm (g _) (spatialPartial _ _ _)]
  have he (i : Fin 3) : (∫ x, spatialPartial (fun y => F y i) x i * g x) =
      -(∫ x, F x i * spatialPartial g x i) := by
    have hh := integral_mul_spatialPartial (hFi i) hg hc i
    linarith
  simp only [he, Finset.sum_neg_distrib]

lemma deriv_weighted_energy {d : Datum} {s : Solution}
    (hs : Classical d s) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x : Vec, g x * totalEnergy s (r,x))
      (∫ x : Vec, fderiv ℝ g x (totalFlux s (t,x))) t := by
  have hE := classical_total_energy_regular hs
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × Vec => g p.2 * totalEnergy s p)
      (Ioi 0 ×ˢ (univ : Set Vec)) := (hg.comp contDiff_snd).contDiffOn.mul hE
  have hz : ∀ r ∈ Ioi (0:ℝ), ∀ x ∉ tsupport g, g x * totalEnergy s (r,x) = 0 := by
    intro r _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support isOpen_Ioi hc ht hF hz
  have hi := fderiv_integral_uniform_support_apply isOpen_Ioi hc ht hF hz (1:ℝ)
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p : ℝ × Vec => g p.2 * totalEnergy s p) (t,x) (1,0) =
        -g x * divergence (fun y => totalFlux s (t,y)) x := by
    intro x
    have he := hE.contDiffAt (x := (t,x)) (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) ⟨ht,mem_univ x⟩)
    have heT : DifferentiableAt ℝ (fun r => totalEnergy s (r,x)) t :=
      DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := totalEnergy s)
        (he.differentiableAt (by simp))
        (differentiableAt_id.prodMk (differentiableAt_const x))
    have hgT : HasDerivAt (fun r => g x * totalEnergy s (r,x))
        (g x * deriv (fun r => totalEnergy s (r,x)) t) t :=
      heT.hasDerivAt.const_mul (g x)
    have hf := hF.contDiffAt (x := (t,x)) (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) ⟨ht,mem_univ x⟩)
    rw [← deriv_time_slice (hf.differentiableAt (by simp)), hgT.deriv]
    have hl := classical_local_energy_conservation hs ht x
    rw [show deriv (fun r => totalEnergy s (r,x)) t =
      -divergence (fun y => totalFlux s (t,y)) x by linarith]
    ring
  have hS : ContDiff ℝ 1 (fun x => totalFlux s (t,x)) := by
    apply contDiffOn_univ.mp
    exact (classical_total_flux_regular hs).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht,mem_univ x⟩)
  have hh : deriv (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t =
      ∫ x : Vec, fderiv ℝ g x (totalFlux s (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t 1 = _
    rw [hi]
    simp only [heq, neg_mul, integral_neg]
    rw [integral_mul_divergence hS hg hc, neg_neg]
  exact hh ▸ hd.differentiableAt.hasDerivAt

lemma classical_total_energy_continuous_slab {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (totalEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hsub : Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace := fun z hz => hz.1.1
  exact (((hs.2.1.continuousOn.mono hsub).norm.pow 2).add
    ((hs.2.2.1.continuousOn.mono hsub).norm.pow 2)).div_const 2 |>.add
      (classical_particle_energy_continuous_slab hs hT)

lemma classical_weighted_energy_continuous {d : Datum} {s : Solution}
    (hs : Classical d s) {g : Vec → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, g x * totalEnergy s (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support hc
    ((hg.comp continuous_snd).continuousOn.mul (classical_total_energy_continuous_slab hs hT))
  intro t _ x hx
  change g x * totalEnergy s (t,x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

lemma weighted_energy_deriv_bound {d : Datum} {s : Solution}
    (hs : Classical d s) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    {t : ℝ} (ht : 0 < t) :
    ‖deriv (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t‖ ≤
      C * (∫ x : Vec, totalEnergy s (t,x)) := by
  rw [(deriv_weighted_energy hs hg hc ht).deriv]
  have hS : Continuous (fun x : Vec => totalFlux s (t,x)) := by
    apply ContinuousOn.comp_continuous (classical_total_flux_regular hs).continuousOn
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hi : Integrable (fun x => fderiv ℝ g x (totalFlux s (t,x))) :=
    ((hg.continuous_fderiv (by simp)).clm_apply hS).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hc.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_apply]))
  calc
    _ ≤ ∫ x : Vec, ‖fderiv ℝ g x (totalFlux s (t,x))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Vec, C * totalEnergy s (t,x) := by
      apply integral_mono hi.norm ((classical_total_energy_integrable hs ht.le).const_mul C)
      intro x
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hb x) (classical_total_flux_bound hs ht.le x) (norm_nonneg _) hC)
    _ = _ := integral_const_mul _ _

lemma weighted_energy_increment_bound {d : Datum} {s : Solution}
    (hs : Classical d s) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {C B T : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hT : 0 ≤ T) (hB : ∀ t ∈ Icc 0 T, (∫ x : Vec, totalEnergy s (t,x)) ≤ B) :
    ‖(∫ x : Vec, g x * totalEnergy s (T,x)) - (∫ x : Vec, g x * totalEnergy s (0,x))‖ ≤ C * B * T := by
  rcases eq_or_lt_of_le hT with he | ht
  · subst T; simp
  let F : ℝ → ℝ := fun t => ∫ x : Vec, g x * totalEnergy s (t,x)
  have hcont : ContinuousOn F (Icc 0 T) := classical_weighted_energy_continuous hs hg.continuous hc hT
  have hdiff : DifferentiableOn ℝ F (Ioo 0 T) := fun t ht =>
    (deriv_weighted_energy hs hg hc ht.1).differentiableAt.differentiableWithinAt
  obtain ⟨c,hcT,heq⟩ := exists_deriv_eq_slope F ht hcont hdiff
  have hder : ‖deriv F c‖ ≤ C * B :=
    (weighted_energy_deriv_bound hs hg hc hC hb hcT.1).trans
      (mul_le_mul_of_nonneg_left (hB c ⟨hcT.1.le,hcT.2.le⟩) hC)
  rw [heq, sub_zero, norm_div, Real.norm_of_nonneg hT] at hder
  exact (div_le_iff₀ ht).mp hder

def energyBump : ContDiffBump (0 : Vec) := ⟨1,2,by norm_num,by norm_num⟩
def energyCutoff (n : ℕ) (x : Vec) : ℝ := energyBump (((n:ℝ)+1)⁻¹ • x)

lemma energyCutoff_smooth (n : ℕ) : ContDiff ℝ 1 (energyCutoff n) :=
  energyBump.contDiff.comp ((contDiff_const : ContDiff ℝ 1 (fun _ : Vec => ((n:ℝ)+1)⁻¹)).smul
    (contDiff_id : ContDiff ℝ 1 (fun x : Vec => x)))

lemma energyCutoff_compact (n : ℕ) : HasCompactSupport (energyCutoff n) := by
  apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) (2*((n:ℝ)+1)))
  intro x hx
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hnX : 2 * ((n:ℝ)+1) < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  have hnx : (((n:ℝ)+1)⁻¹ • x) ∉ Function.support energyBump := by
    rw [energyBump.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), energyBump]
    have hh : 2 < ((n:ℝ)+1)⁻¹ * ‖x‖ := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hn]
      exact hnX
    exact not_lt.mpr hh.le
  exact Function.notMem_support.mp hnx

lemma energyCutoff_bounds (n : ℕ) (x : Vec) : 0 ≤ energyCutoff n x ∧ energyCutoff n x ≤ 1 :=
  ⟨energyBump.nonneg,energyBump.le_one⟩

lemma energyCutoff_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ x : Vec, ‖fderiv ℝ (energyCutoff n) x‖ ≤ C / ((n:ℝ)+1) := by
  have hd : ContDiff ℝ 1 (energyBump : Vec → ℝ) := energyBump.contDiff
  obtain ⟨C,hC⟩ := (hd.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (energyBump.hasCompactSupport.fderiv ℝ)
  have hCp : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hCp,?_⟩
  intro n x
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hh := (hd.differentiable (by simp) (((n:ℝ)+1)⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (((n:ℝ)+1)⁻¹))
  have heq := hh.fderiv
  change fderiv ℝ (energyCutoff n) x = _ at heq
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ (energyBump : Vec → ℝ) (((n:ℝ)+1)⁻¹ • x)‖ *
        ‖((n:ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ Vec‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (energyBump : Vec → ℝ) (((n:ℝ)+1)⁻¹ • x)‖ * ((n:ℝ)+1)⁻¹ := by
      simp [norm_smul, abs_of_pos hn]
    _ ≤ C * ((n:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right (hC _) (inv_pos.mpr hn).le
    _ = _ := div_eq_mul_inv _ _ |>.symm

lemma energyCutoff_tendsto (x : Vec) : Filter.Tendsto (fun n => energyCutoff n x) Filter.atTop (𝓝 1) := by
  have hi : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) Filter.atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hzero : energyBump (0:Vec) = 1 := energyBump.one_of_mem_closedBall (by simp [energyBump])
  simpa only [energyCutoff, zero_smul,hzero,Function.comp_def] using! energyBump.continuous.continuousAt.tendsto.comp (hi.smul_const x)

lemma energyCutoff_integral_tendsto {F : Vec → ℝ} (hF : Integrable F) :
    Filter.Tendsto (fun n => ∫ x : Vec, energyCutoff n x * F x) Filter.atTop (𝓝 (∫ x : Vec, F x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
  · intro n
    exact (energyCutoff_smooth n).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · exact hF.norm
  · intro n
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (energyCutoff_bounds n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (energyCutoff_bounds n x).2
  · filter_upwards [] with x
    simpa only [one_mul] using (energyCutoff_tendsto x).mul_const (F x)

 theorem classical_energy_conservation {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x : Vec, totalEnergy s (T,x)) = ∫ x : Vec, totalEnergy s (0,x) := by
  obtain ⟨C,hC,hb⟩ := energyCutoff_deriv_bound
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).bddAbove_image
    (classical_integrated_energy_continuous hs hT)
  have hB' : ∀ t ∈ Icc 0 T, (∫ x : Vec, totalEnergy s (t,x)) ≤ B :=
    fun t ht => hB ⟨t,ht,rfl⟩
  have hinc (n : ℕ) :
      ‖(∫ x : Vec, energyCutoff n x * totalEnergy s (T,x)) -
        (∫ x : Vec, energyCutoff n x * totalEnergy s (0,x))‖ ≤
          (C / ((n:ℝ)+1)) * B * T :=
    weighted_energy_increment_bound hs (energyCutoff_smooth n) (energyCutoff_compact n)
      (div_nonneg hC (by positivity)) (hb n) hT hB'
  have hl := ((energyCutoff_integral_tendsto (classical_total_energy_integrable hs hT)).sub
    (energyCutoff_integral_tendsto (classical_total_energy_integrable hs (show (0:ℝ) ≤ 0 from le_rfl)))).norm
  have hr : Filter.Tendsto (fun n : ℕ => (C / ((n:ℝ)+1)) * B * T) Filter.atTop (𝓝 0) := by
    have hi : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_mul] using ((hi.const_mul C).mul_const B).mul_const T
  have he := le_of_tendsto_of_tendsto' hl hr hinc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma scalar_gronwall_interior {f : ℝ → ℝ} {K ε T : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hc : ContinuousOn f (Icc 0 T)) (h0 : f 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo 0 T, deriv f t ≤ K*f t+ε) :
    f T ≤ ε*T*Real.exp (K*T) := by
  rcases eq_or_lt_of_le hT with he | ht
  · subst T; simp [h0]
  let g : ℝ → ℝ := fun t => f t * Real.exp (-K*t)
  have hgc : ContinuousOn g (Icc 0 T) := hc.mul (by fun_prop)
  have hgd (t : ℝ) (htt : t ∈ Ioo 0 T) :
      HasDerivAt g ((deriv f t-K*f t)*Real.exp (-K*t)) t := by
    convert (hd t htt).hasDerivAt.mul (((hasDerivAt_id t).const_mul (-K)).exp) using 1 <;> try rfl
    simp only [id_eq]
    ring
  obtain ⟨c,hc',heq⟩ := exists_deriv_eq_slope g ht hgc
    (fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt)
  have he' : Real.exp (-K*c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hc'.1])
  have hg' : deriv g c ≤ ε := by
    rw [(hgd c hc').deriv]
    calc
      _ ≤ ε*Real.exp (-K*c) := mul_le_mul_of_nonneg_right (by linarith [hb c hc']) (Real.exp_pos _).le
      _ ≤ ε := mul_le_of_le_one_right hε he'
  rw [heq,sub_zero,show g 0=0 by simp [g,h0],sub_zero] at hg'
  have hlast := (div_le_iff₀ ht).mp hg'
  have hx := mul_le_mul_of_nonneg_right hlast (Real.exp_pos (K*T)).le
  simpa only [g,mul_assoc,← Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero,mul_one] using hx

lemma weighted_density_hasDerivAt
    {e : ℝ × Vec → ℝ} {g : Vec → ℝ} {t : ℝ}
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x : Vec, g x*e (r,x))
      (∫ x : Vec, g x*fderiv ℝ e (t,x) (1,0)) t := by
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × Vec => g p.2*e p)
      (Ioi 0 ×ˢ (univ : Set Vec)) := (hg.comp contDiff_snd).contDiffOn.mul he
  have hz : ∀ r ∈ Ioi (0:ℝ), ∀ x ∉ tsupport g, g x*e (r,x)=0 := by
    intro r _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hi := fderiv_integral_uniform_support_apply isOpen_Ioi hc ht hF hz (1:ℝ)
  have hd := hasFDerivAt_integral_uniform_support isOpen_Ioi hc ht hF hz
  have heq (x : Vec) : fderiv ℝ (fun p : ℝ × Vec => g p.2*e p) (t,x) (1,0) =
      g x*fderiv ℝ e (t,x) (1,0) := by
    have he' := he.contDiffAt (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    have heT : DifferentiableAt ℝ (fun r => e (r,x)) t :=
      DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := e)
        (he'.differentiableAt (by simp))
        (differentiableAt_id.prodMk (differentiableAt_const x))
    have hgT := heT.hasDerivAt.const_mul (g x)
    have hf := hF.contDiffAt (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    rw [← deriv_time_slice (hf.differentiableAt (by simp)), hgT.deriv,
      deriv_time_slice (he'.differentiableAt (by simp))]
  have hid : deriv (fun r => ∫ x : Vec, g x*e (r,x)) t =
      ∫ x : Vec, g x*fderiv ℝ e (t,x) (1,0) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g x*e (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
  exact hid ▸ hd.differentiableAt.hasDerivAt

lemma continuous_divergence {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  unfold divergence spatialPartial
  apply continuous_finsetSum
  intro i _
  have hi : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

lemma weighted_density_deriv_le
    {e : ℝ × Vec → ℝ} {F : ℝ × Vec → Vec} {g : Vec → ℝ} {t K C : ℝ}
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hF : ContDiffOn ℝ 1 F (Ioi 0 ×ˢ (univ : Set Vec)))
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ht : 0 < t)
    (hg0 : ∀ x, 0 ≤ g x) (hC : 0 ≤ C) (hgb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (heI : Integrable (fun x : Vec => e (t,x)))
    (hflux : ∀ x : Vec, ‖F (t,x)‖ ≤ e (t,x))
    (hineq : ∀ x : Vec, fderiv ℝ e (t,x) (1,0) + divergence (fun y => F (t,y)) x ≤ K*e (t,x)) :
    deriv (fun r => ∫ x : Vec, g x*e (r,x)) t ≤
      K*(∫ x : Vec, g x*e (t,x))+C*(∫ x : Vec, e (t,x)) := by
  have hes : Continuous (fun x : Vec => e (t,x)) := he.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)
  have hfs : ContDiff ℝ 1 (fun x : Vec => F (t,x)) := by
    apply contDiffOn_univ.mp
    exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht,mem_univ _⟩)
  have hedc : Continuous (fun x : Vec => fderiv ℝ e (t,x) (1,0)) :=
    ((he.continuousOn_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)).clm_apply continuous_const
  have hi₁ : Integrable (fun x : Vec => g x*fderiv ℝ e (t,x) (1,0)) :=
    (hg.continuous.mul hedc).integrable_of_hasCompactSupport hc.mul_right
  have hi₂ : Integrable (fun x : Vec => g x*e (t,x)) :=
    (hg.continuous.mul hes).integrable_of_hasCompactSupport hc.mul_right
  have hi₃ : Integrable (fun x : Vec => g x*divergence (fun y => F (t,y)) x) :=
    (hg.continuous.mul (continuous_divergence hfs)).integrable_of_hasCompactSupport hc.mul_right
  have hi₄ : Integrable (fun x : Vec => fderiv ℝ g x (F (t,x))) :=
    ((hg.continuous_fderiv (by simp)).clm_apply hfs.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hc.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_apply]))
  rw [(weighted_density_hasDerivAt he hg hc ht).deriv]
  calc
    _ ≤ ∫ x : Vec, K*(g x*e (t,x))-g x*divergence (fun y => F (t,y)) x := by
      apply integral_mono hi₁ ((hi₂.const_mul K).sub hi₃)
      intro x
      change g x * fderiv ℝ e (t,x) (1,0) ≤ K*(g x*e (t,x))-g x*divergence (fun y => F (t,y)) x
      nlinarith [mul_le_mul_of_nonneg_left (hineq x) (hg0 x)]
    _ = K*(∫ x : Vec, g x*e (t,x))+(∫ x : Vec, fderiv ℝ g x (F (t,x))) := by
      rw [integral_sub (hi₂.const_mul K) hi₃, integral_const_mul, integral_mul_divergence hfs hg hc]
      ring
    _ ≤ _ := by
      apply add_le_add_right
      calc
        _ ≤ ∫ x : Vec, C*e (t,x) := by
          apply integral_mono hi₄ (heI.const_mul C)
          intro x
          exact (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hgb x) (hflux x) (norm_nonneg _) hC))
        _ = _ := integral_const_mul _ _

theorem local_energy_inequality_vanishes
    {e : ℝ × Vec → ℝ} {F : ℝ × Vec → Vec} {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hF : ContDiffOn ℝ 1 F (Ioi 0 ×ˢ (univ : Set Vec)))
    (hec : ContinuousOn e (Icc 0 T ×ˢ (univ : Set Vec)))
    (he0 : ∀ t ∈ Icc 0 T, ∀ x : Vec, 0 ≤ e (t,x))
    (heI : ∀ t ∈ Icc 0 T, Integrable (fun x : Vec => e (t,x)))
    (hcont : ContinuousOn (fun t => ∫ x : Vec, e (t,x)) (Icc 0 T))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x : Vec, ‖F (t,x)‖ ≤ e (t,x))
    (hineq : ∀ t ∈ Ioo 0 T, ∀ x : Vec,
      fderiv ℝ e (t,x) (1,0)+divergence (fun y => F (t,y)) x ≤ K*e (t,x))
    (hinit : ∀ x : Vec, e (0,x)=0) :
    ∀ x : Vec, e (T,x)=0 := by
  obtain ⟨C,hC,hCb⟩ := energyCutoff_deriv_bound
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).bddAbove_image hcont
  have hB' : ∀ t ∈ Icc 0 T, (∫ x : Vec, e (t,x)) ≤ B := fun t ht => hB ⟨t,ht,rfl⟩
  have hBn : 0 ≤ B := by
    have ht0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl,hT⟩
    exact (integral_nonneg (he0 0 ht0)).trans (hB' 0 ht0)
  have hbound (n : ℕ) : (∫ x : Vec, energyCutoff n x*e (T,x)) ≤
      ((C/((n:ℝ)+1))*B)*T*Real.exp (K*T) := by
    let f : ℝ → ℝ := fun t => ∫ x : Vec, energyCutoff n x*e (t,x)
    have hfc : ContinuousOn f (Icc 0 T) := by
      apply continuousOn_integral_uniform_support (energyCutoff_compact n)
        (((energyCutoff_smooth n).continuous.comp continuous_snd).continuousOn.mul hec)
      intro t _ x hx
      change energyCutoff n x * e (t,x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    apply scalar_gronwall_interior hK (mul_nonneg (div_nonneg hC (by positivity)) hBn) hT hfc
    · simp only [f,hinit,mul_zero,integral_zero]
    · intro t ht
      exact (weighted_density_hasDerivAt he (energyCutoff_smooth n) (energyCutoff_compact n) ht.1).differentiableAt
    · intro t ht
      have hder := weighted_density_deriv_le he hF (energyCutoff_smooth n)
        (energyCutoff_compact n) ht.1 (fun x => (energyCutoff_bounds n x).1)
        (div_nonneg hC (by positivity)) (hCb n) (heI t ⟨ht.1.le,ht.2.le⟩)
        (hflux t ht) (hineq t ht)
      exact hder.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (hB' t ⟨ht.1.le,ht.2.le⟩) (div_nonneg hC (by positivity))) _)
  have hl := energyCutoff_integral_tendsto (heI T ⟨hT,le_rfl⟩)
  have hr : Tendsto (fun n : ℕ => ((C/((n:ℝ)+1))*B)*T*Real.exp (K*T)) atTop (nhds 0) := by
    have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_mul] using (((hi.const_mul C).mul_const B).mul_const T).mul_const (Real.exp (K*T))
  have hz : (∫ x : Vec, e (T,x))=0 := le_antisymm
    (le_of_tendsto_of_tendsto' hl hr hbound) (integral_nonneg (he0 T ⟨hT,le_rfl⟩))
  have hae := (integral_eq_zero_iff_of_nonneg (he0 T ⟨hT,le_rfl⟩) (heI T ⟨hT,le_rfl⟩)).mp hz
  have hes : Continuous (fun x : Vec => e (T,x)) := hec.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨⟨hT,le_rfl⟩,mem_univ _⟩)
  exact fun x => congrFun (Measure.eq_of_ae_eq (μ := volume) hae hes continuous_const) x

def RegularParticle (f : Particle) : Prop :=
  ContDiffOn ℝ 1 f particleHalfSpace ∧
    CompactOnFiniteHorizons ⟨f,0,0⟩

lemma Classical.regularParticle {d : Datum} {s : Solution} (hs : Classical d s) :
    RegularParticle s.f := ⟨hs.1,hs.2.2.2.2.2.2.1⟩

lemma RegularParticle.local_data {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime f (p,v) = 0 :=
  particle_spacetime_local_data (s := ⟨f,0,0⟩) x hf.1 hf.2 ht

lemma RegularParticle.slice {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => f (t,x,v)) ∧ HasCompactSupport (fun v : Vec => f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hf.1.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ht)
  · obtain ⟨K,hK,hz⟩ := hf.2 t ht
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hz t ⟨ht,le_rfl⟩ (subset_tsupport _ hn),rfl⟩

def particleMoment {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Particle) (w : Vec → W) (p : ℝ × Vec) : W :=
  ∫ v : Vec, f (p.1,p.2,v) • w v

lemma RegularParticle.moment_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    Integrable (fun v : Vec => f (t,x,v) • w v) := by
  obtain ⟨hs,hc⟩ := hf.slice ht x
  exact (hs.continuous.smul hw).integrable_of_hasCompactSupport hc.smul_right

lemma RegularParticle.moment_regular {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {f : Particle} (hf : RegularParticle f)
    {w : Vec → W} (hw : ContDiff ℝ 1 w) :
    ContDiffOn ℝ 1 (particleMoment f w) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  intro p hp
  obtain ⟨U,K,hU,hK,hp',hF,hzero⟩ := hf.local_data hp.1 p.2
  have hs := contDiffOn_integral_uniform_support (n := 1) hU hK
    (hF.smul (hw.comp contDiff_snd).contDiffOn)
    (fun p hp v hv => by
      change particleBySpacetime f (p,v) • w v = 0
      rw [hzero p hp v hv,zero_smul])
  exact (hs.contDiffAt (hU.mem_nhds hp')).contDiffWithinAt

lemma RegularParticle.moment_continuous_slab {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (particleMoment f w) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, f (p.1,p.2,v) • w v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => f (z.1.1,z.1.2,z.2) • w z.2) (hK.image continuous_snd)
  · apply ContinuousOn.smul ?_ (hw.comp continuous_snd).continuousOn
    exact hf.1.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      (fun z hz => hz.1.1.1)
  · intro p hp v hv
    have hz : f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hz,zero_smul]

lemma RegularParticle.moment_compact {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Particle} (hf : RegularParticle f) (w : Vec → W) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x ∉ K, particleMoment f w (t,x) = 0 := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  refine ⟨Prod.fst '' K,hK.image continuous_fst,?_⟩
  intro t ht x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  have hz : f (t,x,v) = 0 := by
    by_contra hn
    exact hx ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩
  simp only [hz,zero_smul,Pi.zero_apply]

lemma RegularParticle.spatial_moment_integrable {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x : Vec => particleMoment f w (t,x)) := by
  obtain ⟨K,hK,hz⟩ := hf.moment_compact w ht
  have hc := (hf.moment_continuous_slab hw ht).comp_continuous
    (continuous_const.prodMk continuous_id)
    (fun x : Vec => show (t,x) ∈ Icc 0 t ×ˢ (univ : Set Vec) from ⟨⟨ht,le_rfl⟩,mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))

lemma RegularParticle.integrated_moment_continuous {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, particleMoment f w (t,x)) (Icc 0 T) := by
  obtain ⟨K,hK,hz⟩ := hf.moment_compact w hT
  exact continuousOn_integral_uniform_support hK (hf.moment_continuous_slab hw hT) hz

lemma RegularParticle.velocity_flux_bound {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) (hpos : ∀ v, 0 ≤ f (t,x,v)) :
    ‖particleMoment f velocity (t,x)‖ ≤ particleMoment f (fun _ => (1:ℝ)) (t,x) := by
  dsimp [particleMoment]
  simp only [mul_one]
  calc
    _ ≤ ∫ v : Vec, ‖f (t,x,v) • velocity v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : Vec, f (t,x,v) := by
      have hi := hf.moment_integrable (contDiff_velocity (k := 1)).continuous ht x
      have hfI : Integrable (fun v : Vec => f (t,x,v)) :=
        (hf.slice ht x).1.continuous.integrable_of_hasCompactSupport (hf.slice ht x).2
      apply integral_mono hi.norm hfI
      intro v
      change ‖f (t,x,v) • velocity v‖ ≤ f (t,x,v)
      rw [norm_smul,Real.norm_of_nonneg (hpos v)]
      exact mul_le_of_le_one_right (hpos v) (norm_velocity_lt_one v).le

lemma TimeContinuousL2.sub {E F : Field} (hE : TimeContinuousL2 E) (hF : TimeContinuousL2 F) :
    TimeContinuousL2 (E-F) := by
  obtain ⟨E₂,hEc,hEe⟩ := hE
  obtain ⟨F₂,hFc,hFe⟩ := hF
  refine ⟨E₂-F₂,hEc.sub hFc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_sub (E₂ t) (F₂ t),hEe t ht,hFe t ht] with x hsub he hf
  exact hsub.trans (by simp only [he,hf,Pi.sub_apply])

lemma uniqueDiffOn_particleHalfSpace : UniqueDiffOn ℝ particleHalfSpace := by
  have he : particleHalfSpace = Ici (0:ℝ) ×ˢ (univ : Set Phase) := by
    ext p; simp [particleHalfSpace]
  rw [he]
  exact (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

lemma RegularParticle.velocity_derivative_bound {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Ioo 0 T, ∀ x v : Vec,
      ‖fderiv ℝ (fun w => f (t,x,w)) v‖ ≤ L := by
  obtain ⟨K,hK,hz⟩ := hf.2 T hT
  have hfullc := (hf.1.continuousOn_fderivWithin uniqueDiffOn_particleHalfSpace le_rfl).norm
  have hsub : Icc 0 T ×ˢ K ⊆ particleHalfSpace := fun p hp => hp.1.1
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod hK).bddAbove_image
    (hfullc.mono hsub)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro t ht x v
  by_cases hmem : (x,v) ∈ K
  · have hd := particle_differentiableAt_positive (s := ⟨f,0,0⟩) hf.1 ht.1 x v
    have hnhds : particleHalfSpace ∈ nhds (t,x,v) :=
      mem_of_superset ((isOpen_Ioi.preimage (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht.1)
        (fun p hp => show p.1 ≥ 0 from le_of_lt hp)
    have hb : ‖fderiv ℝ f (t,x,v)‖ ≤ max 0 B := by
      rw [← fderivWithin_of_mem_nhds hnhds]
      exact (hB ⟨(t,x,v),⟨⟨ht.1.le,ht.2.le⟩,hmem⟩,rfl⟩).trans (le_max_right _ _)
    have hinj : HasFDerivAt (fun w : Vec => (t,x,w))
        ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
      fun_prop
    have hs := hd.hasFDerivAt.comp v hinj
    apply ContinuousLinearMap.opNorm_le_bound _ (le_max_left 0 B)
    intro w
    have he : fderiv ℝ (fun w => f (t,x,w)) v w = fderiv ℝ f (t,x,v) (0,0,w) := by
      exact congrArg (fun A : Vec →L[ℝ] ℝ => A w) hs.fderiv
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ f (t,x,v)‖ * ‖((0,0,w) : ℝ × Phase)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg w)
  · have hzero : (fun w : Vec => f (t,x,w)) =ᶠ[nhds v] (fun _ => 0) := by
      have hn := (hK.isClosed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem
      filter_upwards [hn] with w hw
      by_contra hne
      exact hw (hz t ⟨ht.1.le,ht.2.le⟩ (subset_tsupport _ hne))
    rw [hzero.fderiv_eq (𝕜 := ℝ)]
    simp

lemma integral_lorentz_derivative_zero {g : Vec → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (E B : Vec) :
    (∫ v : Vec, fderiv ℝ g v (E + cross (velocity v) B)) = 0 := by
  have h := integral_mul_divergence (contDiff_lorentz E B) hg hc
  simp only [divergence_lorentz,mul_zero,integral_zero] at h
  linarith

lemma particle_number_balance_param
    {U : Set (ℝ × Vec)} {K : Set Vec} {F : (ℝ × Vec) × Vec → ℝ}
    {p : ℝ × Vec} (E B : Vec)
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    fderiv ℝ (fun y => ∫ v : Vec, F (y,v)) p (1,0) +
      ∑ i : Fin 3, fderiv ℝ (fun y => ∫ v : Vec, velocity v i * F (y,v)) p (0,basis i) =
      ∫ v : Vec, fderiv ℝ F (p,v) ((1,velocity v), E + cross (velocity v) B) := by
  have hdiff (v : Vec) : DifferentiableAt ℝ F (p,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt (by simp)
  have hs : ContDiff ℝ 1 (fun v : Vec => F (p,v)) := by
    apply contDiffOn_univ.mp
    exact hF.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
      (fun v _ => ⟨hp,mem_univ v⟩)
  have hc : HasCompactSupport (fun v : Vec => F (p,v)) :=
    compactSupport_of_zero_off hK (hzero p hp)
  have hvel (i : Fin 3) : ContDiff ℝ 1 (fun v => velocity v i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity
  have hint : Integrable (fun v : Vec => fderiv ℝ F (p,v) ((1,0),0)) := by
    simpa only [one_mul] using integrable_param_fderiv_apply_weight hU hK hp hF
      (continuous_const (y := (1:ℝ))) hzero (((1:ℝ),(0:Vec)),(0:Vec))
  have hint' (i : Fin 3) := integrable_param_fderiv_apply_weight hU hK hp hF
    (hvel i).continuous hzero (((0:ℝ),basis i),(0:Vec))
  have hintK : Integrable (fun v : Vec => fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) := by
    have hd : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
      (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ => ⟨hp,mem_univ _⟩)
    apply (hd.clm_apply (continuous_const.prodMk (contDiff_lorentz (k := 1) E B).continuous)).integrable_of_hasCompactSupport
    apply compactSupport_of_zero_off (compactSupport_param_fderiv hU hK hp hzero)
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport hv,zero_apply]
  have hK0 : (∫ v : Vec, fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) = 0 := by
    simpa only [fderiv_velocity_slice (hdiff _)] using integral_lorentz_derivative_zero hs hc E B
  have he (v : Vec) : fderiv ℝ F (p,v) ((1,velocity v),E + cross (velocity v) B) =
      fderiv ℝ F (p,v) ((1,0),0) +
        (∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
        fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) := by
    rw [clm_spacetime_velocity_split]
    congr 1
    symm
    have h := clm_spacetime_velocity_split (fderiv ℝ F (p,v)) (0:Vec) (E + cross (velocity v) B)
    have h' : fderiv ℝ F (p,v) ((1,0),E + cross (velocity v) B) =
        fderiv ℝ F (p,v) ((1,0),0) + fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) := by
      rw [← map_add]; congr 1; ext <;> simp
    simp only [PiLp.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] at h
    linarith
  rw [fderiv_integral_uniform_support_apply hU hK hp hF hzero]
  simp_rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF (hvel _) hzero]
  rw [← integral_finsetSum _ (fun i _ => hint' i), ← integral_add hint
    (integrable_finsetSum Finset.univ (fun i _ => hint' i))]
  calc
    _ = (∫ v : Vec, fderiv ℝ F (p,v) ((1,0),0) +
      ∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
       (∫ v : Vec, fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) := by rw [hK0,add_zero]
    _ = _ := by
      calc
        _ = ∫ v : Vec, (fderiv ℝ F (p,v) ((1,0),0) +
          ∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
            fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) :=
          (integral_add (hint.add (integrable_finsetSum Finset.univ (fun i _ => hint' i))) hintK).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with v
          exact (he v).symm

lemma fderiv_square_half {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → ℝ} {p b : H} (hg : DifferentiableAt ℝ g p) :
    fderiv ℝ (fun z => (g z)^2/2) p b = g p * fderiv ℝ g p b := by
  have h := (hg.hasFDerivAt.pow 2).mul_const (2:ℝ)⁻¹
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp only [smul_apply,smul_eq_mul]
  norm_num
  ring

def squareDifference (s₁ s₂ : Solution) : Particle :=
  fun z => (s₁.f z-s₂.f z)^2/2

lemma squareDifference_nonneg (s₁ s₂ : Solution) (z : ℝ × Phase) :
    0 ≤ squareDifference s₁ s₂ z := div_nonneg (sq_nonneg _) (by norm_num)

lemma squareDifference_zero_iff (s₁ s₂ : Solution) (z : ℝ × Phase) :
    squareDifference s₁ s₂ z = 0 ↔ s₁.f z=s₂.f z := by
  simp [squareDifference,sub_eq_zero]

lemma particle_difference_direction {d : Datum} {s₁ s₂ : Solution}
    (hs₁ : Classical d s₁) (hs₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hd₁ := particle_differentiableAt_positive hs₁.1 ht x v
  have hd₂ := particle_differentiableAt_positive hs₂.1 ht x v
  have hsp₁ : DifferentiableAt ℝ (particleBySpacetime s₁.f) ((t,x),v) :=
    (hd₁.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have hsp₂ : DifferentiableAt ℝ (particleBySpacetime s₂.f) ((t,x),v) :=
    (hd₂.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have he₁ := particle_spacetime_vlasov hs₁.1 hs₁.2.2.2.2.2.2.2.1 ht x v
  have he₂ := particle_spacetime_vlasov hs₂.1 hs₂.2.2.2.2.2.2.2.1 ht x v
  change fderiv ℝ (fun z => ((particleBySpacetime s₁.f-particleBySpacetime s₂.f) z)^2/2)
     ((t,x),v) _ = _
  rw [fderiv_square_half (hsp₁.sub hsp₂), fderiv_sub hsp₁ hsp₂]
  simp only [sub_apply,Pi.sub_apply,he₁,zero_sub]
  have hcross : cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)) =
      cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [hcross]
  have hh : (((1:ℝ),velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      ((1,velocity v),s₂.E (t,x)+cross (velocity v) (s₂.B (t,x))) +
        ((0,0),(s₁.E (t,x)-s₂.E (t,x))+(cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)))) := by
    apply Prod.ext
    · simp
    · dsimp
      abel
  rw [hh,map_add,he₂,zero_add]
  have hv := fderiv_velocity_slice hsp₂
  change ∀ b, fderiv ℝ (fun v => s₂.f (t,x,v)) v b =
    fderiv ℝ (particleBySpacetime s₂.f) ((t,x),v) ((0,0),b) at hv
  rw [← hv]
  simp only [particleBySpacetime]
  ring

end RVM

end

end OAI
