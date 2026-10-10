import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SphericalFluxNorm

namespace OAI

noncomputable section

section
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

lemma sourceWave_spatial_ibp {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    sourceWave (dirD ρ (0,basis i)) (t,x) = (4*Real.pi)⁻¹ *
      ((∫ z in ball (0:Vec) t,
        z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) + z i/‖z‖^3*ρ (t-‖z‖,x+z)) +
      ∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure) := by
  rw [sourceWave_ball (contDiff_dirD hρ _).continuous ht.le x,conePotential_spatial_ibp hρ ht]

lemma electricPotentialComponent_ball {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricPotentialComponent ρ j i (t,x) =
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t,
        -(z i/‖z‖^3*ρ (t-‖z‖,x+z)) - z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) -
          dirD (fun p => j p i) (1,0) (t-‖z‖,x+z)/‖z‖) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure) -
      waveK (fun y => j (0,y) i) (t,x) := by
  rw [electricPotentialComponent_source hρ hj,sourceWave_spatial_ibp hρ ht,
    sourceWave_ball (contDiff_dirD (contDiff_component hj i) _).continuous ht.le x]
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have h₁ : IntegrableOn (fun z : Vec => z i/‖z‖^3*ρ (t-‖z‖,x+z)) (ball (0:Vec) t) :=
    integrableOn_ball_direction_div_norm_pow (hρ.continuous.comp harg) 2 (by norm_num) t i
  have h₂ : IntegrableOn (fun z : Vec => z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z)) (ball (0:Vec) t) :=
    integrableOn_ball_direction_div_norm_pow ((contDiff_dirD hρ _).continuous.comp harg) 1 (by norm_num) t i
  have h₃ := integrable_conePotential (contDiff_dirD (contDiff_component hj i) (1,0)).continuous ht.le x
  have hneg : IntegrableOn (fun z : Vec => -(z i/‖z‖^3*ρ (t-‖z‖,x+z))) (ball (0:Vec) t) := h₁.neg
  rw [integral_add h₂ h₁,integral_sub (Integrable.sub' hneg h₂) h₃,
    integral_sub hneg h₂,integral_neg]
  ring

lemma magneticPotentialComponent_ball {j : Field} (hj : ContDiff ℝ ∞ j)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticPotentialComponent j i (t,x) =
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t,
        z (curlA i)/‖z‖^2*dirD (fun p => j p (curlB i)) (1,0) (t-‖z‖,x+z) +
        z (curlA i)/‖z‖^3*j (t-‖z‖,x+z) (curlB i) -
        (z (curlB i)/‖z‖^2*dirD (fun p => j p (curlA i)) (1,0) (t-‖z‖,x+z) +
        z (curlB i)/‖z‖^3*j (t-‖z‖,x+z) (curlA i))) +
      (4*Real.pi)⁻¹ * (∫ n : Sphere,
        t*n.1 (curlA i)*j (0,x+t • n.1) (curlB i) -
        t*n.1 (curlB i)*j (0,x+t • n.1) (curlA i) ∂sphereMeasure) := by
  rw [magneticPotentialComponent_source hj,
    sourceWave_spatial_ibp (contDiff_component hj _) ht,
    sourceWave_spatial_ibp (contDiff_component hj _) ht]
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi (a b : Fin 3) : IntegrableOn (fun z : Vec =>
      z a/‖z‖^2*dirD (fun p => j p b) (1,0) (t-‖z‖,x+z) +
      z a/‖z‖^3*j (t-‖z‖,x+z) b) (ball (0:Vec) t) :=
    Integrable.add (integrableOn_ball_direction_div_norm_pow
      ((contDiff_dirD (contDiff_component hj b) _).continuous.comp harg) 1 (by norm_num) t a)
      (integrableOn_ball_direction_div_norm_pow
        ((contDiff_component hj b).continuous.comp harg) 2 (by norm_num) t a)
  have hb (a b : Fin 3) : Integrable (fun n : Sphere => t*n.1 a*j (0,x+t • n.1) b) sphereMeasure := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_const.mul ((PiLp.continuous_apply 2 _ a).comp continuous_subtype_val)).mul
        ((contDiff_component hj b).continuous.comp
          ((continuous_const : Continuous (fun _ : Sphere => (0:ℝ))).prodMk
            (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul
              (continuous_subtype_val : Continuous (fun n : Sphere => (n.1 : Vec)))))))
    · exact HasCompactSupport.of_compactSpace _
  rw [integral_sub (hi _ _) (hi _ _),integral_sub (hb _ _) (hb _ _)]
  ring

lemma uniform_integral_bound_compact {H W : Type*}
    [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {P : Set H} {K : Set Vec} {F : H × Vec → W}
    (hP : IsCompact P) (hK : IsCompact K)
    (hF : ContinuousOn F (P ×ˢ univ)) (hz : ∀ p ∈ P, ∀ v ∉ K, F (p,v)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ∈ P, ‖∫ v : Vec, F (p,v)‖≤C := by
  obtain ⟨C,hC⟩ := ((hP.prod hK).image_of_continuousOn (hF.mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩))).isBounded.exists_norm_le
  refine ⟨max C 0*volume.real K,mul_nonneg (le_max_right _ _) (measureReal_nonneg),?_⟩
  intro p hp
  have hc : Continuous (fun v : Vec => F (p,v)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v)) :=
    hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz p hp))
  have hfi : (∫ v : Vec, F (p,v))=∫ v in K, F (p,v) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hz p hp)
  rw [hfi]
  apply le_trans (norm_integral_le_integral_norm _)
  calc
    (∫ v in K, ‖F (p,v)‖) ≤ ∫ v in K, max C 0 := by
      apply integral_mono_ae hi.norm.integrableOn
        (integrableOn_const (hK.measure_lt_top.ne))
      filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
      exact le_trans (hC _ ⟨(p,v),⟨hp,hv⟩,rfl⟩) (le_max_left _ _)
    _ = max C 0*volume.real K := by simp [mul_comm]

lemma contDiffOn_retarded_flux {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0≤t) (x : Vec) (i : Fin 3) :
    ContDiffOn ℝ 1 (fun y => ∫ v : Vec,
      (retardedDensity s.f t x (y,v)*retardedG x (y,v) i) • velocity v)
      (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,hF,hz⟩ := retarded_local_data hf hc ht x
  have hG : ContDiffOn ℝ 1 (fun z => retardedG x z i) (retardedSpaceDomain t x ×ˢ univ) := by
    intro z hz
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp z
      (contDiffAt_retardedG hz.1.1)).contDiffWithinAt
  apply contDiffOn_integral_uniform_support (isOpen_retardedSpaceDomain t x) hK
    ((hF.mul hG).smul (contDiff_velocity.comp contDiff_snd).contDiffOn)
  intro y hy v hv
  change (retardedDensity s.f t x (y,v)*retardedG x (y,v) i) • velocity v=0
  rw [hz y hy v hv,zero_mul,zero_smul]

lemma divergence_add_right {F : Vec → Vec} (x z : Vec) :
    divergence (fun y => F (x+y)) z=divergence F (x+z) := by
  unfold divergence spatialPartial
  congr 1
  funext i
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i)) (fderiv_comp_add_left (f:=fun y => F y i) (x:=z) x)

lemma coneRadius_add (x z : Vec) : coneRadius x (x+z)=‖z‖ := by
  unfold coneRadius
  rw [show x-(x+z) = -z by abel,norm_neg]

lemma retarded_flux_norm_bound {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖∫ v : Vec, (retardedDensity s.f t x (x+z,v)*retardedG x (x+z,v) i) • velocity v‖≤C/‖z‖ := by
  have ht : 0≤t := le_trans hR hRt.le
  obtain ⟨K,hK,hz⟩ := hc t ht
  let K' : Set Vec := Prod.snd '' K
  have hK' : IsCompact K' := hK.image continuous_snd
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  let F : (Vec × Vec) × Vec → Vec := fun p =>
    (s.f (t-‖p.1.1‖,x+p.1.1,p.2)*(1-dot p.1.2 (velocity p.2))⁻¹*
      (p.1.2 i-velocity p.2 i)) • velocity p.2
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  have hu : Continuous (fun p : (Vec × Vec) × Vec => velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : (Vec × Vec) × Vec => 1-dot p.1.2 (velocity p.2)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_fst.snd.prodMk hu))
  have hd0 (p : (Vec × Vec) × Vec) (hp : p ∈ P ×ˢ univ) : 1-dot p.1.2 (velocity p.2)≠0 := by
    apply (cone_denom_pos _ _ ?_).ne'
    simpa only [mem_sphere,dist_zero_right] using hp.1.2
  have hcn : Continuous (fun p : (Vec × Vec) × Vec => p.1.2 i-velocity p.2 i) :=
    ((PiLp.continuous_apply 2 _ i).comp continuous_fst.snd).sub
      ((PiLp.continuous_apply 2 _ i).comp hu)
  have hF : ContinuousOn F (P ×ˢ univ) :=
    ((hcf.mul (hd.continuousOn.inv₀ hd0)).mul hcn.continuousOn).smul hu.continuousOn
  have hzero : ∀ p ∈ P, ∀ v ∉ K', F (p,v)=0 := by
    intro p hp v hv
    have hsf : s.f (t-‖p.1‖,x+p.1,v)=0 := by
      by_contra hne
      exact hv ⟨(x+p.1,v),hz _ (htime p.1 hp.1) (subset_tsupport _ hne),rfl⟩
    simp only [F,hsf,zero_mul,zero_smul]
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK' hF hzero
  refine ⟨C,hC,?_⟩
  intro z hz0 hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz0)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  let n := coneDirection x (x+z)
  have hn : ‖n‖=1 := coneDirection_norm hxy
  have hp : (z,n) ∈ P := ⟨by simpa only [mem_closedBall_zero_iff] using hzR,
    by simpa only [mem_sphere,dist_zero_right] using hn⟩
  have he : (∫ v : Vec, (retardedDensity s.f t x (x+z,v)*retardedG x (x+z,v) i) • velocity v) =
      ‖z‖⁻¹ • ∫ v : Vec, F ((z,n),v) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [retardedDensity,retardedG,eulerianG,coneRadius_add,PiLp.smul_apply,smul_eq_mul,
      mul_inv_rev,PiLp.sub_apply,F,smul_smul]
    congr 1
    ring
  rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz0.le)]
  calc
    ‖z‖⁻¹*‖∫ v : Vec, F ((z,n),v)‖ ≤ ‖z‖⁻¹*C :=
      mul_le_mul_of_nonneg_left (hbound (z,n) hp) (inv_nonneg.mpr hz0.le)
    _ = C/‖z‖ := by ring

lemma retarded_flux_tip {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1
      (∫ v : Vec, (retardedDensity s.f t x (x+ε • n.1,v)*
        retardedG x (x+ε • n.1,v) i) • velocity v) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := retarded_flux_norm_bound hf hc (show 0≤t/2 by linarith)
    (show t/2<t by linarith) x i
  apply spherical_flux_tendsto_zero (C:=C) (R:=t/2)
    (F:=fun z => ∫ v : Vec, (retardedDensity s.f t x (x+z,v)*retardedG x (x+z,v) i) • velocity v)
    (show 0<t/2 by linarith)
  intro z hz hzR
  exact hbound z hz hzR.le
end RVM

end

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
lemma retarded_weighted_integral_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, ‖z‖≤R → ∀ n : Vec, ‖n‖=1 →
      ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) • A ((z,n),v)‖≤C := by
  have ht : 0≤t := le_trans hR hRt.le
  obtain ⟨K,hK,hz⟩ := hc t ht
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  have hzero : ∀ p ∈ P, ∀ v ∉ Prod.snd '' K, s.f (t-‖p.1‖,x+p.1,v) • A (p,v)=0 := by
    intro p hp v hv
    have hsf : s.f (t-‖p.1‖,x+p.1,v)=0 := by
      by_contra hne
      exact hv ⟨(x+p.1,v),hz _ (htime p.1 hp.1) (subset_tsupport _ hne),rfl⟩
    rw [hsf,zero_smul]
  obtain ⟨C,hC,hb⟩ := uniform_integral_bound_compact hP (hK.image continuous_snd) (hcf.smul hA) hzero
  refine ⟨C,hC,?_⟩
  intro z hz n hn
  exact hb (z,n) ⟨by simpa only [mem_closedBall_zero_iff] using hz,
    by simpa only [mem_sphere,dist_zero_right] using hn⟩

def normalisedElectricKernel (r : ℝ) (n u b : Vec) : Vec :=
  ((1-dot u u)/(1-dot n u)^3) • (n-u) +
    (r/(1-dot n u)^3) • ((dot n b) • (n-u)-(1-dot n u) • b)

lemma normalisedElectricKernel_eq {r : ℝ} (hr : r≠0) (n u b : Vec) :
    normalisedElectricKernel r n u b=r^2 • physicalElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,physicalElectricKernel,PiLp.add_apply,PiLp.smul_apply,
    PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma continuousOn_normalisedElectricKernel {H : Type*} [TopologicalSpace H]
    {r : H → ℝ} {n u b : H → Vec} {S : Set H}
    (hr : ContinuousOn r S) (hn : ContinuousOn n S) (hu : ContinuousOn u S)
    (hb : ContinuousOn b S) (hd : ∀ z ∈ S, 1-dot (n z) (u z)≠0) :
    ContinuousOn (fun z => normalisedElectricKernel (r z) (n z) (u z) (b z)) S := by
  have hdot (f g : H → Vec) (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun z => dot (f z) (g z)) S :=
    (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (hf.prodMk hg)
  have hD : ContinuousOn (fun z => 1-dot (n z) (u z)) S :=
    continuousOn_const.sub (hdot n u hn hu)
  have hp : ∀ z ∈ S, (1-dot (n z) (u z))^3≠0 := fun z hz => pow_ne_zero 3 (hd z hz)
  exact (((continuousOn_const.sub (hdot u u hu hu)).div (hD.pow 3) hp).smul (hn.sub hu)).add
    ((hr.div (hD.pow 3) hp).smul (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma retarded_electric_kernel_norm_bound {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖∫ v : Vec, (s.f (t-coneRadius x (x+z),x+z,v)*
        (1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel (coneRadius x (x+z)) (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x (x+z),x+z)+
            cross (velocity v) (s.B (t-coneRadius x (x+z),x+z))))‖≤C/‖z‖^2 := by
  let S : Set ((Vec × Vec) × Vec) := (closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ
  let u : (Vec × Vec) × Vec → Vec := fun p => velocity p.2
  let n : (Vec × Vec) × Vec → Vec := fun p => p.1.2
  let b : (Vec × Vec) × Vec → Vec := fun p => fderiv ℝ velocity p.2
    (s.E (t-‖p.1.1‖,x+p.1.1)+cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1)))
  have hu : Continuous u := (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hn : Continuous n := continuous_fst.snd
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk (continuous_const.add continuous_fst.fst)
  have hmap : MapsTo (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) S fieldHalfSpace := by
    intro p hp
    have hnz : ‖p.1.1‖≤R := by simpa only [mem_closedBall_zero_iff] using hp.1.1
    change 0≤t-‖p.1.1‖
    linarith
  have he := hE.comp harg.continuousOn hmap
  have hm := hB.comp harg.continuousOn hmap
  have hcross : ContinuousOn (fun p : (Vec × Vec) × Vec =>
      cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1))) S :=
    (contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hm)
  have hb : ContinuousOn b S :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp continuous_snd).continuousOn.clm_apply (he.add hcross)
  have hD : Continuous (fun p : (Vec × Vec) × Vec => 1-dot (n p) (u p)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hD0 (p : (Vec × Vec) × Vec) (hp : p ∈ S) : 1-dot (n p) (u p)≠0 := by
    apply (cone_denom_pos _ _ ?_).ne'
    simpa only [n,mem_sphere,dist_zero_right] using hp.1.2
  have hN := continuousOn_normalisedElectricKernel (S:=S)
    continuous_fst.fst.norm.continuousOn hn.continuousOn hu.continuousOn hb hD0
  obtain ⟨C,hC,hbound⟩ := retarded_weighted_integral_bound hf hc hR hRt x (hD.continuousOn.smul hN)
  refine ⟨C,hC,?_⟩
  intro z hz0 hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz0)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have hh := hbound z hzR (coneDirection x (x+z)) (coneDirection_norm hxy)
  have heq : (∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))) =
      ‖z‖^2 • ∫ v : Vec, (s.f (t-‖z‖,x+z,v)*(1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [normalisedElectricKernel_eq hz0.ne']
    simp only [smul_smul]
    congr 1
    ring
  change ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))‖≤C at hh
  rw [heq,norm_smul,Real.norm_of_nonneg (sq_nonneg _)] at hh
  simp only [coneRadius_add]
  apply (le_div_iff₀ (sq_pos_of_pos hz0)).mpr
  simpa only [mul_comm] using hh

def retardedElectricDensity (s : Solution) (t : ℝ) (x y : Vec) : Vec :=
  ∫ v : Vec, (s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))) •
    physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
      (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))

def retardedElectricFlux (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (y : Vec) : Vec :=
  ∫ v : Vec, (retardedDensity s.f t x (y,v)*retardedG x (y,v) i) • velocity v

lemma field_contDiffAt_positive {k : ℕ∞ω} {F : Field}
    (hF : ContDiffOn ℝ k F fieldHalfSpace) {t : ℝ} (ht : 0<t) (x : Vec) :
    ContDiffAt ℝ k F (t,x) := by
  have hn : fieldHalfSpace ∈ 𝓝 (t,x) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)
      (fun p hp => show 0≤p.1 from hp.le)
  exact (hF _ ht.le).contDiffAt hn

lemma contDiffAt_physicalElectricKernel {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ∞ω} {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hr0 : r z≠0) (hd0 : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => physicalElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div ((hr.pow 2).mul (hD.pow 3))
      (mul_ne_zero (pow_ne_zero 2 hr0) (pow_ne_zero 3 hd0))).smul (hn.sub hu)).add
    (((hr.mul (hD.pow 3)).inv (mul_ne_zero hr0 (pow_ne_zero 3 hd0))).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma contDiffAt_retardedElectricIntegrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} {x y v : Vec} (hxy : x≠y) (ht : 0<t-coneRadius x y) :
    ContDiffAt ℝ 1 (fun z : Phase =>
      (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
        physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
          (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+
            cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))))) (y,v) := by
  have hr : ContDiffAt ℝ 1 (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ 1 (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have harg : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius x z.1,z.1)) (y,v) :=
    (contDiffAt_const.sub hr).prodMk contDiffAt_fst
  have he := (field_contDiffAt_positive hE ht y).comp (y,v) harg
  have hm := (field_contDiffAt_positive hB ht y).comp (y,v) harg
  have hcross : ContDiffAt ℝ 1 (fun z : Phase =>
      cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))) (y,v) :=
    contDiff_cross.contDiffAt.comp (y,v) (hu.prodMk hm)
  have hdf : ContDiff ℝ 1 (fderiv ℝ velocity) :=
    (contDiff_velocity (k:=2)).fderiv_right (by norm_num)
  have hb : ContDiffAt ℝ 1 (fun z : Phase => fderiv ℝ velocity z.2
      (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))) (y,v) :=
    (hdf.contDiffAt.comp (y,v) contDiffAt_snd).clm_apply (he.add hcross)
  have hd0 : 1-dot (coneDirection x y) (velocity v)≠0 :=
    (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  have hk := contDiffAt_physicalElectricKernel hr hn hu hb
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) hd0
  exact ((contDiffAt_retardedDensity (particle_contDiffAt_positive hf ht y v) hxy).mul
    (contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu)))).smul hk

lemma contDiffOn_retardedElectricDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedElectricDensity s t x) (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,_,hz⟩ := retarded_local_data hf hc ht x
  unfold retardedElectricDensity
  apply contDiffOn_integral_uniform_support (n:=1)
    (F:=fun z : Phase => (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
      physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
        (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))))
    (isOpen_retardedSpaceDomain t x) hK
  · intro z hz
    exact (contDiffAt_retardedElectricIntegrand hf hE hB hz.1.1 hz.1.2).contDiffWithinAt
  · intro y hy v hv
    change (retardedDensity s.f t x (y,v)*_) • _=0
    rw [hz y hy v hv,zero_mul,zero_smul]

lemma integrableOn_ball_of_punctured_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {R C α : ℝ} (hα : α<3)
    (hF : ContinuousOn F (ball (0:Vec) R \ {0}))
    (hb : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → ‖F z‖≤C*‖z‖^(-α)) :
    IntegrableOn F (ball (0:Vec) R) := by
  have hae : (ball (0:Vec) R \ ({0} : Set Vec) : Set Vec) =ᵐ[volume] (ball (0:Vec) R : Set Vec) := by
    filter_upwards [volume.ae_ne (0:Vec)] with z hz
    apply propext
    simp only [Set.mem_sdiff,mem_singleton_iff,hz,not_false_eq_true,and_true]
  have hmeas : AEStronglyMeasurable F (volume.restrict (ball (0:Vec) R)) := by
    rw [← Measure.restrict_congr_set hae]
    exact hF.aestronglyMeasurable (measurableSet_ball.diff (measurableSet_singleton _))
  apply ((integrableOn_norm_rpow_neg hα).const_mul C).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hb z (norm_pos_iff.mpr hz0) (by simpa only [mem_ball_zero_iff] using hz)

lemma integrableOn_retardedElectricDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) :
    IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt.le
  have hcont := (contDiffOn_retardedElectricDensity hf hE hB hc ht x).continuousOn
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont' := hcont.comp (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (C:=C) (α:=2) (by norm_num) hcont'
  intro z hz hzR
  have hh := hbound z hz hzR.le
  change ‖retardedElectricDensity s t x (x+z)‖≤C*‖z‖^(-(2:ℝ))
  rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  exact hh
end RVM

end

end OAI
