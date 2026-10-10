import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets
import OAI.Analysis.VlasovMaxwell.Population.HomogeneousCancellation

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma transportSpatialFlux_joint_contDiffAt (e : Vec) (i : Fin 3) {p : Phase}
    (hp : p.1 ≠ 0) :
    ContDiffAt ℝ 1 (fun z : Phase => transportSpatialFlux z.2 e i z.1) p := by
  have hz : (0:Vec) ≠ p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have he := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hd := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hne := (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hc := he.div (contDiffAt_const.sub hd) hne
  have hW : ContDiffAt ℝ 1 (fun z : Phase => coneSpatialLift 0 z.1 z.2 e) p :=
    contDiffAt_const.add (hc.smul hu)
  have hA := contDiffAt_transportAngularCore hn hu hne
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact (((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi).smul hW

lemma divergence_phase_first {F : Phase → Vec} {p : Phase}
    (hF : DifferentiableAt ℝ F p) :
    divergence (fun z => F (z,p.2)) p.1 =
      ∑ j : Fin 3, (fderiv ℝ F p (basis j,0)) j := by
  have hP := (hasFDerivAt_id (𝕜:=ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hh := hF.hasFDerivAt.comp p.1 hP
  change HasFDerivAt (fun z : Vec => F (z,p.2)) _ p.1 at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma continuousOn_transportSpatialDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : Phase => divergence (transportSpatialFlux p.2 e i) p.1)
      {p | p.1≠0} := by
  have he (p : Phase) (hp : p.1≠0) :=
    divergence_phase_first ((transportSpatialFlux_joint_contDiffAt e i hp).differentiableAt (by simp))
  apply ContinuousOn.congr (f:=fun p : Phase => ∑ j : Fin 3,
    (fderiv ℝ (fun z : Phase => transportSpatialFlux z.2 e i z.1) p (basis j,0)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((transportSpatialFlux_joint_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact he p hp

lemma transportSpatialDivergence_uniform_bound (P : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      |divergence (transportSpatialFlux v e i) n.1|≤C := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => divergence (transportSpatialFlux p.2 e i) p.1) K :=
    (continuousOn_transportSpatialDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
      intro hz
      simp only [hz,norm_zero] at hn
      norm_num at hn)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro v hv n
  exact (hC (n.1,v) ⟨n.2,hv⟩).trans (le_max_left _ _)

lemma divergence_phase_second {F : Phase → Vec} {p : Phase}
    (hF : DifferentiableAt ℝ F p) :
    divergence (fun z => F (p.1,z)) p.2 =
      ∑ j : Fin 3, (fderiv ℝ F p (0,basis j)) j := by
  have hP := (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id (𝕜:=ℝ) p.2)
  have hh := hF.hasFDerivAt.comp p.2 hP
  change HasFDerivAt (fun z : Vec => F (p.1,z)) _ p.2 at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma continuous_divergence_phase_slices {U : Set Vec} {F : Phase → Vec} {y : Vec}
    (hU : IsOpen U) (hy : y∈U) (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) :
    Continuous (fun v => divergence (fun z => F (z,v)) y) ∧
    Continuous (fun v => divergence (fun z => F (y,z)) v) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (y,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hd (v : Vec) : DifferentiableAt ℝ F (y,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)
  constructor
  · simp_rw [divergence_phase_first (hd _)]
    exact continuous_finsetSum _ (fun j _ =>
      (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp (hc.clm_apply continuous_const))
  · simp_rw [divergence_phase_second (hd _)]
    exact continuous_finsetSum _ (fun j _ =>
      (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp (hc.clm_apply continuous_const))

lemma phase_division_integral {U K : Set Vec} {g : Phase → ℝ} {W V : Phase → Vec}
    {y : Vec} {L : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hy : y∈U)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ univ))
    (hW : ContDiffOn ℝ 1 W (U ×ˢ univ))
    (hV : ContDiffOn ℝ 1 V (U ×ˢ univ))
    (hz : ∀ z∈U, ∀ v∉K, g (z,v)=0)
    (heq : ∀ v, L v = divergence (fun z => g (z,v) • W (z,v)) y+
      divergence (fun w => g (y,w) • V (y,w)) v-
      g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v)) :
    Integrable L ∧ (∫ v, L v) =
      divergence (fun z => ∫ v, g (z,v) • W (z,v)) y-
      ∫ v, g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v) := by
  have hgw := hg.smul hW
  have hgV := hg.smul hV
  have hzw : ∀ z∈U, ∀ v∉K, (g (z,v) • W (z,v))=0 := by
    intro z hu v hv
    rw [hz z hu v hv,zero_smul]
  have hsi := integrable_spatial_divergence_uniform_support hU hK hy hgw hzw
  have hse := divergence_integral_uniform_support hU hK hy hgw hzw
  change Integrable (fun v => divergence (fun z => g (z,v) • W (z,v)) y) at hsi
  change divergence (fun z => ∫ v, g (z,v) • W (z,v)) y =
    ∫ v, divergence (fun z => g (z,v) • W (z,v)) y at hse
  have hvc : ContDiff ℝ 1 (fun w => g (y,w) • V (y,w)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (hgV.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)
  have hgs : HasCompactSupport (fun v => g (y,v)) :=
    compactSupport_of_zero_off hK (hz y hy)
  have hvcp : HasCompactSupport (fun w => g (y,w) • V (y,w)) := hgs.smul_right
  have hvi := integrable_divergence_compact hvc hvcp
  have hgc : Continuous (fun v => g (y,v)) :=
    hg.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hci : Integrable (fun v => g (y,v)*(divergence (fun z => W (z,v)) y+
      divergence (fun w => V (y,w)) v)) :=
    (hgc.mul ((continuous_divergence_phase_slices hU hy hW).1.add
      (continuous_divergence_phase_slices hU hy hV).2)).integrable_of_hasCompactSupport hgs.mul_right
  have he : L = fun v => divergence (fun z => g (z,v) • W (z,v)) y+
      divergence (fun w => g (y,w) • V (y,w)) v-
      g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v) := funext heq
  rw [he]
  refine ⟨(hsi.add hvi).sub hci,?_⟩
  have hsub := integral_sub (hsi.add hvi) hci
  have hadd := integral_add hsi hvi
  simp only [Pi.add_apply] at hsub hadd hse
  rw [hsub,hadd,integral_divergence_zero hvc hvcp,add_zero,←hse]

lemma contDiffAt_coneSpatialCoefficient_phase {k : ℕ∞ω} {x y v e : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (fun z : Phase => coneSpatialCoefficient x z.1 z.2 e) (y,v) := by
  have hn := (contDiffAt_coneDirection (k:=k) hxy).comp (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ k (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have hde := contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu)
  exact hde.div (contDiffAt_const.sub hdu) (cone_denom_pos v _ (coneDirection_norm hxy)).ne'

lemma retarded_spatial_integral_division {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y e : Vec} {t : ℝ} (hxy : x≠y) (ht : 0<t-coneRadius x y)
    {k : Phase → ℝ} {K : Phase → Vec}
    (hk : ContDiffOn ℝ 1 k (retardedSpaceDomain t x ×ˢ univ))
    (hK : ContDiffOn ℝ 1 K (retardedSpaceDomain t x ×ˢ univ))
    (heq : ∀ v, fderiv ℝ s.f (t-coneRadius x y,y,v) (1,velocity v,K (y,v))=0) :
    (∫ v, k (y,v)*fderiv ℝ s.f (t-coneRadius x y,y,v) (0,e,0)) =
      divergence (fun z => ∫ v, (s.f (t-coneRadius x z,z,v)*k (z,v)) • coneSpatialLift x z v e) y-
      ∫ v, s.f (t-coneRadius x y,y,v)*
        (divergence (fun z => k (z,v) • coneSpatialLift x z v e) y+
          divergence (fun w => k (y,w) • (coneSpatialCoefficient x y w e • K (y,w))) v) := by
  have ht0 : 0≤t := by have hr := norm_nonneg (x-y); change 0<t-‖x-y‖ at ht; linarith
  obtain ⟨S,hS,hg,hz⟩ := retarded_local_data hf hc ht0 x
  have hU := isOpen_retardedSpaceDomain t x
  have hy : y∈retardedSpaceDomain t x := ⟨hxy,ht⟩
  have hco : ContDiffOn ℝ 1 (fun z : Phase => coneSpatialCoefficient x z.1 z.2 e)
      (retardedSpaceDomain t x ×ˢ univ) := fun z hz =>
    (contDiffAt_coneSpatialCoefficient_phase hz.1.1).contDiffWithinAt
  have hu : ContDiffOn ℝ 1 (fun z : Phase => velocity z.2) (retardedSpaceDomain t x ×ˢ univ) :=
    (contDiff_velocity.comp contDiff_snd).contDiffOn
  have hW : ContDiffOn ℝ 1 (fun z : Phase => k z • coneSpatialLift x z.1 z.2 e)
      (retardedSpaceDomain t x ×ˢ univ) :=
    hk.smul ((contDiffOn_const (c:=e)).add (hco.smul hu))
  have hV : ContDiffOn ℝ 1 (fun z : Phase => k z • (coneSpatialCoefficient x z.1 z.2 e • K z))
      (retardedSpaceDomain t x ×ˢ univ) := hk.smul (hco.smul hK)
  have hh := phase_division_integral
    (L:=fun v => k (y,v)*fderiv ℝ s.f (t-coneRadius x y,y,v) (0,e,0))
    hU hS hy hg hW hV hz (by
      intro v
      have hp := retarded_spatial_divergence (e:=e) (particle_differentiableAt_positive hf ht y v) hxy
        ((hK.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp))
        ((hk.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)) (heq v)
      simpa only [retardedDensity,smul_smul,smul_eq_mul,mul_assoc] using hp)
  simpa only [retardedDensity,smul_smul,smul_eq_mul,mul_assoc] using hh.2

lemma continuousOn_phase_divergences {U : Set Vec} {F : Phase → Vec}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) :
    ContinuousOn (fun p : Phase => divergence (fun z => F (z,p.2)) p.1) (U ×ˢ univ) ∧
    ContinuousOn (fun p : Phase => divergence (fun z => F (p.1,z)) p.2) (U ×ˢ univ) := by
  have hc := hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl
  have hd (p : Phase) (hp : p∈U ×ˢ univ) : DifferentiableAt ℝ F p :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hb (e : Phase) (j : Fin 3) :
      ContinuousOn (fun p => (fderiv ℝ F p e) j) (U ×ˢ univ) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp_continuousOn
      (hc.clm_apply continuousOn_const)
  constructor
  · apply ContinuousOn.congr (continuousOn_finsetSum _ (fun j _ => hb (basis j,0) j))
    intro p hp
    exact divergence_phase_first (hd p hp)
  · apply ContinuousOn.congr (continuousOn_finsetSum _ (fun j _ => hb (0,basis j) j))
    intro p hp
    exact divergence_phase_second (hd p hp)

lemma continuousOn_divergence_of_isOpen {U : Set Vec} {F : Vec → Vec}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) : ContinuousOn (divergence F) U := by
  have hc := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hd (p : Vec) (hp : p∈U) : DifferentiableAt ℝ F p :=
    (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  apply ContinuousOn.congr (f:=fun p => ∑ j : Fin 3, (fderiv ℝ F p (basis j)) j)
  · apply continuousOn_finsetSum
    intro j _
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp_continuousOn
      (hc.clm_apply continuousOn_const)
  · intro p hp
    unfold divergence spatialPartial
    simp_rw [fderiv_vec_component_at (hd p hp)]

lemma phase_division_annulus {U K : Set Vec} {g : Phase → ℝ} {W V : Phase → Vec}
    {L : Phase → ℝ} {ε R T : ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hε : 0<ε) (hεR : ε≤R) (hRT : R<T)
    (hdom : ∀ z : Vec, 0<‖z‖ → ‖z‖<T → z∈U)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ univ))
    (hW : ContDiffOn ℝ 1 W (U ×ˢ univ))
    (hV : ContDiffOn ℝ 1 V (U ×ˢ univ))
    (hz : ∀ z∈U, ∀ v∉K, g (z,v)=0)
    (heq : ∀ z∈U, ∀ v, L (z,v)=divergence (fun y => g (y,v) • W (y,v)) z+
      divergence (fun w => g (z,w) • V (z,w)) v-
      g (z,v)*(divergence (fun y => W (y,v)) z+divergence (fun w => V (z,w)) v)) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, L (z,v)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, g (R • n.1,v) • W (R • n.1,v)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, g (ε • n.1,v) • W (ε • n.1,v)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        g (z,v)*(divergence (fun y => W (y,v)) z+divergence (fun w => V (z,w)) v) := by
  let F : Vec → Vec := fun z => ∫ v, g (z,v) • W (z,v)
  have hF : ContDiffOn ℝ 1 F U :=
    contDiffOn_integral_uniform_support hU hK (hg.smul hW) (by
      intro z hu v hv
      change g (z,v) • W (z,v)=0
      rw [hz z hu v hv,zero_smul])
  let A := ball (0:Vec) R \ ball (0:Vec) ε
  let C := closedBall (0:Vec) R \ ball (0:Vec) ε
  have hC : IsCompact C := (isCompact_closedBall _ _).diff isOpen_ball
  have hAU : A⊆C := fun z hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hCU : C⊆U := by
    intro z hz
    have hzr : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz.1
    have hze : ε≤‖z‖ := by simpa only [mem_ball_zero_iff,not_lt] using hz.2
    exact hdom z (hε.trans_le hze) (hzr.trans_lt hRT)
  have hDz : IntegrableOn (divergence F) A :=
    (((continuousOn_divergence_of_isOpen hU hF).mono hCU).integrableOn_compact hC).mono_set hAU
  let B : Phase → ℝ := fun p =>
    g p*(divergence (fun y => W (y,p.2)) p.1+divergence (fun w => V (p.1,w)) p.2)
  have hB : ContinuousOn B (U ×ˢ univ) := hg.continuousOn.mul
    ((continuousOn_phase_divergences hU hW).1.add (continuousOn_phase_divergences hU hV).2)
  have hBi : ContinuousOn (fun z => ∫ v, B (z,v)) U := by
    apply continuousOn_integral_of_compact_support (k:=K) hK hB
    intro z v hu hv
    dsimp [B]
    rw [hz z hu v hv,zero_mul]
  have hBint : IntegrableOn (fun z => ∫ v, B (z,v)) A :=
    (hBi.mono hCU).integrableOn_compact hC |>.mono_set hAU
  have hD := divergence_annulus_local hε hεR hRT (F:=F) (by
    intro z hz ht
    exact hF.contDiffAt (hU.mem_nhds (hdom z hz ht)))
  have he (z : Vec) (hzA : z∈A) : (∫ v, L (z,v))=divergence F z-∫ v, B (z,v) :=
    (phase_division_integral hU hK (hCU (hAU hzA)) hg hW hV hz (heq z (hCU (hAU hzA)))).2
  rw [setIntegral_congr_fun (g:=fun z => divergence F z-∫v,B (z,v))
    (measurableSet_ball.diff measurableSet_ball) he,integral_sub hDz hBint,hD]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def spatialTranslateParticle (x : Vec) (f : Particle) : Particle :=
  fun p => f (p.1,x+p.2.1,p.2.2)

lemma spatialTranslateParticle_add (x : Vec) (f : Particle) :
    spatialTranslateParticle x f = fun p => f ((0,x,0)+p) := by
  funext p
  change f (p.1,x+p.2.1,p.2.2) = f (0+p.1,x+p.2.1,0+p.2.2)
  rw [zero_add,zero_add]

lemma fderiv_spatialTranslateParticle (x : Vec) (f : Particle) (p : ℝ × Phase) :
    fderiv ℝ (spatialTranslateParticle x f) p = fderiv ℝ f (p.1,x+p.2.1,p.2.2) := by
  rw [spatialTranslateParticle_add,fderiv_comp_add_left]
  change fderiv ℝ f (0+p.1,x+p.2.1,0+p.2.2)=_
  rw [zero_add,zero_add]

lemma shifted_retarded_local_data {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0≤t) (x : Vec) :
    ∃ K : Set Vec, IsCompact K ∧
      ContDiffOn ℝ 1 (retardedDensity (spatialTranslateParticle x s.f) t 0)
        (retardedSpaceDomain t 0 ×ˢ univ) ∧
      ∀ z∈retardedSpaceDomain t 0, ∀ v∉K,
        retardedDensity (spatialTranslateParticle x s.f) t 0 (z,v)=0 := by
  obtain ⟨K,hK,hg,hz⟩ := retarded_local_data hf hc ht x
  have hmap (z : Vec) (hz : z∈retardedSpaceDomain t 0) : x+z∈retardedSpaceDomain t x := by
    refine ⟨?_,?_⟩
    · intro he
      have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa only [add_zero] using he.symm)
      exact hz.1 hh.symm
    · rw [coneRadius_add]
      simpa only [coneRadius,zero_sub,norm_neg] using hz.2
  refine ⟨K,hK,?_,?_⟩
  · have hshift : ContDiff ℝ 1 (fun p : Phase => (x+p.1,p.2)) :=
      ((contDiff_const (c:=x)).add contDiff_fst).prodMk contDiff_snd
    have hm : MapsTo (fun p : Phase => (x+p.1,p.2))
        (retardedSpaceDomain t 0 ×ˢ univ) (retardedSpaceDomain t x ×ˢ univ) :=
      fun p hp => ⟨hmap p.1 hp.1,hp.2⟩
    have hh := hg.comp hshift.contDiffOn hm
    convert hh using 1
    funext p
    simp [retardedDensity,spatialTranslateParticle,coneRadius]
  · intro z hzu v hv
    have hh := hz (x+z) (hmap z hzu) v hv
    simpa [retardedDensity,spatialTranslateParticle,coneRadius] using hh

lemma shifted_retarded_spatial_divergence {f : Particle} {K : Phase → Vec} {k : Phase → ℝ}
    {x z v e : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius 0 z,x+z,v)) (hz : (0:Vec)≠z)
    (hK : DifferentiableAt ℝ K (z,v)) (hk : DifferentiableAt ℝ k (z,v))
    (heq : fderiv ℝ f (t-coneRadius 0 z,x+z,v) (1,velocity v,K (z,v))=0) :
    k (z,v)*fderiv ℝ f (t-coneRadius 0 z,x+z,v) (0,e,0)=
      divergence (fun y => (f (t-coneRadius 0 y,x+y,v)*k (y,v)) • coneSpatialLift 0 y v e) z+
      divergence (fun w => (f (t-coneRadius 0 z,x+z,w)*k (z,w)) •
        (coneSpatialCoefficient 0 z w e • K (z,w))) v-
      f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => k (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => k (z,w) • (coneSpatialCoefficient 0 z w e • K (z,w))) v) := by
  have hf' : DifferentiableAt ℝ (spatialTranslateParticle x f) (t-coneRadius 0 z,z,v) := by
    rw [spatialTranslateParticle_add]
    apply DifferentiableAt.comp (f:=fun p : ℝ × Phase => (0,x,0)+p) _ ?_
      ((differentiableAt_const _).add differentiableAt_id)
    change DifferentiableAt ℝ f (0+(t-coneRadius 0 z),x+z,0+v)
    simpa only [zero_add] using hf
  have heq' : fderiv ℝ (spatialTranslateParticle x f) (t-coneRadius 0 z,z,v)
      (1,velocity v,K (z,v))=0 := by
    rw [fderiv_spatialTranslateParticle]
    exact heq
  have hh := retarded_spatial_divergence (e:=e) hf' hz hK hk heq'
  simpa only [fderiv_spatialTranslateParticle,spatialTranslateParticle] using hh

lemma retarded_spatial_annulus {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x e : Vec} {t ε R : ℝ} (hε : 0<ε) (hεR : ε≤R) (hRt : R<t)
    {k : Phase → ℝ} {K : Phase → Vec}
    (hk : ContDiffOn ℝ 1 k (retardedSpaceDomain t 0 ×ˢ univ))
    (hK : ContDiffOn ℝ 1 K (retardedSpaceDomain t 0 ×ˢ univ))
    (heq : ∀ z∈retardedSpaceDomain t 0, ∀ v,
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (1,velocity v,K (z,v))=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,
      ∫ v, k (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v,
        (s.f (t-R,x+R • n.1,v)*k (R • n.1,v)) • coneSpatialLift 0 (R • n.1) v e) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v,
        (s.f (t-ε,x+ε • n.1,v)*k (ε • n.1,v)) • coneSpatialLift 0 (ε • n.1) v e) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => k (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => k (z,w) • (coneSpatialCoefficient 0 z w e • K (z,w))) v) := by
  have ht : 0<t := (hε.trans_le hεR).trans hRt
  obtain ⟨S,hS,hg,hzero⟩ := shifted_retarded_local_data hf hc ht.le x
  have hU := isOpen_retardedSpaceDomain t 0
  have hco : ContDiffOn ℝ 1 (fun z : Phase => coneSpatialCoefficient 0 z.1 z.2 e)
      (retardedSpaceDomain t 0 ×ˢ univ) := fun p hp =>
    (contDiffAt_coneSpatialCoefficient_phase hp.1.1).contDiffWithinAt
  have hu : ContDiffOn ℝ 1 (fun z : Phase => velocity z.2) (retardedSpaceDomain t 0 ×ˢ univ) :=
    (contDiff_velocity.comp contDiff_snd).contDiffOn
  have hW : ContDiffOn ℝ 1 (fun z : Phase => k z • coneSpatialLift 0 z.1 z.2 e)
      (retardedSpaceDomain t 0 ×ˢ univ) :=
    hk.smul ((contDiffOn_const (c:=e)).add (hco.smul hu))
  have hV : ContDiffOn ℝ 1 (fun z : Phase => k z • (coneSpatialCoefficient 0 z.1 z.2 e • K z))
      (retardedSpaceDomain t 0 ×ˢ univ) := hk.smul (hco.smul hK)
  have hh := phase_division_annulus
    (L:=fun p => k p*fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0))
    hU hS hε hεR hRt (by
      intro z hz hzt
      refine ⟨(norm_pos_iff.mp hz).symm,?_⟩
      simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hzt)
    hg hW hV hzero (by
      intro z hzu v
      have hp := shifted_retarded_spatial_divergence (e:=e)
        (particle_differentiableAt_positive hf hzu.2 (x+z) v) hzu.1
        ((hK.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hzu,mem_univ _⟩)).differentiableAt (by simp))
        ((hk.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hzu,mem_univ _⟩)).differentiableAt (by simp))
        (heq z hzu v)
      simpa only [retardedDensity,spatialTranslateParticle,smul_smul,smul_eq_mul,mul_assoc] using hp)
  have hrad (a : ℝ) (ha : 0≤a) (n : Sphere) : coneRadius 0 (a • n.1)=a := by
    simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg ha,sphere_norm,mul_one]
  simpa only [retardedDensity,spatialTranslateParticle,smul_smul,smul_eq_mul,mul_assoc,
    hrad R (hε.le.trans hεR),hrad ε hε.le] using hh

end RVM

end

end OAI
