import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.ParticleC1
import OAI.Analysis.VlasovMaxwell.Regularity.SlabL2

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def SlabEquations (s : Solution) (T : ℝ) : Prop := ∀ t∈Icc 0 T,
  (∀ x v,
    derivWithin (fun t' => s.f (t', x, v)) (Icc 0 T) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => s.f (t, y, v)) x i) +
    (∑ i : Fin 3, (s.E (t, x) + cross (velocity v) (s.B (t, x))) i *
      spatialPartial (fun v' => s.f (t, x, v')) v i) = 0) ∧
  (∀ x, derivWithin (fun t' => s.E (t', x)) (Icc 0 T) t -
    curl (fun y => s.B (t, y)) x = -current (fun z => s.f (t, z)) x) ∧
  (∀ x, derivWithin (fun t' => s.B (t', x)) (Icc 0 T) t +
    curl (fun y => s.E (t, y)) x = 0) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x = rho (fun z => s.f (t, z)) x) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)

lemma derivWithin_slab_assemble {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} {a : W} {A : U →L[ℝ] W} {t T : ℝ} {x : U}
    (hT : 0<T) (ht : t∈Icc 0 T)
    (hd : HasFDerivWithinAt F (assembleDerivative a A) {p | p.1∈Icc 0 T} (t,x)) :
    derivWithin (fun r => F (r,x)) (Icc 0 T) t=a := by
  have hh := hd.comp_hasDerivWithinAt t
    (((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt (s:=Icc 0 T))
    (fun r hr => hr)
  have he : assembleDerivative a A (1,0)=a := by simp [assembleDerivative]
  simpa only [Function.comp_def,id_eq,he] using hh.derivWithin (uniqueDiffOn_Icc hT t ht)

lemma slab_equations_of_derivatives {s : Solution} {T : ℝ} (hT : 0<T)
    {Z : ℝ × Phase → (Phase →L[ℝ] ℝ)} {XE XB : ℝ × Vec → (Vec →L[ℝ] Vec)}
    (hf : ∀ p : ℝ × Phase, p.1∈Icc 0 T → HasFDerivWithinAt s.f
      (assembleDerivative (-Z p (lorentzField s.E s.B p)) (Z p)) (particleSlab T) p)
    (hE : ∀ p : ℝ × Vec, p.1∈Icc 0 T → HasFDerivWithinAt s.E
      (assembleDerivative (curlMap (XB p)-current (fun z => s.f (p.1,z)) p.2) (XE p)) (fieldSlab T) p)
    (hB : ∀ p : ℝ × Vec, p.1∈Icc 0 T → HasFDerivWithinAt s.B
      (assembleDerivative (-curlMap (XE p)) (XB p)) (fieldSlab T) p)
    (hZ : ∀ t∈Icc 0 T, ∀ z, HasFDerivAt (fun w => s.f (t,w)) (Z (t,z)) z)
    (hXE : ∀ t∈Icc 0 T, ∀ x, HasFDerivAt (fun y => s.E (t,y)) (XE (t,x)) x)
    (hXB : ∀ t∈Icc 0 T, ∀ x, HasFDerivAt (fun y => s.B (t,y)) (XB (t,x)) x)
    (hGauss : ∀ p : ℝ × Vec, p.1∈Icc 0 T → divMap (XE p)=rho (fun z => s.f (p.1,z)) p.2 ∧ divMap (XB p)=0) :
    SlabEquations s T := by
  intro t ht
  have hsE : Differentiable ℝ (fun y => s.E (t,y)) := fun x => (hXE t ht x).differentiableAt
  have hsB : Differentiable ℝ (fun y => s.B (t,y)) := fun x => (hXB t ht x).differentiableAt
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x v
    rw [derivWithin_slab_assemble hT ht (hf (t,x,v) ht)]
    simp only [spatialPartial]
    rw [← clm_sum_basis,← clm_sum_basis]
    rw [add_assoc,fderiv_phase_split (hZ t ht (x,v)).differentiableAt,(hZ t ht (x,v)).fderiv]
    exact neg_add_cancel _
  · intro x
    rw [derivWithin_slab_assemble hT ht (hE (t,x) ht),curl_eq_curlMap hsB,(hXB t ht x).fderiv]
    abel
  · intro x
    rw [derivWithin_slab_assemble hT ht (hB (t,x) ht),curl_eq_curlMap hsE,(hXE t ht x).fderiv]
    exact neg_add_cancel _
  · intro x
    rw [divergence_eq_divMap hsE,(hXE t ht x).fderiv]
    exact (hGauss (t,x) ht).1
  · intro x
    rw [divergence_eq_divMap hsB,(hXB t ht x).fderiv]
    exact (hGauss (t,x) ht).2

lemma local_c1_limit_of_picard {d : Datum} {S : ℕ → Solution} {s : Solution}
    {T A R P H Hf M L : ℝ} (hT : 0<T) (hH : 0≤H) (hHf : 0≤Hf) (hM : 0≤M) (hL : 0≤L)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (htransport : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hc : ∀ n, SpatialFieldCurvature T H (S n).E (S n).B)
    (hcf : ∀ n, PhaseParticleCurvature T Hf (S (n+1)).f)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hlip : ∀ n, PhaseParticleLip T M (S (n+1)).f)
    (hlb : GlobalFieldBound T L s.E s.B)
    (hbf : LocalParticleBound T A R P s.f)
    (hfc : ContinuousOn s.f (particleSlab T))
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) s.f atTop (particleSlab T))
    (hEl : TendstoUniformlyOn (fun n => (S n).E) s.E atTop (fieldSlab T))
    (hBl : TendstoUniformlyOn (fun n => (S n).B) s.B atTop (fieldSlab T)) :
    ContDiffOn ℝ 1 s.f (particleSlab T) ∧ ContDiffOn ℝ 1 s.E (fieldSlab T) ∧
      ContDiffOn ℝ 1 s.B (fieldSlab T) ∧ SlabEquations s T := by
  have hEl' := hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)
  have hBl' := hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)
  obtain ⟨XE,XB,hXE,hXB,hs,hDE,hDB,hGauss⟩ := picard_field_full_derivative_limit hT hH hr
    (fun n => hc (n+1)) hb hbf hfc hfl hEl' hBl'
  obtain ⟨Z,hZ,hsZ,hDf⟩ := picard_particle_full_derivative_limit hHf hM hL hr htransport hcf hlip hlb hfl hEl hBl
  obtain ⟨hfC,hdf⟩ := c1_slab_uniform_derivative hT (fun n => (hr n).smooth_f) hfl hDf
  obtain ⟨hEC,hdE⟩ := c1_slab_uniform_derivative hT (fun n => (hr n).smooth_E) hEl' hDE
  obtain ⟨hBC,hdB⟩ := c1_slab_uniform_derivative hT (fun n => (hr n).smooth_B) hBl' hDB
  exact ⟨hfC,hEC,hBC,slab_equations_of_derivatives hT hdf hdE hdB hsZ
    (fun t ht x => (hs t ht x).1) (fun t ht x => (hs t ht x).2) hGauss⟩

theorem exists_local_c1_core (d : Datum) (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∃ (S : ℕ → Solution) (s : Solution),
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        ContDiffOn ℝ 1 s.f (particleSlab T) ∧ ContDiffOn ℝ 1 s.E (fieldSlab T) ∧
        ContDiffOn ℝ 1 s.B (fieldSlab T) ∧ SlabEquations s T ∧
        (∀ t∈Icc 0 T, ∀ z, 0 ≤ s.f (t,z)) ∧ LocalParticleBound T A R P s.f ∧
        FieldControl T L N s.E s.B ∧ PhaseParticleLip T M s.f ∧
        (∀ z, s.f (0,z)=d.f₀ z) ∧ (∀ x, s.E (0,x)=d.E₀ x) ∧ (∀ x, s.B (0,x)=d.B₀ x) ∧
        TendstoUniformlyOn (fun n => (S (n+1)).f) s.f atTop (particleSlab T) ∧
        TendstoUniformlyOn (fun n => (S n).E) s.E atTop (fieldSlab T) ∧
        TendstoUniformlyOn (fun n => (S n).B) s.B atTop (fieldSlab T) := by
  obtain ⟨T₀,A,R,P,L,N,M,hT₀,hT₀1,hA,hR,hP,hL,hN,hM,S,E,B,hS0,hsm,hc,hr,hg,hEl,hBl,hEc,hBc,hcLim⟩ :=
    exists_picard_field_limit hd
  obtain ⟨T,Hf,H,hT,hTT,hHf,hH,hcurv,hcurvf⟩ := uniform_picard_sequence_curvature hd hT₀ hT₀1 hL.le hN.le hM hS0 hsm hc hr
  obtain ⟨f,hfl,hfc,hfn,hfi,hfb,hfLip⟩ := picard_particle_limit hd hT₀.le hL.le hN.le hsm hc hr hg
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 T₀ := Icc_subset_Icc_right hTT
  have hr' (n : ℕ) : PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f :=
    ⟨(hr n).1,(hr n).2.1,fun t ht => (hr n).2.2.1 t (hsub ht),fun t ht => (hr n).2.2.2 t (hsub ht)⟩
  have hElT : TendstoUniformlyOn (fun n => (S n).E) E atTop (fieldSlab T) := hEl.mono (fun p hp => hsub hp)
  have hBlT : TendstoUniformlyOn (fun n => (S n).B) B atTop (fieldSlab T) := hBl.mono (fun p hp => hsub hp)
  have hflT : TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop (particleSlab T) := hfl.mono (fun p hp => hsub hp)
  have hcT : FieldControl T L N E B := ⟨fun t ht => hcLim.1 t (hsub ht),fun t ht => hcLim.2 t (hsub ht)⟩
  have hfbT : LocalParticleBound T A R P f := fun t ht => hfb t (hsub ht)
  obtain ⟨hfC,hEC,hBC,heq⟩ := local_c1_limit_of_picard (s:=⟨f,E,B⟩) hT hH hHf hM hL.le
    (fun n => (hr n).1) (fun n => (hr n).2.1) hcurv hcurvf (fun n => (hr' n).2.2.1)
    (fun n => (hr' n).2.2.2) hcT.1 hfbT (hfc.mono (fun p hp => hsub hp)) hflT hElT hBlT
  refine ⟨T,A,R,P,L,N,M,hT,hTT.trans hT₀1,hA,hR,hP,hL,hN,hM,S,⟨f,E,B⟩,hsm,hr',hfC,hEC,hBC,heq,
    (fun t ht => hfn t (hsub ht)),hfbT,hcT,(fun t ht => hfLip t (hsub ht)),hfi,?_,?_,hflT,hElT,hBlT⟩
  · intro x
    have hh := (hElT.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_E] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · intro x
    have hh := (hBlT.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_B] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

structure C1ClassicalPrefix (d : Datum) (s : Solution) (T : ℝ) : Prop where
  f_c1 : ContDiffOn ℝ 1 s.f (particleSlab T)
  E_c1 : ContDiffOn ℝ 1 s.E (fieldSlab T)
  B_c1 : ContDiffOn ℝ 1 s.B (fieldSlab T)
  nonnegative : ∀ t∈Icc 0 T, ∀ z, 0 ≤ s.f (t,z)
  E_L2 : SlabTimeContinuousL2 T s.E
  B_L2 : SlabTimeContinuousL2 T s.B
  compact : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K
  equations : EquationsBefore s T
  initial_f : ∀ z, s.f (0,z)=d.f₀ z
  initial_E : ∀ x, s.E (0,x)=d.E₀ x
  initial_B : ∀ x, s.B (0,x)=d.B₀ x

lemma derivWithin_Ici_eq_Icc_of_lt {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) {t T : ℝ} (ht : t<T) :
    derivWithin f (Ici 0) t=derivWithin f (Icc 0 T) t := by
  apply derivWithin_congr_set
  filter_upwards [Iio_mem_nhds ht] with r hr
  change (0≤r) = (0≤r ∧ r≤T)
  exact propext ⟨fun h => ⟨h,hr.le⟩,fun h => h.1⟩

lemma SlabEquations.equationsBefore {s : Solution} {T : ℝ} (h : SlabEquations s T) :
    EquationsBefore s T := by
  intro t ht htT
  simpa only [derivWithin_Ici_eq_Icc_of_lt _ htT] using h t ⟨ht,htT.le⟩

lemma LocalParticleBound.compact {T A R P : ℝ} {f : Particle} (h : LocalParticleBound T A R P f) :
    ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => f (t,z)) ⊆ K := by
  refine ⟨closedBall (0:Vec) R ×ˢ closedBall (0:Vec) P,
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _),?_⟩
  intro t ht
  apply closure_minimal
  · intro z hz
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using ((h t ht z.1 z.2).2 hz).1,
      by simpa only [mem_closedBall,dist_zero_right] using ((h t ht z.1 z.2).2 hz).2⟩
  · exact isClosed_closedBall.prod isClosed_closedBall

theorem exists_local_classical_prefix (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, C1ClassicalPrefix d s T ∧ SlabEquations s T := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,s,hsm,hr,hfC,hEC,hBC,heq,hn,hb,hcontrol,hlip,
    hfi,hEi,hBi,hfl,hEl,hBl⟩ := exists_local_c1_core d hd
  have hELBL := picard_limit_slab_l2 hT.le hEC.continuousOn hBC.continuousOn hsm
    (fun n => (hr n).1) (fun n => (hr n).2.1) (fun n => (hr n).2.2.1) hEl hBl
  exact ⟨T,hT,s,⟨hfC,hEC,hBC,hn,hELBL.1,hELBL.2,hb.compact,heq.equationsBefore,hfi,hEi,hBi⟩,heq⟩

lemma C1ClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : C1ClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨hs.f_c1.mono (fun _ hp => hp.1),hs.E_c1.mono (fun _ hp => hp.1),
    hs.B_c1.mono (fun _ hp => hp.1),hs.nonnegative,hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

end RVM

end

end OAI
