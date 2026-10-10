import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets
import OAI.Analysis.VlasovMaxwell.Continuation.SlabSmoothBootstrap
import OAI.Analysis.VlasovMaxwell.LocalPDE.SlabRHS

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def BoundedSpatiallySmoothSlab {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : ℝ) (F : ℝ × U → W) : Prop :=
  SpatiallySmoothSlab T F ∧ ∀ k : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x,
    ‖iteratedFDeriv ℝ k (fun y => F (t,y)) x‖≤C

lemma boundedSpatiallySmoothSlab_of_uniform_jets {U W : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → ℝ × U → W} {f : ℝ × U → W} {T : ℝ}
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈Icc (0:ℝ) T → ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => F n (t,y)) x‖≤C)
    (hl : TendstoUniformlyOn F f atTop {p | p.1∈Icc (0:ℝ) T}) :
    BoundedSpatiallySmoothSlab T f := by
  refine ⟨spatiallySmoothSlab_of_uniform_jets hF hb hl,?_⟩
  intro k
  obtain ⟨C,hC,hCb⟩ := hb k
  refine ⟨C,hC,?_⟩
  intro t ht x
  have hj := (smooth_spatial_limit_nat k hF hb hl).2.2.tendsto_at (x:=(t,x)) ht
  exact le_of_tendsto hj.norm (Eventually.of_forall fun n => hCb n t ht x)

theorem exists_local_spatially_smooth_bounded_classical (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, C1ClassicalPrefix d s T ∧ SlabEquations s T ∧
      BoundedSpatiallySmoothSlab T s.f ∧ BoundedSpatiallySmoothSlab T s.E ∧ BoundedSpatiallySmoothSlab T s.B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,E,B,hS0,hsm,hc,hr,hg,hEl,hBl,hEc,hBc,hcLim⟩ :=
    exists_picard_field_limit hd
  have hjets := uniform_picard_sequence_jets hd hT hT1 hN.le hM hS0 hsm hc hr
  obtain ⟨Q,hQ,hQEB,hQf⟩ := hjets 1
  have hQ0 : 0≤Q := zero_le_one.trans hQ
  have hcurv : ∀ n, SpatialFieldCurvature T (2*Q) (S n).E (S n).B := by
    intro n t ht
    exact ⟨curvature_of_second_derivative_bound ((hsm n).1.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).1),
      curvature_of_second_derivative_bound ((hsm n).2.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).2)⟩
  have hcurvf : ∀ n, PhaseParticleCurvature T (2*Q) (S (n+1)).f := by
    intro n t ht
    exact curvature_of_second_derivative_bound ((hr n).1.smooth_f.comp (contDiff_const.prodMk contDiff_id)) hQ0
      (hQf n t ht 2 le_rfl)
  obtain ⟨f,hfl,hfc,hfn,hfi,hfb,hfLip⟩ := picard_particle_limit hd hT.le hL.le hN.le hsm hc hr hg
  obtain ⟨hfC,hEC,hBC,heq⟩ := local_c1_limit_of_picard (s:=⟨f,E,B⟩) hT (by positivity) (by positivity) hM hL.le
    (fun n => (hr n).1) (fun n => (hr n).2.1) hcurv hcurvf (fun n => (hr n).2.2.1)
    (fun n => (hr n).2.2.2) hcLim.1 hfb hfc hfl hEl hBl
  have hEi (x : Vec) : E (0,x)=d.E₀ x := by
    have hh := (hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_E] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hBi (x : Vec) : B (0,x)=d.B₀ x := by
    have hh := (hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_B] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hL2 := picard_limit_slab_l2 hT.le hEC.continuousOn hBC.continuousOn hsm
    (fun n => (hr n).1) (fun n => (hr n).2.1) (fun n => (hr n).2.2.1) hEl hBl
  refine ⟨T,hT,⟨f,E,B⟩,⟨hfC,hEC,hBC,hfn,hL2.1,hL2.2,hfb.compact,heq.equationsBefore,hfi,hEi,hBi⟩,
    heq,?_,?_,?_⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hr n).1.smooth_f) _ hfl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht z => hQf n t ht k (by omega) z⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).1) _ hEl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).1⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).2) _ hBl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).2⟩

theorem exists_local_smooth_bounded_prefix (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, SmoothClassicalPrefix d s T ∧ SlabEquations s T ∧
      BoundedSpatiallySmoothSlab T s.f ∧ BoundedSpatiallySmoothSlab T s.E ∧
      BoundedSpatiallySmoothSlab T s.B := by
  obtain ⟨T,hT,s,hs,heq,hf,hE,hB⟩ := exists_local_spatially_smooth_bounded_classical d hd
  have htime {Domain Codomain : Type} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
      [NormedAddCommGroup Codomain] [NormedSpace ℝ Codomain]
      {function : ℝ × Domain → Codomain} {time : ℝ}
      (hfunction : ContDiffOn ℝ 1 function {point | point.1∈Icc 0 T})
      (hwithin : time∈Icc 0 T) (point : Domain) :
      DifferentiableWithinAt ℝ (fun value => function (value,point)) (Icc 0 T) time := by
    exact (hfunction.differentiableOn (by norm_num) (time,point) hwithin).comp time
      ((differentiableAt_id.prodMk (differentiableAt_const point)).differentiableWithinAt)
      (fun value hvalue => hvalue)
  have hparticle (time : ℝ) (hwithin : time∈Icc 0 T) (point : Phase) :
      HasDerivWithinAt (fun value => s.f (value,point)) (slabParticleRHS s (time,point))
        (Icc 0 T) time := by
    have hequation := (heq time hwithin).1 point.1 point.2
    have hspatial := (hf.1.1 time hwithin).differentiable (by simp) point
    simp only [spatialPartial] at hequation
    rw [← clm_sum_basis,← clm_sum_basis,add_assoc,fderiv_phase_split hspatial] at hequation
    have hderivative := (htime hs.f_c1 hwithin point).hasDerivWithinAt
    have hvalue : derivWithin (fun value => s.f (value,point)) (Icc 0 T) time =
        slabParticleRHS s (time,point) := by
      change derivWithin (fun value => s.f (value,point)) (Icc 0 T) time =
        -(fderiv ℝ (fun position => s.f (time,position)) point) (lorentzField s.E s.B (time,point))
      exact eq_neg_of_add_eq_zero_left hequation
    rwa [hvalue] at hderivative
  have helectric (time : ℝ) (hwithin : time∈Icc 0 T) (point : Vec) :
      HasDerivWithinAt (fun value => s.E (value,point)) (slabElectricRHS s (time,point))
        (Icc 0 T) time := by
    have hequation := (heq time hwithin).2.1 point
    rw [curl_eq_curlMap ((hB.1.1 time hwithin).differentiable (by simp))] at hequation
    have hderivative := (htime hs.E_c1 hwithin point).hasDerivWithinAt
    have hvalue : derivWithin (fun value => s.E (value,point)) (Icc 0 T) time =
        slabElectricRHS s (time,point) := by
      change _ = curlMap (fderiv ℝ (fun position => s.B (time,position)) point) -
        current (fun position => s.f (time,position)) point
      rw [sub_eq_iff_eq_add] at hequation
      rw [hequation]; abel
    rwa [hvalue] at hderivative
  have hmagnetic (time : ℝ) (hwithin : time∈Icc 0 T) (point : Vec) :
      HasDerivWithinAt (fun value => s.B (value,point)) (slabMagneticRHS s (time,point))
        (Icc 0 T) time := by
    have hequation := (heq time hwithin).2.2.1 point
    rw [curl_eq_curlMap ((hE.1.1 time hwithin).differentiable (by simp))] at hequation
    have hderivative := (htime hs.B_c1 hwithin point).hasDerivWithinAt
    have hvalue : derivWithin (fun value => s.B (value,point)) (Icc 0 T) time =
        slabMagneticRHS s (time,point) := eq_neg_of_add_eq_zero_left hequation
    rwa [hvalue] at hderivative
  have hregular (order : ℕ) : SpatialJetRegular order (Icc 0 T) s.f ∧
      SpatialJetRegular order (Icc 0 T) s.E ∧ SpatialJetRegular order (Icc 0 T) s.B := by
    induction order with
    | zero => exact ⟨hf.1.spatialJetRegular,hE.1.spatialJetRegular,hB.1.spatialJetRegular⟩
    | succ order hinduction =>
      exact ⟨spatialJetRegular_succ hT order hinduction.1
          (slabParticleRHS_regular hinduction.1 hinduction.2.1 hinduction.2.2) hparticle,
        spatialJetRegular_succ hT order hinduction.2.1
          (slabElectricRHS_regular hT order hinduction.1 hinduction.2.2 hs.compact) helectric,
        spatialJetRegular_succ hT order hinduction.2.2
          (slabMagneticRHS_regular hinduction.2.1) hmagnetic⟩
  have hfs : ContDiffOn ℝ ∞ s.f (particleSlab T) := by
    rw [contDiffOn_infty]
    exact fun order => (hregular order).1.regular
  have hEs : ContDiffOn ℝ ∞ s.E (fieldSlab T) := by
    rw [contDiffOn_infty]
    exact fun order => (hregular order).2.1.regular
  have hBs : ContDiffOn ℝ ∞ s.B (fieldSlab T) := by
    rw [contDiffOn_infty]
    exact fun order => (hregular order).2.2.regular
  exact ⟨T,hT,s,⟨hfs,hEs,hBs,hs.nonnegative,hs.E_L2,hs.B_L2,hs.compact,
    hs.equations,hs.initial_f,hs.initial_E,hs.initial_B⟩,heq,hf,hE,hB⟩

def timeSliceDatum (s : Solution) (t : ℝ) : Datum :=
  ⟨fun z => s.f (t,z),fun x => s.E (t,x),fun x => s.B (t,x)⟩

lemma SmoothClassicalPrefix.slice_admissible {d : Datum} {s : Solution} {T t : ℝ}
    (hs : SmoothClassicalPrefix d s T) (heq : SlabEquations s T)
    (hE : BoundedSpatiallySmoothSlab T s.E) (hB : BoundedSpatiallySmoothSlab T s.B)
    (ht : t∈Icc 0 T) : Admissible (timeSliceDatum s t) := by
  have hf : ContDiff ℝ ∞ (fun z => s.f (t,z)) :=
    hs.f_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun z => ht)
  obtain ⟨K,hK,hk⟩ := hs.compact
  have hfc : HasCompactSupport (fun z => s.f (t,z)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hk t ht)
  have hEb : BoundedSmooth (fun x => s.E (t,x)) :=
    ⟨hE.1.1 t ht,fun k => by obtain ⟨C,hC,hCb⟩ := hE.2 k; exact ⟨C,hCb t ht⟩⟩
  have hBb : BoundedSmooth (fun x => s.B (t,x)) :=
    ⟨hB.1.1 t ht,fun k => by obtain ⟨C,hC,hCb⟩ := hB.2 k; exact ⟨C,hCb t ht⟩⟩
  obtain ⟨EF,hEc,hEe⟩ := hs.E_L2
  obtain ⟨BF,hBc,hBe⟩ := hs.B_L2
  exact ⟨hf,hfc,hs.nonnegative t ht,hEb,hBb,
    (Lp.memLp (EF t)).ae_eq (hEe t ht), (Lp.memLp (BF t)).ae_eq (hBe t ht),
    (heq t ht).2.2.2.1,(heq t ht).2.2.2.2⟩

structure DatumRestartControl (d : Datum) (A R P D D₁ A₁ : ℝ) : Prop where
  particle : ∀ z, |d.f₀ z|≤A
  support : ∀ z : Phase, d.f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P
  fields : ∀ x, ‖d.E₀ x‖≤D ∧ ‖d.B₀ x‖≤D
  boundary : ∀ t∈Ioc (0:ℝ) 1, ∀ x,
    ‖electricBoundaryField (datumBoundarySolution d) t x‖≤D ∧
    ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤D
  fields_lip : ∀ x y, ‖d.E₀ y-d.E₀ x‖≤D₁*‖y-x‖ ∧ ‖d.B₀ y-d.B₀ x‖≤D₁*‖y-x‖
  boundary_lip : ∀ t∈Ioc (0:ℝ) 1, ∀ x y,
    ‖electricBoundaryField (datumBoundarySolution d) t y-electricBoundaryField (datumBoundarySolution d) t x‖≤D₁*‖y-x‖ ∧
    ‖magneticBoundaryField (datumBoundarySolution d) t y-magneticBoundaryField (datumBoundarySolution d) t x‖≤D₁*‖y-x‖
  particle_lip : ∀ z w : Phase, |d.f₀ z-d.f₀ w|≤A₁*‖z-w‖

theorem family_global_picard_invariance {ι : Type*} {d : ι → Datum} (_ : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (_ : 0≤D₀) (_ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      (∀ i, GlobalFieldBound T L (fun p : ℝ × Vec => (d i).E₀ p.2) (fun p : ℝ × Vec => (d i).B₀ p.2) ∧
      ∀ U : ℝ, 0≤U → U≤T → ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → GlobalFieldBound U L E B →
        ∀ s : Solution, PicardRegular (d i) s → TransportFor s E B →
          LocalParticleBound U A R P s.f ∧ GlobalFieldBound U L s.E s.B) := by
  let R := R₀+1
  let P := P₀+1
  let L := D+1
  have hL : 0<L := by dsimp [L]; linarith
  obtain ⟨C,hC,hdensity⟩ := uniform_retarded_density_bound A P L hA
  let T := min 1 (min ((2*L+1)⁻¹) ((C+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1 := min_le_left _ _
  have hT2 : T≤(2*L+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hT3 : T≤(C+1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hLT : 2*L*T≤1 := by
    have hh : T*(2*L+1)≤1 := (le_div_iff₀ (by positivity : 0<2*L+1)).mp (by simpa only [one_div] using hT2)
    nlinarith
  have hCT : C*T≤1 := by
    have hh : T*(C+1)≤1 := (le_div_iff₀ (by positivity : 0<C+1)).mp (by simpa only [one_div] using hT3)
    nlinarith
  refine ⟨T,A,R,P,L,hT,hT1,hA,by dsimp [R]; linarith,by dsimp [P]; linarith,hL,?_⟩
  intro i
  have hf₀ := (hcaps i).particle
  have hphase₀ := (hcaps i).support
  have hDEB := (hcaps i).fields
  have hboundary := (hcaps i).boundary
  constructor
  · intro t ht x
    exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
      (hDEB x).2.trans (by dsimp [L]; linarith)⟩
  · intro U hU0 hU E B hE hB hEB s hs hV
    have hU1 : U≤1 := hU.trans hT1
    have hLU : 2*L*U≤1 := (mul_le_mul_of_nonneg_left hU (by positivity)).trans hLT
    have hCU : C*U≤1 := (mul_le_mul_of_nonneg_left hU hC).trans hCT
    obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
    have hf : ∀ t∈Icc 0 U, ∀ z, |s.f (t,z)|≤A := by
      intro t ht z
      exact F.transported_sup_bound hs.smooth_f hV (fun z => by rw [hs.initial_f]; exact hf₀ z) t z
    have hphase : ∀ t∈Icc 0 U, ∀ z : Phase, s.f (t,z)≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
      intro t ht z hz
      have hh := F.transported_phase_bound hs.smooth_f hV
        (R₀:=R₀) (P₀:=P₀) (T:=U) (L:=L)
        (fun z hz => hphase₀ z (by simpa only [hs.initial_f] using hz)) hL.le
        (fun r hr x hx => (hEB r hr x).1)
        (fun r hr x hx => (hEB r hr x).2) ht z hz
      constructor
      · dsimp [R]
        linarith [hh.1,ht.2]
      · dsimp [P]
        have hh' : 2*L*t≤2*L*U := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        linarith [hh.2]
    refine ⟨fun t ht x v => ⟨hf t ht (x,v),hphase t ht (x,v)⟩,?_⟩
    intro t ht x
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_B]
      exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
        (hDEB x).2.trans (by dsimp [L]; linarith)⟩
    · have hbd := hboundary t ⟨ht0,ht.2.trans hU1⟩ x
      rw [← (hs.boundary_eq ht0 x).1,← (hs.boundary_eq ht0 x).2] at hbd
      have hdens := hdensity {s with E:=E,B:=B} U hU1 hf (by
        intro r hr y v hv
        exact ⟨(hphase r hr (y,v) hv).2,hEB r hr y⟩) t ht x
      have hh := mixed_fields_bound hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
        hs.smooth_rho hs.smooth_current hs.maxwell ht0 x hbd hdens
      have hh' : C*t≤C*U := mul_le_mul_of_nonneg_left ht.2 hC
      have hbound : D+C*t≤L := by dsimp [L]; linarith
      exact ⟨hh.1.trans hbound,hh.2.trans hbound⟩

theorem family_picard_control {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∀ i, FieldControl T L N (fun p : ℝ × Vec => (d i).E₀ p.2) (fun p : ℝ × Vec => (d i).B₀ p.2) ∧
      (∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → FieldControl T L N E B →
        ∀ s : Solution, PicardRegular (d i) s → TransportFor s E B →
          LocalParticleBound T A R P s.f ∧ PhaseParticleLip T M s.f ∧ FieldControl T L N s.E s.B) ∧
      (∀ (E B E' B' : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
        ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' → FieldControl T L N E B → FieldControl T L N E' B' →
        ∀ (s s' : Solution), PicardRegular (d i) s → PicardRegular (d i) s' →
          TransportFor s E B → TransportFor s' E' B' →
        ∀ D : ℝ, 0≤D →
          (∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D ∧ ‖B (t,x)-B' (t,x)‖≤D) →
          ∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)-s'.E (t,x)‖≤D/2 ∧ ‖s.B (t,x)-s'.B (t,x)‖≤D/2) := by
  obtain ⟨T₀,A,R,P,L,hT₀,hT₀1,hA,hR,hP,hL,hfamily⟩ :=
    family_global_picard_invariance hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  obtain ⟨C,hC,hcomp⟩ := uniform_picard_comparison A P L
  let N := D₀+1
  let M := A₁*Real.exp 1
  let K := 1+2*N+L
  have hN : 0<N := by dsimp [N]; linarith
  have hM : 0≤M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  let T := min T₀ (min K⁻¹ (min (C*(M+N)+1)⁻¹ (2*C*(2*M+1)+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hTT : T≤T₀ := min_le_left _ _
  have hT1 : T≤1 := hTT.trans hT₀1
  have hTK : K*T≤1 := by
    have hh : T≤K⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ hK).mp (show T≤1/K by simpa only [one_div] using hh)
    nlinarith
  have hTC : C*(M+N)*T≤1 := by
    have hh : T≤(C*(M+N)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<C*(M+N)+1)).mp
      (show T≤1/(C*(M+N)+1) by simpa only [one_div] using hh)
    nlinarith
  have hTC' : 2*C*(2*M+1)*T≤1 := by
    have hh : T≤(2*C*(2*M+1)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<2*C*(2*M+1)+1)).mp
      (show T≤1/(2*C*(2*M+1)+1) by simpa only [one_div] using hh)
    nlinarith
  have hexp {r : ℝ} (hr : r≤T) : Real.exp (K*r)≤Real.exp 1 :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hr hK.le).trans hTK)
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_⟩
  intro i
  obtain ⟨h₀,hstep⟩ := hfamily i
  have hDinit := (hcaps i).fields_lip
  have hDb := (hcaps i).boundary_lip
  have hAf' := (hcaps i).particle_lip
  have hbase {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular (d i) s) (hV : TransportFor s E B) :=
    hstep T hT.le hTT E B hE hB hc.1 s hs hV
  have hflip {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular (d i) s) (hV : TransportFor s E B) :
      PhaseParticleLip T M s.f := by
    intro t ht z z'
    have hh := transported_spatial_lipschitz hs hE hB hV hA₁ hL.le hN.le hAf'
      (fun r hr x => (hc.1 r hr x).2) (fun r hr x y => (hc.2 r hr x y).1)
      (fun r hr x y => (hc.2 r hr x y).2) ht z z'
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp le_rfl) hA₁) (norm_nonneg _))
  refine ⟨?_,?_,?_⟩
  · constructor
    · exact fun t ht x => h₀ t ⟨ht.1,ht.2.trans hTT⟩ x
    · intro t ht x y
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
  · intro E B hE hB hc s hs hV
    have hp := (hbase hE hB hc hs hV).1
    have hf := hflip hE hB hc hs hV
    refine ⟨hp,hf,(hbase hE hB hc hs hV).2,?_⟩
    intro t ht x y
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_E,hs.initial_B,hs.initial_B]
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
    · have hh := hcomp (d i) s s E B E B hs hs hE hB hE hB hV hV T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp r hr z v).1⟩)
        (by
          intro r hr z v hv
          have hz : s.f (r,z,v)=0 := by
            by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          exact ⟨hz,hz⟩)
        hc.1 hc.1 t ⟨ht0,ht.2⟩ y x (D₀*‖y-x‖) (M*‖y-x‖) (N*‖y-x‖)
        (hDb t ⟨ht0,ht.2.trans hT1⟩ x y)
        (by
          intro r hr z v
          simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
            max_eq_left (norm_nonneg _),add_sub_add_right_eq_sub] using hf r hr (y+z,v) (x+z,v))
        (by
          intro r hr z
          simpa only [add_sub_add_right_eq_sub] using hc.2 r hr (x+z) (y+z))
      have hm : max (M*‖y-x‖) (N*‖y-x‖)≤(M+N)*‖y-x‖ := by
        apply max_le <;> nlinarith [norm_nonneg (y-x)]
      have hb : D₀*‖y-x‖+C*max (M*‖y-x‖) (N*‖y-x‖)*t≤N*‖y-x‖ := by
        calc
          _ ≤ D₀*‖y-x‖+C*((M+N)*‖y-x‖)*T := add_le_add le_rfl
            (mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity))
          _ = (D₀+C*(M+N)*T)*‖y-x‖ := by ring
          _ ≤ N*‖y-x‖ := mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩
  · intro E B E' B' hE hB hE' hB' hc hc' s s' hs hs' hV hV' D hD hdiff t ht x
    have hp := (hbase hE hB hc hs hV).1
    have hp' := (hbase hE' hB' hc' hs' hV').1
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      simp only [hs.initial_E,hs'.initial_E,hs.initial_B,hs'.initial_B,sub_self,norm_zero]
      exact ⟨by positivity,by positivity⟩
    · have hfd (r : ℝ) (hr : r∈Icc 0 T) (z : Phase) : |s.f (r,z)-s'.f (r,z)|≤2*M*D := by
        have hh := transported_comparison hs.smooth_f hs'.smooth_f hE hB hE' hB' hV hV'
          hs.initial_f hs'.initial_f hA₁ hL.le hN.le hD hAf'
          (fun u hu w => (hc.1 u hu w).2) (fun u hu w w' => (hc.2 u hu w w').1)
          (fun u hu w w' => (hc.2 u hu w w').2)
          (fun u hu w => (hdiff u hu w).1) (fun u hu w => (hdiff u hu w).2) hr z z
        simp only [sub_self,norm_zero,zero_add] at hh
        apply hh.trans
        calc
          A₁*(2*D*r)*Real.exp ((1+2*N+L)*r) = (2*D*r)*(A₁*Real.exp (K*r)) := by ring
          _ ≤ (2*D*r)*M := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hexp hr.2) hA₁) (mul_nonneg (mul_nonneg (by norm_num) hD) hr.1)
          _ ≤ (2*D*1)*M := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hr.2.trans hT1) (by positivity)) hM
          _ = 2*M*D := by ring
      have hh := hcomp (d i) s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp' r hr z v).1⟩)
        (by
          intro r hr z v hv
          constructor
          · by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          · by_contra hn
            exact (not_lt_of_ge ((hp' r hr z v).2 hn).2) hv)
        hc.1 hc'.1 t ⟨ht0,ht.2⟩ x x 0 (2*M*D) D (by simp)
        (fun r hr z v => hfd r hr (x+z,v)) (fun r hr z => hdiff r hr (x+z))
      have hm : max (2*M*D) D≤(2*M+1)*D := by apply max_le <;> nlinarith
      have hb : 0+C*max (2*M*D) D*t≤D/2 := by
        calc
          _ ≤ C*((2*M+1)*D)*T := by
            simpa only [zero_add] using mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity)
          _ = (2*C*(2*M+1)*T)*(D/2) := by ring
          _ ≤ 1*(D/2) := mul_le_mul_of_nonneg_right hTC' (by positivity)
          _ = D/2 := one_mul _
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩

theorem family_contractive_picard_sequence {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∀ i, ∃ S : ℕ → Solution, S 0=datumBoundarySolution (d i) ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular (d i) (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        ∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,hfamily⟩ :=
    family_picard_control hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_⟩
  intro i
  obtain ⟨h₀,hstep,hcontract⟩ := hfamily i
  let Q := {s : Solution // ContDiff ℝ ∞ s.E ∧ ContDiff ℝ ∞ s.B}
  have hchoose (q : Q) : ∃ r : Q, PicardRegular (d i) r.1 ∧ TransportFor r.1 q.1.E q.1.B := by
    obtain ⟨s,hs,hV⟩ := exists_picard_regular (hd i) q.2.1 q.2.2
    exact ⟨⟨s,hs.smooth_E,hs.smooth_B⟩,hs,hV⟩
  choose step hs using hchoose
  let q₀ : Q := ⟨datumBoundarySolution (d i),
    (hd i).2.2.2.1.1.comp contDiff_snd,(hd i).2.2.2.2.1.1.comp contDiff_snd⟩
  let q : ℕ → Q := fun n => step^[n] q₀
  have hrec (n : ℕ) : q (n+1)=step (q n) := Function.iterate_succ_apply' step n q₀
  have hbound (n : ℕ) : FieldControl T L N (q n).1.E (q n).1.B := by
    induction n with
    | zero => exact h₀
    | succ n ih =>
      rw [hrec]
      exact (hstep _ _ (q n).2.1 (q n).2.2 ih _ (hs (q n)).1 (hs (q n)).2).2.2
  have hreg (n : ℕ) : PicardRegular (d i) (q (n+1)).1 ∧ TransportFor (q (n+1)).1 (q n).1.E (q n).1.B ∧
      LocalParticleBound T A R P (q (n+1)).1.f ∧ PhaseParticleLip T M (q (n+1)).1.f := by
    rw [hrec]
    exact ⟨(hs (q n)).1,(hs (q n)).2,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).1,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).2.1⟩
  refine ⟨fun n => (q n).1,rfl,
    fun n => (q n).2,hbound,hreg,?_⟩
  intro n
  induction n with
  | zero =>
    intro t ht x
    have h0 := (hbound 0).1 t ht x
    have h1 := (hbound 1).1 t ht x
    simp only [pow_zero,mul_one]
    constructor
    · exact (norm_sub_le _ _).trans (by linarith [h0.1,h1.1])
    · exact (norm_sub_le _ _).trans (by linarith [h0.2,h1.2])
  | succ n ih =>
    have hh := hcontract (q (n+1)).1.E (q (n+1)).1.B (q n).1.E (q n).1.B
      (q (n+1)).2.1 (q (n+1)).2.2 (q n).2.1 (q n).2.2 (hbound (n+1)) (hbound n)
      (q (n+1+1)).1 (q (n+1)).1 (hreg (n+1)).1 (hreg n).1 (hreg (n+1)).2.1 (hreg n).2.1
      (2*L*(1/2:ℝ)^n) (by positivity) ih
    intro t ht x
    convert hh t ht x using 1 <;> rw [pow_succ] <;> ring_nf

theorem family_picard_field_limit {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∀ i, ∃ (S : ℕ → Solution) (E B : Field), S 0=datumBoundarySolution (d i) ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular (d i) (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        (∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) ∧
        TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T} ∧
        TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T} ∧
        ContinuousOn E {p | p.1∈Icc 0 T} ∧ ContinuousOn B {p | p.1∈Icc 0 T} ∧
        FieldControl T L N E B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,hfamily⟩ :=
    family_contractive_picard_sequence hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_⟩
  intro i
  obtain ⟨S,hS0,hsm,hc,hr,hg⟩ := hfamily i
  obtain ⟨E,hE⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).E) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).1)
  obtain ⟨B,hB⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).B) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).2)
  refine ⟨S,E,B,hS0,hsm,hc,hr,hg,hE,hB,
    hE.continuousOn (Frequently.of_forall fun n => (hsm n).1.continuous.continuousOn),
    hB.continuousOn (Frequently.of_forall fun n => (hsm n).2.continuous.continuousOn),?_,?_⟩
  · intro t ht x
    exact ⟨le_of_tendsto (hE.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.1),
      le_of_tendsto (hB.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.2)⟩
  · intro t ht x y
    exact ⟨le_of_tendsto ((hE.tendsto_at (x:=(t,y)) ht).sub (hE.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.1),
      le_of_tendsto ((hB.tendsto_at (x:=(t,y)) ht).sub (hB.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.2)⟩

theorem family_local_spatially_smooth_bounded_classical {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T : ℝ, 0<T ∧ ∀ i, ∃ s : Solution, C1ClassicalPrefix (d i) s T ∧ SlabEquations s T ∧
      BoundedSpatiallySmoothSlab T s.f ∧ BoundedSpatiallySmoothSlab T s.E ∧ BoundedSpatiallySmoothSlab T s.B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,hfamily⟩ :=
    family_picard_field_limit hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  refine ⟨T,hT,?_⟩
  intro i
  obtain ⟨S,E,B,hS0,hsm,hc,hr,hg,hEl,hBl,hEc,hBc,hcLim⟩ := hfamily i
  have hjets := uniform_picard_sequence_jets (hd i) hT hT1 hN.le hM hS0 hsm hc hr
  obtain ⟨Q,hQ,hQEB,hQf⟩ := hjets 1
  have hQ0 : 0≤Q := zero_le_one.trans hQ
  have hcurv : ∀ n, SpatialFieldCurvature T (2*Q) (S n).E (S n).B := by
    intro n t ht
    exact ⟨curvature_of_second_derivative_bound ((hsm n).1.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).1),
      curvature_of_second_derivative_bound ((hsm n).2.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).2)⟩
  have hcurvf : ∀ n, PhaseParticleCurvature T (2*Q) (S (n+1)).f := by
    intro n t ht
    exact curvature_of_second_derivative_bound ((hr n).1.smooth_f.comp (contDiff_const.prodMk contDiff_id)) hQ0
      (hQf n t ht 2 le_rfl)
  obtain ⟨f,hfl,hfc,hfn,hfi,hfb,hfLip⟩ := picard_particle_limit (hd i) hT.le hL.le hN.le hsm hc hr hg
  obtain ⟨hfC,hEC,hBC,heq⟩ := local_c1_limit_of_picard (s:=⟨f,E,B⟩) hT (by positivity) (by positivity) hM hL.le
    (fun n => (hr n).1) (fun n => (hr n).2.1) hcurv hcurvf (fun n => (hr n).2.2.1)
    (fun n => (hr n).2.2.2) hcLim.1 hfb hfc hfl hEl hBl
  have hEi (x : Vec) : E (0,x)=(d i).E₀ x := by
    have hh := (hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_E] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hBi (x : Vec) : B (0,x)=(d i).B₀ x := by
    have hh := (hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_B] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hL2 := picard_limit_slab_l2 hT.le hEC.continuousOn hBC.continuousOn hsm
    (fun n => (hr n).1) (fun n => (hr n).2.1) (fun n => (hr n).2.2.1) hEl hBl
  refine ⟨⟨f,E,B⟩,⟨hfC,hEC,hBC,hfn,hL2.1,hL2.2,hfb.compact,heq.equationsBefore,hfi,hEi,hBi⟩,
    heq,?_,?_,?_⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hr n).1.smooth_f) _ hfl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht z => hQf n t ht k (by omega) z⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).1) _ hEl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).1⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).2) _ hBl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).2⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def timePaste {U W : Type*} (T : ℝ) (F G : ℝ × U → W) (p : ℝ × U) : W :=
  if p.1≤T then F p else G (p.1-T,p.2)

lemma timePaste_left {U W : Type*} (T : ℝ) (F G : ℝ × U → W) {t : ℝ} (ht : t≤T) :
    (fun x => timePaste T F G (t,x))=(fun x => F (t,x)) := by
  funext x; simp [timePaste,ht]

lemma timePaste_right {U W : Type*} (T : ℝ) (F G : ℝ × U → W)
    (hjoin : ∀ x, F (T,x)=G (0,x)) {t : ℝ} (ht : T≤t) :
    (fun x => timePaste T F G (t,x))=(fun x => G (t-T,x)) := by
  funext x
  by_cases hh : t≤T
  · have he : t=T := le_antisymm hh ht
    subst t; simp [timePaste,hjoin]
  · simp [timePaste,hh]

lemma continuousOn_timePaste {U W : Type*} [TopologicalSpace U] [TopologicalSpace W]
    {T S : ℝ} (_ : 0≤T) (_ : 0≤S) {F G : ℝ × U → W}
    (hF : ContinuousOn F {p | p.1∈Icc 0 T}) (hG : ContinuousOn G {p | p.1∈Icc 0 S})
    (hjoin : ∀ x, F (T,x)=G (0,x)) :
    ContinuousOn (timePaste T F G) {p | p.1∈Icc 0 (T+S)} := by
  let A : Set (ℝ × U) := {p | p.1≤T}
  have hA : IsClosed A := isClosed_le continuous_fst continuous_const
  have hF' : ContinuousOn F ({p | p.1∈Icc 0 (T+S)}∩A) :=
    hF.mono (fun p hp => ⟨hp.1.1,hp.2⟩)
  have hG' : ContinuousOn (fun p : ℝ × U => G (p.1-T,p.2))
      ({p | p.1∈Icc 0 (T+S)}∩{p | T≤p.1}) := by
    apply hG.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
    intro p hp
    change p.1-T∈Icc 0 S
    exact ⟨sub_nonneg.mpr hp.2,by linarith [hp.1.2]⟩
  have hleft : IsClosed ({p : ℝ × U | p.1∈Icc 0 (T+S)}∩A) :=
    ((isClosed_Icc).preimage continuous_fst).inter hA
  have hright : IsClosed ({p : ℝ × U | p.1∈Icc 0 (T+S)}∩{p | T≤p.1}) :=
    ((isClosed_Icc).preimage continuous_fst).inter (isClosed_le continuous_const continuous_fst)
  have h1 : ContinuousOn (timePaste T F G) ({p | p.1∈Icc 0 (T+S)}∩A) :=
    hF'.congr (fun p hp => by change (if p.1≤T then F p else G (p.1-T,p.2))=F p; exact ite_eq_left hp.2)
  have h2 : ContinuousOn (timePaste T F G) ({p | p.1∈Icc 0 (T+S)}∩{p | T≤p.1}) :=
    hG'.congr (fun p hp => congrFun (timePaste_right T F G hjoin hp.2) p.2)
  have hu := h1.union_of_isClosed h2 hleft hright
  have he : ({p : ℝ × U | p.1∈Icc 0 (T+S)}∩A)∪
      ({p | p.1∈Icc 0 (T+S)}∩{p | T≤p.1})={p | p.1∈Icc 0 (T+S)} := by
    ext p
    simp only [mem_union,mem_inter_iff,mem_ofPred_eq,A]
    exact ⟨fun h => h.elim And.left And.left,fun h => (le_total p.1 T).elim
      (fun hh => Or.inl ⟨h,hh⟩) (fun hh => Or.inr ⟨h,hh⟩)⟩
  rwa [he] at hu

lemma spatiallySmoothSlab_timePaste {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {T S : ℝ} (hT : 0≤T) (hS : 0≤S)
    {F G : ℝ × U → W} (hF : SpatiallySmoothSlab T F) (hG : SpatiallySmoothSlab S G)
    (hjoin : ∀ x, F (T,x)=G (0,x)) : SpatiallySmoothSlab (T+S) (timePaste T F G) := by
  have he (t : ℝ) : (fun x => timePaste T F G (t,x))=
      if t≤T then (fun x => F (t,x)) else (fun x => G (t-T,x)) := by
    split_ifs <;> funext x <;> simp_all [timePaste]
  refine ⟨?_,?_⟩
  · intro t ht
    rw [he]
    split_ifs with hh
    · exact hF.1 t ⟨ht.1,hh⟩
    · exact hG.1 (t-T) ⟨by linarith,by linarith [ht.2]⟩
  · intro k
    have hj : ∀ x, iteratedFDeriv ℝ k (fun y => F (T,y)) x=
        iteratedFDeriv ℝ k (fun y => G (0,y)) x := by
      intro x; rw [show (fun y => F (T,y))=(fun y => G (0,y)) from funext hjoin]
    have hh := continuousOn_timePaste hT hS (hF.2 k) (hG.2 k) hj
    convert hh using 1
    funext p
    rw [he]
    simp only [timePaste]
    split_ifs <;> rfl

lemma boundedSpatiallySmoothSlab_timePaste {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {T S : ℝ} (hT : 0≤T) (hS : 0≤S)
    {F G : ℝ × U → W} (hF : BoundedSpatiallySmoothSlab T F) (hG : BoundedSpatiallySmoothSlab S G)
    (hjoin : ∀ x, F (T,x)=G (0,x)) : BoundedSpatiallySmoothSlab (T+S) (timePaste T F G) := by
  refine ⟨spatiallySmoothSlab_timePaste hT hS hF.1 hG.1 hjoin,?_⟩
  intro k
  obtain ⟨A,hA,hAb⟩ := hF.2 k
  obtain ⟨B,hB,hBb⟩ := hG.2 k
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro t ht x
  by_cases hh : t≤T
  · rw [timePaste_left T F G hh]
    exact (hAb t ⟨ht.1,hh⟩ x).trans (le_max_left _ _)
  · rw [timePaste_right T F G hjoin (le_of_not_ge hh)]
    exact (hBb (t-T) ⟨by linarith,by linarith [ht.2]⟩ x).trans (le_max_right _ _)

lemma hasDerivWithinAt_timePaste {U W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T S : ℝ} (hT : 0≤T) (hS : 0≤S) {F G P Q : ℝ × U → W}
    (hF : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (P (t,x)) (Icc 0 T) t)
    (hG : ∀ t∈Icc 0 S, ∀ x, HasDerivWithinAt (fun r => G (r,x)) (Q (t,x)) (Icc 0 S) t)
    (hjoin : ∀ x, F (T,x)=G (0,x)) (hDjoin : ∀ x, P (T,x)=Q (0,x))
    {t : ℝ} (ht : t∈Icc 0 (T+S)) (x : U) :
    HasDerivWithinAt (fun r => timePaste T F G (r,x)) (timePaste T P Q (t,x)) (Icc 0 (T+S)) t := by
  have hleft (u : ℝ) (hu : u∈Icc 0 T) :
      HasDerivWithinAt (fun r => timePaste T F G (r,x)) (timePaste T P Q (u,x)) (Icc 0 T) u := by
    rw [congrFun (timePaste_left T P Q hu.2) x]
    exact (hF u hu x).congr (fun r hr => congrFun (timePaste_left T F G hr.2) x)
      (congrFun (timePaste_left T F G hu.2) x)
  have hright (u : ℝ) (hu : u∈Icc T (T+S)) :
      HasDerivWithinAt (fun r => timePaste T F G (r,x)) (timePaste T P Q (u,x)) (Icc T (T+S)) u := by
    have hv : u-T∈Icc 0 S := ⟨sub_nonneg.mpr hu.1,by linarith [hu.2]⟩
    have hh := (hG (u-T) hv x).scomp u ((hasDerivAt_id u).sub_const T).hasDerivWithinAt
      (show MapsTo (fun r => r-T) (Icc T (T+S)) (Icc 0 S) from
        fun r hr => ⟨sub_nonneg.mpr hr.1,by linarith [hr.2]⟩)
    simp only [one_smul] at hh
    rw [congrFun (timePaste_right T P Q hDjoin hu.1) x]
    exact hh.congr (fun r hr => congrFun (timePaste_right T F G hjoin hr.1) x)
      (congrFun (timePaste_right T F G hjoin hu.1) x)
  rcases lt_trichotomy t T with hlt|heq|hgt
  · apply (hleft t ⟨ht.1,hlt.le⟩).congr_set
    filter_upwards [Iio_mem_nhds hlt] with r hr
    exact propext ⟨fun h => ⟨h.1,by linarith [h.2]⟩,fun h => ⟨h.1,hr.le⟩⟩
  · subst t
    have hh := (hleft T ⟨hT,le_rfl⟩).union (hright T ⟨le_rfl,by linarith⟩)
    have he : Icc (0:ℝ) T∪Icc T (T+S)=Icc 0 (T+S) := by
      ext r
      simp only [mem_union,mem_Icc]
      constructor
      · rintro (hr|hr) <;> constructor <;> linarith [hr.1,hr.2]
      · intro hr
        exact (le_total r T).elim (fun h => Or.inl ⟨hr.1,h⟩) (fun h => Or.inr ⟨h,hr.2⟩)
    rwa [he] at hh
  · apply (hright t ⟨hgt.le,ht.2⟩).congr_set
    filter_upwards [Ioi_mem_nhds hgt] with r hr
    exact propext ⟨fun h => ⟨by linarith [h.1],h.2⟩,fun h => ⟨hr.le,h.2⟩⟩

lemma slabTimeContinuousL2_timePaste {T S : ℝ} (hT : 0≤T) (hS : 0≤S)
    {F G : Field} (hF : SlabTimeContinuousL2 T F) (hG : SlabTimeContinuousL2 S G)
    (hjoin : ∀ x, F (T,x)=G (0,x)) : SlabTimeContinuousL2 (T+S) (timePaste T F G) := by
  obtain ⟨F₂,hFc,hFe⟩ := hF
  obtain ⟨G₂,hGc,hGe⟩ := hG
  have hj : F₂ T=G₂ 0 := by
    apply Lp.ext
    filter_upwards [hFe T ⟨hT,le_rfl⟩,hGe 0 ⟨le_rfl,hS⟩] with x hf hg
    exact hf.trans ((hjoin x).trans hg.symm)
  let U := timePaste T (fun p : ℝ × Unit => F₂ p.1) (fun p => G₂ p.1)
  have hc : ContinuousOn U {p | p.1∈Icc 0 (T+S)} :=
    continuousOn_timePaste hT hS (hFc.comp continuous_fst.continuousOn (fun _ h => h))
      (hGc.comp continuous_fst.continuousOn (fun _ h => h)) (fun _ => hj)
  refine ⟨fun t => U (t,()),hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ h => h),?_⟩
  intro t ht
  by_cases hh : t≤T
  · dsimp only [U,timePaste]
    simp only [hh,ite_true]
    exact hFe t ⟨ht.1,hh⟩
  · dsimp only [U,timePaste]
    simp only [hh,ite_false]
    exact hGe (t-T) ⟨by linarith,by linarith [ht.2]⟩

end RVM

end

end OAI
