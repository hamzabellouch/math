import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.ElectricBoundaryField
import OAI.Analysis.VlasovMaxwell.Flow.PhaseTimePullback

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def receiverQCLM (a n : Vec) : Vec →L[ℝ] Vec :=
  ContinuousLinearMap.id ℝ Vec+(crossCLM a).comp (crossCLM n)

lemma receiverQCLM_apply (a n h : Vec) : receiverQCLM a n h=receiverQ a n h := by
  simp only [receiverQCLM,add_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,crossCLM_apply,receiverQ_force]

lemma integral_receiverQ {H : Vec → Vec} (hH : Integrable H) (a n : Vec) :
    (∫ v : Vec, receiverQ a n (H v))=receiverQ a n (∫ v : Vec, H v) := by
  simpa only [receiverQCLM_apply] using (receiverQCLM a n).integral_comp_comm hH

def retardedForceKernel (s : Solution) (t : ℝ) (x a : Vec) (y v : Vec) : Vec :=
  s.f (t-coneRadius x y,y,v) •
    (forceTransportKernel (coneRadius x y) (coneDirection x y) a v+
      forceSourceKernel (coneRadius x y) (coneDirection x y) a v
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))))

lemma physical_lorentz_density {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} {x y : Vec} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (a : Vec) :
    retardedElectricDensity s t x y+cross a (retardedMagneticDensity s t x y)=
      ∫ v : Vec, retardedForceKernel s t x a y v := by
  change receiverQCLM a (coneDirection x y) (retardedElectricDensity s t x y)=_
  rw [receiverQCLM_apply,retardedElectricDensity,← integral_receiverQ
    (integrable_retardedElectricDensity_integrand hf hc hxy ht)]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [receiverQ_smul,mul_smul,physical_force_kernel _ _ _ _ _
    (show coneRadius x y≠0 by exact (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).ne')
    (coneDirection_norm hxy)]
  rfl

lemma classical_boundaryLorentzForce_datum {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0<t) (x a : Vec) :
    boundaryLorentzForce s t x a=boundaryLorentzForce (datumBoundarySolution d) t x a := by
  have hE : electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_electricConeBoundary_datum hs ht x i
  have hB : magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_magneticConeBoundary_datum hs ht x i
  simp only [boundaryLorentzForce,hE,hB]

lemma classical_retarded_force_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, ∫ v : Vec, retardedForceKernel s t x a (x+z) v := by
  rw [classical_physical_force_representation hs hm ht,classical_boundaryLorentzForce_datum hs ht]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  apply physical_lorentz_density hs.1 hs.2.2.2.2.2.2.1
  · intro he
    exact hz0 (add_left_cancel (show x+z=x+0 by simpa using he.symm))
  · rw [coneRadius_add]
    exact sub_nonneg.mpr (show ‖z‖≤t from (mem_ball_zero_iff.mp hz).le)

lemma ball_puncture_ae (R : ℝ) :
    (ball (0:Vec) R \ ({0} : Set Vec) : Set Vec) =ᵐ[volume] (ball (0:Vec) R : Set Vec) := by
  filter_upwards [volume.ae_ne (0:Vec)] with z hz
  apply propext
  simp only [Set.mem_sdiff,mem_singleton_iff,hz,not_false_eq_true,and_true]

lemma integrable_joint_of_punctured_norm_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : Vec × Vec → W} {R C α : ℝ} {K : Set Vec} (hα : α<3)
    (hK : IsCompact K)
    (hF : ContinuousOn F ((ball (0:Vec) R \ {0}) ×ˢ univ))
    (hz : ∀ z ∈ ball (0:Vec) R \ {0}, ∀ v ∉ K, F (z,v)=0)
    (hb : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → (∫ v : Vec, ‖F (z,v)‖)≤C*‖z‖^(-α)) :
    Integrable F ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  have hm : AEStronglyMeasurable F ((volume.restrict (ball (0:Vec) R)).prod volume) := by
    rw [← Measure.restrict_congr_set (ball_puncture_ae R)]
    have hh := hF.aestronglyMeasurable (μ:=volume.prod volume)
      ((measurableSet_ball.diff (measurableSet_singleton _)).prod MeasurableSet.univ)
    simpa only [← Measure.prod_restrict,Measure.restrict_univ] using hh
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzR hz0
    have hz' : z∈ball (0:Vec) R \ {0} := ⟨hzR,hz0⟩
    have hc : Continuous (fun v : Vec => F (z,v)) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz',mem_univ _⟩)
    exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz z hz'))
  · apply integrableOn_ball_of_punctured_bound hα
      (continuousOn_integral_uniform_support hK hF.norm (by
        intro z hz' v hv
        simp only [hz z hz' v hv,norm_zero]))
    intro z hz0 hzR
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb z hz0 hzR

lemma coneDirection_translate (x z : Vec) : coneDirection x (x+z)=coneDirection 0 z := by
  simp only [coneDirection,coneRadius,show x-(x+z) = -z by abel,zero_sub]

lemma continuousOn_coneDirection_zero {R : ℝ} :
    ContinuousOn (coneDirection (0:Vec)) (ball (0:Vec) R \ {0}) := by
  intro z hz
  have h0z : (0:Vec)≠z := by simpa only [mem_singleton_iff,ne_comm] using hz.2
  exact (contDiffAt_coneDirection (k:=1) h0z).continuousAt.continuousWithinAt

lemma integrable_radial_lift {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {R : ℝ} {K : Set Vec} {F : (Vec × Vec) × Vec → W}
    (hK : IsCompact K)
    (hF : ContinuousOn F ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ))
    (hz : ∀ z ∈ closedBall (0:Vec) R, ∀ n ∈ sphere (0:Vec) 1, ∀ v ∉ K, F ((z,n),v)=0) :
    Integrable (fun p : Vec × Vec => (‖p.1‖^2)⁻¹ • F ((p.1,coneDirection 0 p.1),p.2))
      ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  let S : Set Vec := ball (0:Vec) R \ {0}
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  have hN : ContinuousOn (fun z : Vec => (‖z‖^2)⁻¹) S :=
    (continuous_norm.pow 2).continuousOn.inv₀ (by
      intro z hz'
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz'.2))
  have harg : ContinuousOn (fun p : Vec × Vec => ((p.1,coneDirection 0 p.1),p.2)) (S ×ˢ univ) :=
    (continuous_fst.continuousOn.prodMk
      (continuousOn_coneDirection_zero.comp continuous_fst.continuousOn (fun _ h => h.1))).prodMk
      continuous_snd.continuousOn
  have hmap : MapsTo (fun p : Vec × Vec => ((p.1,coneDirection 0 p.1),p.2)) (S ×ˢ univ) (P ×ˢ univ) := by
    intro p hp
    refine ⟨⟨ball_subset_closedBall hp.1.1,?_⟩,mem_univ _⟩
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm (Ne.symm hp.1.2)
  have hcont : ContinuousOn (fun p : Vec × Vec => (‖p.1‖^2)⁻¹ • F ((p.1,coneDirection 0 p.1),p.2))
      (S ×ˢ univ) :=
    (hN.comp continuous_fst.continuousOn (fun _ h => h.1)).smul (hF.comp harg hmap)
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK hF.norm
    (by intro p hp v hv; simp only [hz p.1 hp.1 p.2 hp.2 v hv,norm_zero])
  apply integrable_joint_of_punctured_norm_bound (C:=C) (α:=2) (by norm_num) hK hcont
  · intro z hzs v hv
    have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
      simpa only [mem_sphere,dist_zero_right] using coneDirection_norm (Ne.symm hzs.2)
    rw [hz z (ball_subset_closedBall hzs.1) _ hn v hv,smul_zero]
  · intro z hz0 hzR
    have hz' : z∈closedBall (0:Vec) R := mem_closedBall_zero_iff.mpr hzR.le
    have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
      simpa only [mem_sphere,dist_zero_right] using coneDirection_norm (Ne.symm (norm_pos_iff.mp hz0))
    have hb := hbound (z,coneDirection 0 z) ⟨hz',hn⟩
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hb
    simp only [norm_smul,Real.norm_of_nonneg (show 0≤(‖z‖^2)⁻¹ by positivity),integral_const_mul]
    rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two,mul_comm C]
    exact mul_le_mul_of_nonneg_left hb (by positivity)

lemma integrable_retarded_weighted_radial {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    Integrable (fun p : Vec × Vec => (‖p.1‖^2)⁻¹ •
      (s.f (t-‖p.1‖,x+p.1,p.2) • A ((p.1,coneDirection 0 p.1),p.2)))
      ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  have ht : 0≤t := le_trans hR hRt
  obtain ⟨K,hK,hz⟩ := hc t ht
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  apply integrable_radial_lift (hK.image continuous_snd) (hcf.smul hA)
  intro z hz' n hn v hv
  have hsf : s.f (t-‖z‖,x+z,v)=0 := by
    by_contra hne
    exact hv ⟨(x+z,v),hz _ (htime z hz') (subset_tsupport _ hne),rfl⟩
  change s.f (t-‖z‖,x+z,v) • A ((z,n),v)=0
  rw [hsf,zero_smul]

lemma continuousOn_receiverQ {H : Type*} [TopologicalSpace H] {S : Set H}
    {a n h : H → Vec} (ha : ContinuousOn a S) (hn : ContinuousOn n S) (hh : ContinuousOn h S) :
    ContinuousOn (fun p => receiverQ (a p) (n p) (h p)) S := by
  exact ((continuousOn_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (hn.prodMk ha))).smul hh).add
      (((contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (ha.prodMk hh)).smul hn)

def retardedNormalisedForce (s : Solution) (t : ℝ) (x a : Vec) (p : (Vec × Vec) × Vec) : Vec :=
  (1-dot p.1.2 (velocity p.2)) • receiverQ a p.1.2
    (normalisedElectricKernel ‖p.1.1‖ p.1.2 (velocity p.2)
      (fderiv ℝ velocity p.2 (s.E (t-‖p.1.1‖,x+p.1.1)+
        cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1)))))

lemma continuousOn_retardedNormalisedForce {s : Solution}
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    {t R : ℝ} (hRt : R≤t) (x a : Vec) :
    ContinuousOn (retardedNormalisedForce s t x a)
      ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ) := by
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
  exact hD.continuousOn.smul (continuousOn_receiverQ continuousOn_const hn.continuousOn hN)

lemma radial_retardedNormalisedForce_eq (s : Solution) (t : ℝ) (x a z v : Vec) (hz : z≠0) :
    (‖z‖^2)⁻¹ • (s.f (t-‖z‖,x+z,v) • retardedNormalisedForce s t x a ((z,coneDirection 0 z),v)) =
      retardedForceKernel s t x a (x+z) v := by
  simp only [retardedNormalisedForce,retardedForceKernel,coneRadius_add,coneDirection_translate]
  rw [normalisedElectricKernel_eq (norm_ne_zero_iff.mpr hz),receiverQ_smul]
  rw [← physical_force_kernel _ _ _ _ _ (norm_ne_zero_iff.mpr hz)
    (coneDirection_norm (Ne.symm hz))]
  simp only [smul_smul]
  congr 1
  field_simp

lemma integrable_joint_retardedForceKernel {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x a : Vec) :
    Integrable (fun p : Vec × Vec => retardedForceKernel s t x a (x+p.1) p.2)
      ((volume.restrict (ball (0:Vec) R)).prod volume) := by
  have hi := integrable_retarded_weighted_radial hf hc hR hRt x
    (continuousOn_retardedNormalisedForce hE hB hRt x a)
  apply hi.congr
  have hne : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), z≠0 :=
    ae_restrict_of_ae (volume.ae_ne (0:Vec))
  filter_upwards [MeasureTheory.Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hne] with p hp
  exact radial_retardedNormalisedForce_eq s t x a p.1 p.2 hp

lemma classical_retarded_force_phase_integral {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ p : Phase, retardedForceKernel s t x a (x+p.1) p.2
        ∂((volume.restrict (ball (0:Vec) t)).prod volume) := by
  rw [classical_retarded_force_representation hs hm ht]
  congr 2
  symm
  exact integral_prod _ (integrable_joint_retardedForceKernel hs.1 hs.2.1.continuousOn
    hs.2.2.1.continuousOn hs.2.2.2.2.2.2.1 ht.le le_rfl x a)

end RVM

end

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma retarded_phase_translate_integral {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : Phase → W) (t : ℝ) (x : Vec) :
    (∫ p : Phase, f (x+p.1,p.2) ∂((volume.restrict (ball (0:Vec) t)).prod volume)) =
      ∫ p in retardedPhaseDomain t x, f p := by
  have hm : ((volume.restrict (ball (0:Vec) t)).prod volume : Measure Phase)=
      volume.restrict (ball (0:Vec) t ×ˢ (univ : Set Vec)) := by
    simpa only [Measure.restrict_univ,← Measure.volume_eq_prod] using
      (Measure.prod_restrict (μ:=(volume:Measure Vec)) (ν:=(volume:Measure Vec))
        (ball (0:Vec) t) univ)
  rw [hm,← integral_indicator (measurableSet_ball.prod MeasurableSet.univ)]
  rw [← integral_indicator (isOpen_retardedPhaseDomain t x).measurableSet,
    ← integral_add_left_eq_self ((retardedPhaseDomain t x).indicator f) (x, (0:Vec))]
  apply integral_congr_ae
  have hne : ∀ᵐ p : Phase ∂volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (volume.ae_ne (0:Vec))
  filter_upwards [hne] with p hp
  by_cases hb : ‖p.1‖<t
  · rw [indicator_of_mem (show p∈ball (0:Vec) t ×ˢ (univ : Set Vec) from
        ⟨mem_ball_zero_iff.mpr hb,mem_univ _⟩),
      indicator_of_mem (show (x,(0:Vec))+p∈retardedPhaseDomain t x from by
        change 0<‖x-(x+p.1)‖ ∧ ‖x-(x+p.1)‖<t
        rw [show x-(x+p.1) = -p.1 by abel,norm_neg]
        exact ⟨norm_pos_iff.mpr hp,hb⟩)]
    congr 1
    ext <;> simp
  · rw [indicator_of_notMem (show p∉ball (0:Vec) t ×ˢ (univ : Set Vec) from by
        intro h; exact hb (mem_ball_zero_iff.mp h.1)),
      indicator_of_notMem (show (x,(0:Vec))+p∉retardedPhaseDomain t x from by
        intro h
        apply hb
        simpa only [retardedPhaseDomain,mem_ofPred_eq,Prod.fst_add,
          show x-(x+p.1) = -p.1 by abel,norm_neg] using h.2)]

lemma retarded_phase_translate_integrable_iff {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : Phase → W) (t : ℝ) (x : Vec) :
    Integrable (fun p : Phase => f (x+p.1,p.2)) ((volume.restrict (ball (0:Vec) t)).prod volume) ↔
      IntegrableOn f (retardedPhaseDomain t x) := by
  have hm : ((volume.restrict (ball (0:Vec) t)).prod volume : Measure Phase)=
      volume.restrict (ball (0:Vec) t ×ˢ (univ : Set Vec)) := by
    simpa only [Measure.restrict_univ,← Measure.volume_eq_prod] using
      (Measure.prod_restrict (μ:=(volume:Measure Vec)) (ν:=(volume:Measure Vec))
        (ball (0:Vec) t) univ)
  have heq : (ball (0:Vec) t ×ˢ (univ : Set Vec)).indicator (fun p : Phase => f (x+p.1,p.2)) =ᵐ[volume]
      (fun p : Phase => (retardedPhaseDomain t x).indicator f ((x,(0:Vec))+p)) := by
    have hne : ∀ᵐ p : Phase ∂volume, p.1≠0 :=
      Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (volume.ae_ne (0:Vec))
    filter_upwards [hne] with p hp
    by_cases hb : ‖p.1‖<t
    · rw [indicator_of_mem (show p∈ball (0:Vec) t ×ˢ (univ : Set Vec) from
          ⟨mem_ball_zero_iff.mpr hb,mem_univ _⟩),
        indicator_of_mem (show (x,(0:Vec))+p∈retardedPhaseDomain t x from by
          change 0<‖x-(x+p.1)‖ ∧ ‖x-(x+p.1)‖<t
          rw [show x-(x+p.1) = -p.1 by abel,norm_neg]
          exact ⟨norm_pos_iff.mpr hp,hb⟩)]
      congr 1
      ext <;> simp
    · rw [indicator_of_notMem (show p∉ball (0:Vec) t ×ˢ (univ : Set Vec) from by
          intro h; exact hb (mem_ball_zero_iff.mp h.1)),
        indicator_of_notMem (show (x,(0:Vec))+p∉retardedPhaseDomain t x from by
          intro h
          apply hb
          simpa only [retardedPhaseDomain,mem_ofPred_eq,Prod.fst_add,
            show x-(x+p.1) = -p.1 by abel,norm_neg] using h.2)]
  rw [hm]
  change IntegrableOn (fun p : Phase => f (x+p.1,p.2)) (ball (0:Vec) t ×ˢ (univ : Set Vec)) volume ↔ _
  rw [← integrable_indicator_iff (μ:=volume) (measurableSet_ball.prod MeasurableSet.univ),
    ← integrable_indicator_iff (μ:=volume) (isOpen_retardedPhaseDomain t x).measurableSet]
  constructor
  · intro hi
    have hcomp : Integrable (fun p : Phase => (retardedPhaseDomain t x).indicator f ((x,(0:Vec))+p)) volume := hi.congr heq
    have hh := hcomp.comp_add_left (-(x,(0:Vec)))
    simpa only [add_neg_cancel_left] using hh
  · intro hi
    exact (hi.comp_add_left (x,(0:Vec))).congr heq.symm

def physicalPhaseForce (s : Solution) (t : ℝ) (x a : Vec) (p : Phase) : Vec :=
  forceTransportKernel (coneRadius x p.1) (coneDirection x p.1) a p.2+
    forceSourceKernel (coneRadius x p.1) (coneDirection x p.1) a p.2
      (fderiv ℝ velocity p.2 (s.E (t-coneRadius x p.1,p.1)+
        cross (velocity p.2) (s.B (t-coneRadius x p.1,p.1))))

lemma retardedForceKernel_phase (s : Solution) (t : ℝ) (x a : Vec) (p : Phase) :
    retardedForceKernel s t x a p.1 p.2=
      s.f (t-‖x-p.1‖,p) • physicalPhaseForce s t x a p := rfl

lemma integrableOn_physical_force_phase {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x a : Vec) :
    IntegrableOn (fun p : Phase => s.f (t-‖x-p.1‖,p) • physicalPhaseForce s t x a p)
      (retardedPhaseDomain t x) := by
  apply (retarded_phase_translate_integrable_iff _ t x).mp
  exact integrable_joint_retardedForceKernel hf hE hB hc ht le_rfl x a

lemma classical_retarded_force_phase_domain {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ p in retardedPhaseDomain t x,
        s.f (t-‖x-p.1‖,p) • physicalPhaseForce s t x a p := by
  rw [classical_retarded_force_phase_integral hs hm ht,
    retarded_phase_translate_integral (fun p => retardedForceKernel s t x a p.1 p.2) t x]
  rfl

lemma classical_retarded_force_label_integral {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {T t : ℝ}
    (F : PhaseFlowOn s.E s.B T) (ht : t∈Icc 0 T) (ht0 : 0<t) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ z in initialConeLabels t x,
        (1-dot (coneDirection x (F.retardedSource ht x z).1)
          (velocity (F.retardedSource ht x z).2))⁻¹ •
          (d.f₀ z • physicalPhaseForce s t x a (F.retardedSource ht x z)) := by
  rw [classical_retarded_force_phase_domain hs hm ht0]
  congr 2
  have he := hs.energyPrefix (ht.1.trans ht.2)
  rw [F.retarded_transport_integral he.f_smooth he.vlasov ht x]
  apply setIntegral_congr_fun (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
  intro z hz
  change _ • (s.f (0,z) • _) = _ • (d.f₀ z • _)
  rw [hs.2.2.2.2.2.2.2.2.1]
  rfl

lemma physical_force_branch_kernel (r : ℝ) (n a v b : Vec)
    (hr : r≠0) (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    ((1-dot n (velocity v))/(1-dot n a)) •
      ((1-dot n (velocity v))⁻¹ •
        (forceTransportKernel r n a v+forceSourceKernel r n a v b)) =
      signedForceKernel r a (velocity v) n b := by
  rw [← physical_force_kernel r n a v b hr hn]
  rw [show (1-dot n (velocity v))⁻¹ • ((1-dot n (velocity v)) •
      receiverQ a n (physicalElectricKernel r n (velocity v) b)) =
      receiverQ a n (physicalElectricKernel r n (velocity v) b) by
        rw [smul_smul,inv_mul_cancel₀ (cone_denom_pos v n hn).ne',one_smul]]
  exact physical_kernel_signed_transform r n (velocity v) b a hr
    (cone_denom_pos v n hn).ne' hD

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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

abbrev ConeKernelState := (ℝ×ℝ)×(Vec×Phase)
def coneKernelDomain (T : ℝ) : Set ConeKernelState :=
  (Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T) ×ˢ (sphere (0:Vec) 1 ×ˢ univ)

lemma EnergyPrefix.uniform_cone_kernel_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {A : ConeKernelState→Vec}
    (hA : ContinuousOn A (coneKernelDomain T)) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc 0 T, ∀ σ∈Icc 0 T, ∀ n : Vec, ‖n‖=1 →
      ∀ z : Phase, ‖s.f (σ,z) • A ((t,σ),(n,z))‖≤C := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  let S : Set ConeKernelState := (Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T) ×ˢ (sphere (0:Vec) 1 ×ˢ K)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).prod ((isCompact_sphere _ _).prod hK)
  have hsub : S⊆coneKernelDomain T := fun p hp=>⟨hp.1,hp.2.1,mem_univ _⟩
  have hf : ContinuousOn (fun p : ConeKernelState=>s.f (p.1.2,p.2.2)) S :=
    hs.f_smooth.continuousOn.comp
      (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn
      (fun _ hp=>⟨hp.1.2,mem_univ _⟩)
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn (hf.smul (hA.mono hsub))
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht σ hσ n hn z
  by_cases hz : z∈K
  · exact (hC ((t,σ),(n,z)) ⟨⟨ht,hσ⟩,⟨by simpa only [mem_sphere,dist_zero_right] using hn,hz⟩⟩).trans (le_max_left _ _)
  · have hf0 : s.f (σ,z)=0 := by
      by_contra hne
      exact hz (hzero σ hσ (subset_tsupport _ hne))
    simp only [hf0,zero_smul,norm_zero]
    exact le_max_right _ _

def normalisedSignedForce (r : ℝ) (a u n b : Vec) : Vec :=
  ((1-dot n u)/(1-dot n a)) • receiverQ a n (normalisedElectricKernel r n u b)

lemma normalisedSignedForce_eq {r : ℝ} (a u n b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) (hD : 1-dot n a≠0) :
    normalisedSignedForce r a u n b=r^2 • signedForceKernel r a u n b := by
  rw [normalisedSignedForce,normalisedElectricKernel_eq hr,receiverQ_smul,smul_comm]
  congr 1
  exact physical_kernel_signed_transform _ _ _ _ _ hr hd hD

lemma continuousOn_normalisedSignedForce {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n b : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hb : ContinuousOn b S)
    (hd : ∀p∈S,1-dot (n p) (u p)≠0) (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>normalisedSignedForce (r p) (a p) (u p) (n p) (b p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  exact ((continuousOn_const.sub (hdot hn hu)).div
    (continuousOn_const.sub (hdot hn ha)) hD).smul
      (continuousOn_receiverQ ha hn (continuousOn_normalisedElectricKernel hr hn hu hb hd))

def sourceAcceleration (s : Solution) (p : ℝ×Phase) : Vec :=
  fderiv ℝ velocity p.2.2 (s.E (p.1,p.2.1)+cross (velocity p.2.2) (s.B (p.1,p.2.1)))

lemma EnergyPrefix.continuousOn_sourceAcceleration {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) :
    ContinuousOn (sourceAcceleration s) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hp : Continuous (fun p : ℝ×Phase=>(p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have hE : ContinuousOn (fun p : ℝ×Phase=>s.E (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.E_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hB : ContinuousOn (fun p : ℝ×Phase=>s.B (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.B_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hu := (contDiff_velocity (k:=1)).continuous.comp (continuous_snd.snd : Continuous (fun p : ℝ×Phase=>p.2.2))
  exact (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp_continuousOn
    continuous_snd.snd.continuousOn).clm_apply
      (hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hB)))

lemma PhaseFlowOn.normalised_source_force_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (fun p : ConeKernelState=>normalisedSignedForce (p.1.1-p.1.2)
      (velocity (F.flow zX p.1.1).2) (velocity p.2.2.2) p.2.1
      (sourceAcceleration s (p.1.2,p.2.2))) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hb : ContinuousOn (fun p : ConeKernelState=>sourceAcceleration s (p.1.2,p.2.2)) (coneKernelDomain T) :=
    (hs.continuousOn_sourceAcceleration).comp
    (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn (fun _ hp=>⟨hp.1.2,mem_univ _⟩)
  refine continuousOn_normalisedSignedForce (continuous_fst.fst.sub continuous_fst.snd).continuousOn
    ha hu.continuousOn continuous_snd.fst.continuousOn hb ?_ ?_
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

lemma PhaseFlowOn.source_force_inverse_square_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc 0 T, ∀ σ∈Icc 0 T, σ<t →
      ∀ n : Vec, ‖n‖=1 → ∀ z : Phase,
      ‖s.f (σ,z) • signedForceKernel (t-σ) (velocity (F.flow zX t).2)
        (velocity z.2) n (sourceAcceleration s (σ,z))‖≤C*(t-σ)⁻¹^2 := by
  obtain ⟨C,hC,hb⟩ := hs.uniform_cone_kernel_bound (F.normalised_source_force_continuousOn hs zX)
  refine ⟨C,hC,?_⟩
  intro t ht σ hσ hst n hn z
  have hr : t-σ≠0 := (sub_pos.mpr hst).ne'
  have hh := hb t ht σ hσ n hn z
  rw [normalisedSignedForce_eq _ _ _ _ hr (cone_denom_pos _ _ hn).ne' (cone_denom_pos _ _ hn).ne',
    smul_comm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hh
  have hh' : ‖s.f (σ,z) • signedForceKernel (t-σ) (velocity (F.flow zX t).2)
      (velocity z.2) n (sourceAcceleration s (σ,z))‖≤C/(t-σ)^2 :=
    (le_div_iff₀ (sq_pos_of_ne_zero hr)).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv,inv_pow] using hh'

def arrivalPhaseDomain (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set (ℝ×Phase) :=
  (fun p=>(p.1,p.2.1)) ⁻¹' arrivalDomain α zX T

def arrivalKernelState (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (p : ℝ×Phase) : ConeKernelState :=
  ((arrivalTime α zX T (p.1,p.2.1),p.1),(arrivalDirection α zX T (p.1,p.2.1),p.2))

lemma PhaseFlowOn.isOpen_arrivalPhaseDomain {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) : IsOpen (arrivalPhaseDomain F.flow zX T) :=
  (F.isOpen_arrivalDomain zX).preimage (continuous_fst.prodMk continuous_snd.fst)

lemma PhaseFlowOn.arrivalKernelState_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈arrivalPhaseDomain F.flow zX T) :
    arrivalKernelState F.flow zX T p∈coneKernelDomain T := by
  have ht := F.arrival_time_spec zX hp
  exact ⟨⟨⟨(hp.1.1.trans ht.1.1).le,ht.1.2.le⟩,Ioo_subset_Icc_self hp.1⟩,
    ⟨by simpa only [arrivalKernelState,mem_sphere,dist_zero_right] using F.norm_arrivalDirection zX hp,mem_univ _⟩⟩

lemma PhaseFlowOn.arrivalKernelState_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (arrivalKernelState F.flow zX T) (arrivalPhaseDomain F.flow zX T) := by
  intro p hp
  have hc : ContinuousAt (fun p : ℝ×Phase=>(p.1,p.2.1)) p :=
    continuousAt_fst.prodMk continuousAt_snd.fst
  exact (((F.arrivalTime_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1)) hc).prodMk continuousAt_fst).prodMk
    (((F.arrivalDirection_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1)) hc).prodMk continuousAt_snd) |>.continuousWithinAt

def arrivalConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) : ℝ×Phase→Vec :=
  (arrivalPhaseDomain α zX T).indicator (fun p=>
    (arrivalRadius α zX T (p.1,p.2.1))⁻¹^2 • (s.f p • A (arrivalKernelState α zX T p)))

lemma PhaseFlowOn.measurable_arrivalConeKernel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Measurable (arrivalConeKernel s F.flow zX T A) := by
  classical
  have hr : ContinuousOn (fun p : ℝ×Phase=>arrivalRadius F.flow zX T (p.1,p.2.1))
      (arrivalPhaseDomain F.flow zX T) := by
    intro p hp
    exact ((F.arrivalRadius_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1))
      (continuousAt_fst.prodMk continuousAt_snd.fst)).continuousWithinAt
  have hr0 : ∀p∈arrivalPhaseDomain F.flow zX T,
      arrivalRadius F.flow zX T (p.1,p.2.1)≠0 := fun p hp=>
    (sub_pos.mpr (F.arrival_time_spec zX hp).1.1).ne'
  have hf : ContinuousOn s.f (arrivalPhaseDomain F.flow zX T) :=
    hs.f_smooth.continuousOn.mono (fun _ hp=>⟨Ioo_subset_Icc_self hp.1,mem_univ _⟩)
  have hc := ((hr.inv₀ hr0).pow 2).smul (hf.smul
    (hA.comp (F.arrivalKernelState_continuousOn zX) (fun _ hp=>F.arrivalKernelState_mem zX hp)))
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_arrivalPhaseDomain zX).measurableSet

lemma PhaseFlowOn.arrivalConeKernel_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Integrable (arrivalConeKernel s F.flow zX T A) := by
  classical
  obtain ⟨K,hK,hzero⟩ := hs.compact
  obtain ⟨C,hC,hb⟩ := hs.uniform_cone_kernel_bound hA
  apply F.source_cone_integrable_of_bound zX (hK.image continuous_snd)
    (F.measurable_arrivalConeKernel hs zX hA).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p∈arrivalPhaseDomain F.flow zX T
  · have hspec := F.arrival_time_spec zX hp
    have ht : arrivalTime F.flow zX T (p.1,p.2.1)∈Icc 0 T :=
      ⟨(hp.1.1.trans hspec.1.1).le,hspec.1.2.le⟩
    have he : (p.1,p.2.1)∈arrivalDomain F.flow zX T := hp
    rw [arrivalConeKernel,indicator_of_mem hp,phaseArrivalMajorant,arrivalInverseSquare,
      indicator_of_mem he]
    by_cases hv : p.2.2∈Prod.snd '' K
    · rw [indicator_of_mem hv,mul_one,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh := hb _ ht _ (Ioo_subset_Icc_self hp.1) _ (F.norm_arrivalDirection zX hp) p.2
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (mul_comm _ _)
    · have hf0 : s.f p=0 := by
        by_contra hne
        exact hv ⟨p.2,hzero _ (Ioo_subset_Icc_self hp.1) (subset_tsupport _ hne),rfl⟩
      simp only [hf0,zero_smul,smul_zero,norm_zero,indicator_of_notMem hv,mul_zero,le_refl]
  · have he : (p.1,p.2.1)∉arrivalDomain F.flow zX T := hp
    simp only [arrivalConeKernel,indicator_of_notMem hp,norm_zero,phaseArrivalMajorant,
      arrivalInverseSquare,indicator_of_notMem he,zero_mul,mul_zero,le_refl]

def actualArrivalSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (arrivalPhaseDomain α zX T).indicator (fun p=>s.f p •
    signedForceKernel (arrivalRadius α zX T (p.1,p.2.1))
      (velocity (α zX (arrivalTime α zX T (p.1,p.2.1))).2)
      (velocity p.2.2) (arrivalDirection α zX T (p.1,p.2.1)) (sourceAcceleration s p))

lemma PhaseFlowOn.actualArrivalSignedForce_eq {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    actualArrivalSignedForce s F.flow zX T=arrivalConeKernel s F.flow zX T
      (fun p=>normalisedSignedForce (p.1.1-p.1.2)
        (velocity (F.flow zX p.1.1).2) (velocity p.2.2.2) p.2.1
        (sourceAcceleration s (p.1.2,p.2.2))) := by
  classical
  funext p
  by_cases hp : p∈arrivalPhaseDomain F.flow zX T
  · have hr : arrivalRadius F.flow zX T (p.1,p.2.1)≠0 :=
      (sub_pos.mpr (F.arrival_time_spec zX hp).1.1).ne'
    have hn := F.norm_arrivalDirection zX hp
    have hd := (cone_denom_pos p.2.2 _ hn).ne'
    have hD := (cone_denom_pos (F.flow zX (arrivalTime F.flow zX T (p.1,p.2.1))).2 _ hn).ne'
    simp only [actualArrivalSignedForce,arrivalConeKernel,indicator_of_mem hp,arrivalKernelState]
    change _=(arrivalRadius F.flow zX T (p.1,p.2.1))⁻¹^2 •
      (s.f p • normalisedSignedForce (arrivalRadius F.flow zX T (p.1,p.2.1)) _ _ _ _)
    rw [normalisedSignedForce_eq _ _ _ _ hr hd hD,smul_comm (s.f p),smul_smul,
      ←mul_pow,inv_mul_cancel₀ hr,one_pow,one_smul]
  · simp only [actualArrivalSignedForce,arrivalConeKernel,indicator_of_notMem hp]

lemma PhaseFlowOn.actualArrivalSignedForce_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualArrivalSignedForce s F.flow zX T) := by
  rw [F.actualArrivalSignedForce_eq zX]
  exact F.measurable_arrivalConeKernel hs zX (F.normalised_source_force_continuousOn hs zX)

lemma PhaseFlowOn.actualArrivalSignedForce_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Integrable (actualArrivalSignedForce s F.flow zX T) := by
  rw [F.actualArrivalSignedForce_eq zX]
  exact F.arrivalConeKernel_integrable hs zX (F.normalised_source_force_continuousOn hs zX)

lemma PhaseFlowOn.actualArrivalSignedForce_integrable_weight {s : Solution} {T C : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {ψ : ℝ×Phase→ℝ} (hψ : Measurable ψ) (hb : ∀p, |ψ p|≤C) :
    Integrable (fun p=>ψ p • actualArrivalSignedForce s F.flow zX T p) := by
  apply (F.actualArrivalSignedForce_integrable hs zX).bdd_smul C hψ.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p=>by simpa only [Real.norm_eq_abs] using hb p)

end RVM

end

end OAI
