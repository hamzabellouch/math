import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.EnergyBump
import OAI.Analysis.VlasovMaxwell.Flow.WithinFlow

namespace OAI

noncomputable section

section
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
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def retardedPhaseDomain (t : ℝ) (x : Vec) : Set Phase :=
  {z | 0 < ‖x-z.1‖ ∧ ‖x-z.1‖ < t}

def initialConeLabels (t : ℝ) (x : Vec) : Set Phase := {z | ‖x-z.1‖ < t}

lemma isOpen_retardedPhaseDomain (t : ℝ) (x : Vec) : IsOpen (retardedPhaseDomain t x) :=
  (isOpen_lt continuous_const ((continuous_const.sub continuous_fst).norm)).inter
    (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const)

lemma retarded_emission_mem {T t : ℝ} {x : Vec} {z : Phase} (ht : t ≤ T)
    (hz : z ∈ retardedPhaseDomain t x) : t-‖x-z.1‖ ∈ Ioo 0 T := by
  constructor <;> linarith [hz.1,hz.2]

lemma PhaseFlowOn.retarded_injective {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (ht : t ≤ T) (x : Vec) :
    InjOn (retardedLabel F.flow t x) (retardedPhaseDomain t x) := by
  intro a ha b hb hab
  have hsa := (retarded_emission_mem ht ha)
  have hsb := (retarded_emission_mem ht hb)
  let z := retardedLabel F.flow t x a
  have hfa : F.flow z (t-‖x-a.1‖) = a := F.flow_inversePhase (Ioo_subset_Icc_self hsa) a
  have hfb : F.flow z (t-‖x-b.1‖) = b := by
    change F.flow (retardedLabel F.flow t x a) (t-‖x-b.1‖)=b
    rw [hab]
    exact F.flow_inversePhase (Ioo_subset_Icc_self hsb) b
  have he : t-‖x-a.1‖=t-‖x-b.1‖ := by
    apply (F.emission_strictMono hT z x).injOn (Ioo_subset_Icc_self hsa) (Ioo_subset_Icc_self hsb)
    dsimp only
    rw [hfa,hfb]
    ring
  rw [← hfa,← hfb,he]

lemma PhaseFlowOn.exists_emission {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) {z : Phase} (hz : z ∈ initialConeLabels t x) :
    ∃! s : ℝ, s ∈ Icc 0 t ∧ s+‖x-(F.flow z s).1‖=t := by
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hc : ContinuousOn (fun s => s+‖x-(F.flow z s).1‖) (Icc 0 t) :=
    continuousOn_id.add ((continuousOn_const.sub ((F.continuousOn_time z).mono hsub).fst).norm)
  have hzero : 0+‖x-(F.flow z 0).1‖ < t := by simpa only [F.initial,zero_add,initialConeLabels,mem_ofPred_eq] using hz
  have hend : t ≤ t+‖x-(F.flow z t).1‖ := le_add_of_nonneg_right (norm_nonneg _)
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc ht.1 hc ⟨hzero.le,hend⟩
  refine ⟨s,⟨hs,he⟩,?_⟩
  intro r hr
  apply (F.emission_strictMono (ht.1.trans ht.2) z x).injOn (hsub hr.1) (hsub hs)
  exact hr.2.trans he.symm

lemma PhaseFlowOn.retarded_image {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) :
    retardedLabel F.flow t x '' retardedPhaseDomain t x =
      initialConeLabels t x \ {z : Phase | (F.flow z t).1=x} := by
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    let z := retardedLabel F.flow t x a
    let s := t-‖x-a.1‖
    have hs : s ∈ Ioo 0 T := retarded_emission_mem ht.2 ha
    have hst : s < t := by dsimp [s]; linarith [ha.1]
    have hf : F.flow z s=a := F.flow_inversePhase (Ioo_subset_Icc_self hs) a
    have he : s+‖x-(F.flow z s).1‖=t := by rw [hf]; dsimp [s]; ring
    have hm := F.emission_strictMono (ht.1.trans ht.2) z x
    constructor
    · have hh := hm ⟨le_rfl,ht.1.trans ht.2⟩ (Ioo_subset_Icc_self hs) hs.1
      dsimp only at hh
      rw [F.initial,zero_add,he] at hh
      exact hh
    · intro htip
      have hh := hm (Ioo_subset_Icc_self hs) ht hst
      dsimp only at hh
      change (F.flow z t).1=x at htip
      rw [he,htip,sub_self,norm_zero,add_zero] at hh
      exact (lt_irrefl t) hh
  · rintro ⟨hz,hnot⟩
    obtain ⟨s,⟨hs,he⟩,_⟩ := F.exists_emission ht x hz
    have hs₀ : 0 < s := by
      by_contra h
      have hs' : s=0 := le_antisymm (le_of_not_gt h) hs.1
      rw [hs',F.initial,zero_add] at he
      exact (ne_of_lt hz) he
    have hst : s < t := by
      by_contra h
      have hs' : s=t := le_antisymm hs.2 (le_of_not_gt h)
      have hn : ‖x-(F.flow z t).1‖=0 := by rw [hs'] at he; linarith
      exact hnot (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    have htime : t-‖x-(F.flow z s).1‖=s := by linarith
    refine ⟨F.flow z s,⟨?_,?_⟩,?_⟩
    · linarith
    · linarith
    · change inversePhase F.flow (t-‖x-(F.flow z s).1‖,F.flow z s)=z
      rw [htime]
      exact F.inversePhase_flow hsT z

def VlasovOn (f : Particle) (E B : Field) (T : ℝ) : Prop :=
  ∀ t ∈ Ioo 0 T, ∀ x v,
    deriv (fun r => f (r,x,v)) t +
      (∑ i : Fin 3, velocity v i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, (E (t,x)+cross (velocity v) (B (t,x))) i *
        spatialPartial (fun w => f (t,x,w)) v i) = 0

lemma PhaseFlowOn.transport {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    f (t,F.flow z t) = f (0,z) := by
  rcases ht.1.eq_or_lt with h | h
  · simp only [← h,F.initial]
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hc : ContinuousOn (fun s => f (s,F.flow z s)) (Icc 0 t) :=
    hf.continuousOn.comp (continuousOn_id.prodMk ((F.continuousOn_time z).mono hsub))
      (fun _ hs => ⟨hsub hs,mem_univ _⟩)
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => f (r,F.flow z r)) (0 : ℝ) s := by
    intro s hs
    have hsT : s ∈ Ioo 0 T := ⟨hs.1,hs.2.trans_le ht.2⟩
    have hdiff : DifferentiableAt ℝ f (s,F.flow z s) :=
      ((hf (s,F.flow z s) ⟨Ioo_subset_Icc_self hsT,mem_univ _⟩).contDiffAt
        (prod_mem_nhds (Icc_mem_nhds hsT.1 hsT.2) univ_mem)).differentiableAt (by simp)
    have hode := (F.ode z s (Ioo_subset_Icc_self hsT)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)
    have hh := hasDerivAt_particle_along_curve (X := fun r => (F.flow z r).1)
      (V := fun r => (F.flow z r).2) hdiff hode.fst hode.snd
    simpa only [lorentzField,lorentzPhase,heq s hsT] using hh
  obtain ⟨r,_,he⟩ := exists_hasDerivAt_eq_slope (fun s => f (s,F.flow z s)) (fun _ => 0) h hc hd
  have hnum : f (t,F.flow z t)-f (0,F.flow z 0)=0 :=
    (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr (ne_of_gt h))
  simpa only [F.initial] using sub_eq_zero.mp hnum

lemma PhaseFlowOn.transport_inverse {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    f (t,z) = f (0,inversePhase F.flow (t,z)) := by
  have hh := F.transport hf heq ht (inversePhase F.flow (t,z))
  simpa only [F.flow_inversePhase ht] using hh

lemma PhaseFlowOn.transport_nonneg {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) (hzero : ∀ z, 0 ≤ f (0,z))
    {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) : 0 ≤ f (t,z) := by
  rw [F.transport_inverse hf heq ht z]
  exact hzero _

lemma PhaseFlowOn.transport_integral {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ z, f (t,z) = ∫ z, f (0,z) := by
  rw [← F.integral_comp ht (fun z => f (t,z))]
  exact integral_congr_ae (Filter.Eventually.of_forall (F.transport hf heq ht))
end RVM
end

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
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.retarded_integral {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Phase → G) :
    ∫ z in initialConeLabels t x, g z =
      ∫ a in retardedPhaseDomain t x,
        (1-dot (‖x-a.1‖⁻¹ • (x-a.1)) (velocity a.2)) • g (retardedLabel F.flow t x a) := by
  have hx (a : Phase) (ha : a ∈ retardedPhaseDomain t x) : x ≠ a.1 :=
    sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt ha.1))
  have hd : ∀ a ∈ retardedPhaseDomain t x,
      HasFDerivWithinAt (retardedLabel F.flow t x)
        (fderiv ℝ (retardedLabel F.flow t x) a) (retardedPhaseDomain t x) a := by
    intro a ha
    obtain ⟨D,_,hD⟩ := F.retarded_differential x a (retarded_emission_mem ht.2 ha) (hx a ha)
    exact hD.hasFDerivAt.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  calc
    _ = ∫ z in retardedLabel F.flow t x '' retardedPhaseDomain t x, g z := by
      apply setIntegral_congr_set
      rw [F.retarded_image ht x]
      exact (sdiff_null_ae_eq_self (F.tip_null ht x)).symm
    _ = ∫ a in retardedPhaseDomain t x,
        |(fderiv ℝ (retardedLabel F.flow t x) a).det| • g (retardedLabel F.flow t x a) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume (isOpen_retardedPhaseDomain t x).measurableSet
        hd (F.retarded_injective (ht.1.trans ht.2) ht.2 x) g
    _ = _ := by
      apply setIntegral_congr_fun (isOpen_retardedPhaseDomain t x).measurableSet
      intro a ha
      dsimp only
      rw [F.retarded_jacobian x a (retarded_emission_mem ht.2 ha) (hx a ha),
        abs_of_pos (cone_deficit_positive (hx a ha) a.2)]

def PhaseFlowOn.retardedSource {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) (z : Phase) : Phase := by
  classical
  exact if hz : z ∈ initialConeLabels t x then F.flow z (F.exists_emission ht x hz).choose else z

lemma PhaseFlowOn.retardedSource_label {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) {a : Phase} (ha : a ∈ retardedPhaseDomain t x) :
    F.retardedSource ht x (retardedLabel F.flow t x a)=a := by
  classical
  let z := retardedLabel F.flow t x a
  have hz : z ∈ initialConeLabels t x := by
    have hi := F.retarded_image ht x
    have hh : z ∈ retardedLabel F.flow t x '' retardedPhaseDomain t x := ⟨a,ha,rfl⟩
    rw [hi] at hh
    exact hh.1
  have hs : t-‖x-a.1‖ ∈ Icc 0 t := ⟨by linarith [ha.2],by linarith [norm_nonneg (x-a.1)]⟩
  have hf : F.flow z (t-‖x-a.1‖)=a :=
    F.flow_inversePhase ⟨hs.1,hs.2.trans ht.2⟩ a
  have he := (F.exists_emission ht x hz).choose_spec.2 (t-‖x-a.1‖) ⟨hs,by rw [hf]; ring⟩
  change F.retardedSource ht x z=a
  rw [PhaseFlowOn.retardedSource,dite_eq_left hz,← he,hf]

lemma PhaseFlowOn.retarded_integral_inverse {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Phase → G) :
    ∫ a in retardedPhaseDomain t x, g a =
      ∫ z in initialConeLabels t x,
        (1-dot (‖x-(F.retardedSource ht x z).1‖⁻¹ • (x-(F.retardedSource ht x z).1))
          (velocity (F.retardedSource ht x z).2))⁻¹ • g (F.retardedSource ht x z) := by
  rw [F.retarded_integral ht x]
  apply setIntegral_congr_fun (isOpen_retardedPhaseDomain t x).measurableSet
  intro a ha
  dsimp only
  rw [F.retardedSource_label ht x ha,smul_smul,mul_inv_cancel₀,one_smul]
  exact ne_of_gt (cone_deficit_positive (sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt ha.1))) a.2)

lemma PhaseFlowOn.retarded_transport_integral {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) (ht : t ∈ Icc 0 T) (x : Vec)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (K : Phase → G) :
    ∫ a in retardedPhaseDomain t x, f (t-‖x-a.1‖,a) • K a =
      ∫ z in initialConeLabels t x,
        (1-dot (‖x-(F.retardedSource ht x z).1‖⁻¹ • (x-(F.retardedSource ht x z).1))
          (velocity (F.retardedSource ht x z).2))⁻¹ • (f (0,z) • K (F.retardedSource ht x z)) := by
  rw [F.retarded_integral ht x]
  apply setIntegral_congr_fun (isOpen_retardedPhaseDomain t x).measurableSet
  intro a ha
  dsimp only
  rw [F.retardedSource_label ht x ha,← mul_smul,mul_inv_cancel₀,one_smul]
  · congr 1
    exact F.transport_inverse hf heq (Ioo_subset_Icc_self (retarded_emission_mem ht.2 ha)) a
  · exact ne_of_gt (cone_deficit_positive (sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt ha.1))) a.2)

structure EnergyPrefix (s : Solution) (T : ℝ) : Prop where
  f_smooth : ContDiffOn ℝ 1 s.f (Icc 0 T ×ˢ (univ : Set Phase))
  E_smooth : ContDiffOn ℝ 1 s.E (Icc 0 T ×ˢ (univ : Set Vec))
  B_smooth : ContDiffOn ℝ 1 s.B (Icc 0 T ×ˢ (univ : Set Vec))
  nonnegative : ∀ t ∈ Icc 0 T, ∀ z, 0 ≤ s.f (t,z)
  E_L2 : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => s.E (t,x))
  B_L2 : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => s.B (t,x))
  compact : ∃ K : Set Phase, IsCompact K ∧ ∀ t ∈ Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K
  vlasov : VlasovOn s.f s.E s.B T
  maxwell : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun r => s.E (r,x)) t - curl (fun y => s.B (t,y)) x = -current (fun z => s.f (t,z)) x ∧
    deriv (fun r => s.B (r,x)) t + curl (fun y => s.E (t,y)) x = 0

namespace EnergyPrefix
variable {s : Solution} {T : ℝ}

lemma differentiable_particle (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (z : Phase) :
    DifferentiableAt ℝ s.f (t,z) :=
  (hs.f_smooth.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)).differentiableAt (by simp)

lemma differentiable_field {F : Field} (hF : ContDiffOn ℝ 1 F (Icc 0 T ×ˢ (univ : Set Vec)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) : DifferentiableAt ℝ F (t,x) :=
  (hF.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)).differentiableAt (by simp)

lemma local_data (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec), IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime s.f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime s.f (p,v)=0 := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  let U : Set (ℝ × Vec) := {p | p.1 ∈ Ioo 0 T}
  refine ⟨U,Prod.snd '' K,isOpen_Ioo.preimage continuous_fst,hK.image continuous_snd,ht,?_,?_⟩
  · exact hs.f_smooth.comp contDiff_reassociate.contDiffOn
      (fun p hp => ⟨Ioo_subset_Icc_self hp.1,mem_univ _⟩)
  · intro p hp v hv
    by_contra hn
    have hh : (p.2,v) ∈ tsupport (fun z => s.f (p.1,z)) := subset_tsupport _ hn
    exact hv ⟨(p.2,v),hzero p.1 (Ioo_subset_Icc_self hp) hh,rfl⟩

lemma spacetime_vlasov (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x v : Vec) :
    fderiv ℝ (particleBySpacetime s.f) ((t,x),v)
      ((1,velocity v),s.E (t,x)+cross (velocity v) (s.B (t,x)))=0 := by
  rw [fderiv_particleBySpacetime (hs.differentiable_particle ht (x,v)),
    full_directional_derivative (hs.differentiable_particle ht (x,v))]
  exact hs.vlasov t ht x v

lemma particle_energy_balance (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    fderiv ℝ (fun p : ℝ × Vec => ∫ v : Vec, q v * s.f (p.1,p.2,v)) (t,x) (1,0) +
      ∑ i : Fin 3, fderiv ℝ (fun p : ℝ × Vec => ∫ v : Vec, v i * s.f (p.1,p.2,v))
        (t,x) (0,basis i) = dot (s.E (t,x)) (current (fun z => s.f (t,z)) x) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    hs.local_data ht x
  exact particle_energy_balance_param (s.E (t,x)) (s.B (t,x)) hU hK hp hF hzero
    (hs.spacetime_vlasov ht x)

lemma particle_energy_flux_regular (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    ContDiffAt ℝ 1 (particleEnergy s) (t,x) ∧ ContDiffAt ℝ 1 (particleFlux s) (t,x) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    hs.local_data ht x
  constructor
  · apply (contDiffOn_integral_uniform_support (n := 1) hU hK
      ((contDiff_q.comp contDiff_snd).contDiffOn.mul hF)
      (fun p hp v hv => by simp only [hzero p hp v hv, mul_zero])).contDiffAt (hU.mem_nhds hp)
  · apply (contDiffOn_integral_uniform_support (n := 1) hU hK
      (hF.smul contDiff_snd.contDiffOn)
      (fun p hp v hv => by
        change particleBySpacetime s.f (p,v) • v = 0
        rw [hzero p hp v hv, zero_smul])).contDiffAt (hU.mem_nhds hp)

lemma particleFlux_component (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) (i : Fin 3) :
    particleFlux s (t,x) i = ∫ v : Vec, v i * s.f (t,x,v) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    hs.local_data ht x
  exact param_moment_component hK hp hF.continuousOn hzero i

lemma particle_energy_local (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    deriv (fun r => particleEnergy s (r,x)) t +
      divergence (fun y => particleFlux s (t,y)) x =
        dot (s.E (t,x)) (current (fun z => s.f (t,z)) x) := by
  obtain ⟨henergy,hflux⟩ := particle_energy_flux_regular hs ht x
  rw [deriv_time_slice (henergy.differentiableAt (by simp))]
  apply Eq.trans _ (particle_energy_balance hs ht x)
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hcomp : DifferentiableAt ℝ (fun p => particleFlux s p i) (t,x) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
      (hflux.differentiableAt (by simp))
  rw [spatialPartial_time_slice hcomp]
  have he : (fun p : ℝ × Vec => particleFlux s p i) =ᶠ[𝓝 (t,x)]
      (fun p => ∫ v : Vec, v i * s.f (p.1,p.2,v)) := by
    filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds ht] with p hp
    exact particleFlux_component hs hp p.2 i
  rw [he.fderiv_eq (𝕜 := ℝ)]

lemma local_energy_conservation (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    deriv (fun r => totalEnergy s (r,x)) t +
      divergence (fun y => totalFlux s (t,y)) x = 0 := by
  have hE := differentiable_field hs.E_smooth ht x
  have hB := differentiable_field hs.B_smooth ht x
  obtain ⟨henergy,hflux⟩ := particle_energy_flux_regular hs ht x
  obtain ⟨he,hb⟩ := hs.maxwell t ht x
  have hm := maxwell_energy_balance hE hB he hb
  have hp := particle_energy_local hs ht x
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

lemma velocity_slice (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => s.f (t,x,v)) ∧
      HasCompactSupport (fun v : Vec => s.f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hs.f_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ⟨ht,mem_univ _⟩)
  · obtain ⟨K,hK,hzero⟩ := hs.compact
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩

lemma particle_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.nonnegative t ht (x,v))

lemma particle_flux_bound (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    ‖particleFlux s (t,x)‖ ≤ particleEnergy s (t,x) := by
  obtain ⟨hf,hc⟩ := velocity_slice hs ht x
  have hi : Integrable (fun v : Vec => s.f (t,x,v) • v) :=
    (hf.continuous.smul continuous_id).integrable_of_hasCompactSupport hc.smul_right
  have hqi : Integrable (fun v : Vec => q v * s.f (t,x,v)) :=
    ((contDiff_q (k := 1)).continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  calc
    _ ≤ ∫ v : Vec, ‖s.f (t,x,v) • v‖ := norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono hi.norm hqi
      intro v
      have hp := hs.nonnegative t ht (x,v)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
      nlinarith [norm_lt_q v]

lemma total_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := particle_energy_nonneg hs ht x
  positivity

lemma total_flux_bound (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    ‖totalFlux s (t,x)‖ ≤ totalEnergy s (t,x) := by
  exact (norm_add_le _ _).trans
    (add_le_add (poynting_norm_le_energy (s.E (t,x)) (s.B (t,x)))
      (particle_flux_bound hs ht x))

lemma prefix_memLp {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : MemLp (fun x => F (t,x)) 2 volume := by
  obtain ⟨F₂,hc,heq⟩ := hF
  exact (Lp.memLp (F₂ t)).ae_eq (heq t ht)

lemma prefix_integrable_norm_sq {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : Integrable (fun x => ‖F (t,x)‖^2) := by
  have hm := prefix_memLp hF ht
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma prefix_continuous_integral_norm_sq {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Icc 0 T) := by
  obtain ⟨F₂,hc,heq⟩ := hF
  have hh : ∀ t ∈ Icc (0:ℝ) T, (∫ x : Vec, ‖F (t,x)‖^2) = ‖F₂ t‖^2 := by
    intro t ht
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq t ht] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  exact (hc.norm.pow 2).congr (fun t ht => hh t ht)

lemma particle_energy_continuous_slab (hs : EnergyPrefix s T) :
    ContinuousOn (particleEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, q v * s.f (p.1,p.2,v)) _
  apply continuousOn_integral_uniform_support (F := fun z : (ℝ × Vec) × Vec => q z.2 * s.f (z.1.1,z.1.2,z.2)) (hK.image continuous_snd)
  · apply ((contDiff_q (k := 1)).continuous.comp continuous_snd).continuousOn.mul
    apply hs.f_smooth.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
    intro z hz
    exact ⟨hz.1.1,mem_univ _⟩
  · intro p hp v hv
    have hf : s.f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hf,mul_zero]

lemma particle_energy_compact (hs : EnergyPrefix s T) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x ∉ K, particleEnergy s (t,x) = 0 := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  refine ⟨Prod.fst '' K,hK.image continuous_fst,?_⟩
  intro t ht x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  have hf : s.f (t,x,v) = 0 := by
    by_contra hn
    exact hx ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩
  simp only [hf,mul_zero, Pi.zero_apply]

lemma particle_energy_integrable (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x : Vec => particleEnergy s (t,x)) := by
  obtain ⟨K,hK,hz⟩ := particle_energy_compact hs
  have hc := (particle_energy_continuous_slab hs).comp_continuous
    (continuous_const.prodMk continuous_id)
    (fun x : Vec => show (t,x) ∈ Icc 0 T ×ˢ (univ : Set Vec) from ⟨ht,mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz t ht))

lemma total_energy_integrable (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x : Vec => totalEnergy s (t,x)) := by
  exact ((prefix_integrable_norm_sq hs.E_L2 ht).add
    (prefix_integrable_norm_sq hs.B_L2 ht)).div_const 2 |>.add
      (particle_energy_integrable hs ht)

lemma integrated_energy_continuous (hs : EnergyPrefix s T) :
    ContinuousOn (fun t => ∫ x : Vec, totalEnergy s (t,x)) (Icc 0 T) := by
  obtain ⟨K,hK,hz⟩ := particle_energy_compact hs
  have hp : ContinuousOn (fun t => ∫ x : Vec, particleEnergy s (t,x)) (Icc 0 T) :=
    continuousOn_integral_uniform_support hK
      (particle_energy_continuous_slab hs) hz
  have he := prefix_continuous_integral_norm_sq hs.E_L2
  have hb := prefix_continuous_integral_norm_sq hs.B_L2
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2+particleEnergy s (t,x)) =
    ((∫ x : Vec, ‖s.E (t,x)‖^2)+(∫ x : Vec, ‖s.B (t,x)‖^2))/2+
      (∫ x : Vec, particleEnergy s (t,x))
  calc
    _ = (∫ x : Vec, (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2)+
        (∫ x : Vec, particleEnergy s (t,x)) :=
      integral_add (((prefix_integrable_norm_sq hs.E_L2 ht).add
        (prefix_integrable_norm_sq hs.B_L2 ht)).div_const 2)
        (particle_energy_integrable hs ht)
    _ = _ := by
      rw [integral_div, integral_add (prefix_integrable_norm_sq hs.E_L2 ht)
        (prefix_integrable_norm_sq hs.B_L2 ht)]

lemma total_energy_regular (hs : EnergyPrefix s T) : ContDiffOn ℝ 1 (totalEnergy s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
  have hE := hs.E_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hB := hs.B_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hp : ContDiffOn ℝ 1 (particleEnergy s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
    intro p hp
    exact (particle_energy_flux_regular hs hp.1 p.2).1.contDiffWithinAt
  exact ((hE.norm_sq ℝ).add (hB.norm_sq ℝ)).div_const 2 |>.add hp

lemma total_flux_regular (hs : EnergyPrefix s T) : ContDiffOn ℝ 1 (totalFlux s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
  have hE := hs.E_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hB := hs.B_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hp : ContDiffOn ℝ 1 (particleFlux s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
    intro p hp
    exact (particle_energy_flux_regular hs hp.1 p.2).2.contDiffWithinAt
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (hE.prodMk hB)
    (fun _ _ => mem_univ _)).add hp

lemma deriv_weighted_energy (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x : Vec, g x * totalEnergy s (r,x))
      (∫ x : Vec, fderiv ℝ g x (totalFlux s (t,x))) t := by
  have hE := total_energy_regular hs
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × Vec => g p.2 * totalEnergy s p)
      (Ioo 0 T ×ˢ (univ : Set Vec)) := (hg.comp contDiff_snd).contDiffOn.mul hE
  have hz : ∀ r ∈ Ioo (0:ℝ) T, ∀ x ∉ tsupport g, g x * totalEnergy s (r,x) = 0 := by
    intro r _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support isOpen_Ioo hc ht hF hz
  have hi := fderiv_integral_uniform_support_apply isOpen_Ioo hc ht hF hz (1:ℝ)
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p : ℝ × Vec => g p.2 * totalEnergy s p) (t,x) (1,0) =
        -g x * divergence (fun y => totalFlux s (t,y)) x := by
    intro x
    have he := hE.contDiffAt (x := (t,x)) (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) ⟨ht,mem_univ x⟩)
    have heT : DifferentiableAt ℝ (fun r => totalEnergy s (r,x)) t :=
      DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := totalEnergy s)
        (he.differentiableAt (by simp))
        (differentiableAt_id.prodMk (differentiableAt_const x))
    have hgT : HasDerivAt (fun r => g x * totalEnergy s (r,x))
        (g x * deriv (fun r => totalEnergy s (r,x)) t) t :=
      heT.hasDerivAt.const_mul (g x)
    have hf := hF.contDiffAt (x := (t,x)) (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) ⟨ht,mem_univ x⟩)
    rw [← deriv_time_slice (hf.differentiableAt (by simp)), hgT.deriv]
    have hl := local_energy_conservation hs ht x
    rw [show deriv (fun r => totalEnergy s (r,x)) t =
      -divergence (fun y => totalFlux s (t,y)) x by linarith]
    ring
  have hS : ContDiff ℝ 1 (fun x => totalFlux s (t,x)) := by
    apply contDiffOn_univ.mp
    exact (total_flux_regular hs).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht,mem_univ x⟩)
  have hh : deriv (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t =
      ∫ x : Vec, fderiv ℝ g x (totalFlux s (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t 1 = _
    rw [hi]
    simp only [heq, neg_mul, integral_neg]
    rw [integral_mul_divergence hS hg hc, neg_neg]
  exact hh ▸ hd.differentiableAt.hasDerivAt

lemma total_energy_continuous_slab (hs : EnergyPrefix s T) :
    ContinuousOn (totalEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  exact ((hs.E_smooth.continuousOn.norm.pow 2).add
    (hs.B_smooth.continuousOn.norm.pow 2)).div_const 2 |>.add
      (particle_energy_continuous_slab hs)

lemma weighted_energy_continuous (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    :
    ContinuousOn (fun t => ∫ x : Vec, g x * totalEnergy s (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support hc
    ((hg.comp continuous_snd).continuousOn.mul (total_energy_continuous_slab hs))
  intro t _ x hx
  change g x * totalEnergy s (t,x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

lemma weighted_energy_deriv_bound (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ‖deriv (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t‖ ≤
      C * (∫ x : Vec, totalEnergy s (t,x)) := by
  rw [(deriv_weighted_energy hs hg hc ht).deriv]
  have hS : Continuous (fun x : Vec => totalFlux s (t,x)) := by
    apply ContinuousOn.comp_continuous (total_flux_regular hs).continuousOn
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
      apply integral_mono hi.norm ((total_energy_integrable hs (Ioo_subset_Icc_self ht)).const_mul C)
      intro x
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hb x) (total_flux_bound hs (Ioo_subset_Icc_self ht) x) (norm_nonneg _) hC)
    _ = _ := integral_const_mul _ _

lemma weighted_energy_increment_bound (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {C B : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hT : 0 ≤ T) (hB : ∀ t ∈ Icc 0 T, (∫ x : Vec, totalEnergy s (t,x)) ≤ B) :
    ‖(∫ x : Vec, g x * totalEnergy s (T,x)) - (∫ x : Vec, g x * totalEnergy s (0,x))‖ ≤ C * B * T := by
  rcases eq_or_lt_of_le hT with he | ht
  · subst T; simp
  let F : ℝ → ℝ := fun t => ∫ x : Vec, g x * totalEnergy s (t,x)
  have hcont : ContinuousOn F (Icc 0 T) := weighted_energy_continuous hs hg.continuous hc
  have hdiff : DifferentiableOn ℝ F (Ioo 0 T) := fun t ht =>
    (deriv_weighted_energy hs hg hc ht).differentiableAt.differentiableWithinAt
  obtain ⟨c,hcT,heq⟩ := exists_deriv_eq_slope F ht hcont hdiff
  have hder : ‖deriv F c‖ ≤ C * B :=
    (weighted_energy_deriv_bound hs hg hc hC hb hcT).trans
      (mul_le_mul_of_nonneg_left (hB c ⟨hcT.1.le,hcT.2.le⟩) hC)
  rw [heq, sub_zero, norm_div, Real.norm_of_nonneg hT] at hder
  exact (div_le_iff₀ ht).mp hder

theorem energy_conservation (hs : EnergyPrefix s T) (hT : 0 ≤ T) :
    (∫ x : Vec, totalEnergy s (T,x)) = ∫ x : Vec, totalEnergy s (0,x) := by
  obtain ⟨C,hC,hb⟩ := energyCutoff_deriv_bound
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).bddAbove_image
    (integrated_energy_continuous hs)
  have hB' : ∀ t ∈ Icc 0 T, (∫ x : Vec, totalEnergy s (t,x)) ≤ B :=
    fun t ht => hB ⟨t,ht,rfl⟩
  have hinc (n : ℕ) :
      ‖(∫ x : Vec, energyCutoff n x * totalEnergy s (T,x)) -
        (∫ x : Vec, energyCutoff n x * totalEnergy s (0,x))‖ ≤
          (C / ((n:ℝ)+1)) * B * T :=
    weighted_energy_increment_bound hs (energyCutoff_smooth n) (energyCutoff_compact n)
      (div_nonneg hC (by positivity)) (hb n) hT hB'
  have hl := ((energyCutoff_integral_tendsto (total_energy_integrable hs ⟨hT,le_rfl⟩)).sub
    (energyCutoff_integral_tendsto (total_energy_integrable hs ⟨le_rfl,hT⟩))).norm
  have hr : Filter.Tendsto (fun n : ℕ => (C / ((n:ℝ)+1)) * B * T) Filter.atTop (𝓝 0) := by
    have hi : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_mul] using ((hi.const_mul C).mul_const B).mul_const T
  have he := le_of_tendsto_of_tendsto' hl hr hinc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))

end EnergyPrefix

lemma Classical.energyPrefix {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) : EnergyPrefix s T := by
  refine ⟨hs.1.mono (fun _ hz => hz.1.1),hs.2.1.mono (fun _ hz => hz.1.1),
    hs.2.2.1.mono (fun _ hz => hz.1.1),(fun t ht => hs.2.2.2.1 t ht.1),?_,?_,
    hs.2.2.2.2.2.2.1 T hT,?_,?_⟩
  · obtain ⟨F,hc,he⟩ := hs.2.2.2.2.1
    exact ⟨F,hc.mono Icc_subset_Ici_self,fun t ht => he t ht.1⟩
  · obtain ⟨F,hc,he⟩ := hs.2.2.2.2.2.1
    exact ⟨F,hc.mono Icc_subset_Ici_self,fun t ht => he t ht.1⟩
  · intro t ht x v
    have hh := (hs.2.2.2.2.2.2.2.1 t ht.1.le).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.2.2.2.2.2.2.2.1 t ht.1.le).2.1 x
    have hb := (hs.2.2.2.2.2.2.2.1 t ht.1.le).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩
end RVM

end

end OAI
