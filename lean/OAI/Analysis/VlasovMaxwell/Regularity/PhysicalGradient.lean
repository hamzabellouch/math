import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.MagneticVolterra

namespace OAI

noncomputable section

namespace RVM


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma source_density_integrable {s : Solution} {U t P A M : ℝ} (x : Vec) (i : Fin 3)
    (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (_hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v))
      (ball (0:Vec) t) := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  have hu {z : Vec} (hzt : ‖z‖<t) : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  apply retarded_packet_integrable (F:=sourceWeightedPacket s t i) (P:=P) (C:=K*A) x
  · intro p hp hpt
    exact (sourceWeightedPacket_contDiffAt i hf hE hB hp (by
      simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hpt)).continuousAt
  · intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ (hu hzt) _ v hv,mul_zero]
  · intro x z v hz hzt hv
    change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul (hkb s t x z v hz hv (hEB _ (hu hzt) _).1 (hEB _ (hu hzt) _).2)
      (hfA _ (hu hzt) _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)

lemma retardedElectricDensity_split {s : Solution} {t : ℝ} (x z : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hz : z≠0) (ht : 0≤t-coneRadius 0 z) :
    retardedElectricDensity s t x (x+z) i =
      (∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
      (∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) := by
  have hxy : x≠x+z := by intro he; exact hz (add_left_cancel (show x+z=x+0 by simpa using he.symm))
  have hr : coneRadius x (x+z)=coneRadius 0 z := by simp [coneRadius]
  have hn : coneDirection x (x+z)=coneDirection 0 z := by simp [coneDirection,coneRadius]
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht (x+z)
  have htc : Continuous (fun v => transportConeCoefficient i (z,v)) := (transport_kernel_velocity_contDiff i hz).continuous
  have hsc : Continuous (fun v => sourceConeCoefficient s t x i (z,v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (contDiffAt_const.mul ((sourceAngularProfile_contDiffAt i
      (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').comp v
        (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
  have hti := (htc.mul hreg.continuous).integrable_of_hasCompactSupport (μ:=volume) hcomp.mul_left
  have hsi := (hsc.mul hreg.continuous).integrable_of_hasCompactSupport (μ:=volume) hcomp.mul_left
  change Integrable (fun v => transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) at hti
  change Integrable (fun v => sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) at hsi
  have hi := integrable_retardedElectricDensity_integrand hf hc hxy (by simpa only [hr] using ht)
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simp only [PiLp.proj_apply] at hp
  rw [retardedElectricDensity,←hp,←integral_add hti hsi]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    have hh := congrArg (fun a : Vec => a i) (physicalElectricKernel_eulerian_split
      (fderiv ℝ velocity v (s.E (t-coneRadius 0 z,x+z)+cross (velocity v) (s.B (t-coneRadius 0 z,x+z))))
      (show coneRadius 0 z≠0 by simpa [coneRadius] using hz) (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne')
    simp only [PiLp.smul_apply,smul_eq_mul,PiLp.add_apply] at hh
    simp only [PiLp.smul_apply,smul_eq_mul,hr,hn,
      transportConeCoefficient,sourceConeCoefficient,sourceFixedCoefficient,sourceAngularProfile]
    linear_combination s.f (t-coneRadius 0 z,x+z,v)*hh)


namespace Magnetic

lemma source_density_integrable {s : Solution} {U t P A M : ℝ} (x : Vec) (i : Fin 3)
    (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (_hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v))
      (ball (0:Vec) t) := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  have hu {z : Vec} (hzt : ‖z‖<t) : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  apply retarded_packet_integrable (F:=sourceWeightedPacket s t i) (P:=P) (C:=K*A) x
  · intro p hp hpt
    exact (sourceWeightedPacket_contDiffAt i hf hE hB hp (by
      simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hpt)).continuousAt
  · intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ (hu hzt) _ v hv,mul_zero]
  · intro x z v hz hzt hv
    change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul (hkb s t x z v hz hv (hEB _ (hu hzt) _).1 (hEB _ (hu hzt) _).2)
      (hfA _ (hu hzt) _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)

lemma retardedMagneticDensity_split {s : Solution} {t : ℝ} (x z : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hz : z≠0) (ht : 0≤t-coneRadius 0 z) :
    retardedMagneticDensity s t x (x+z) i =
      (∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
      (∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) := by
  have hxy : x≠x+z := by intro he; exact hz (add_left_cancel (show x+z=x+0 by simpa using he.symm))
  have hr : coneRadius x (x+z)=coneRadius 0 z := by simp [coneRadius]
  have hn : coneDirection x (x+z)=coneDirection 0 z := by simp [coneDirection,coneRadius]
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht (x+z)
  have htc : Continuous (fun v => transportConeCoefficient i (z,v)) := (transport_kernel_velocity_contDiff i hz).continuous
  have hsc : Continuous (fun v => sourceConeCoefficient s t x i (z,v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (contDiffAt_const.mul ((sourceAngularProfile_contDiffAt i
      (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').comp v
        (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
  have hti := (htc.mul hreg.continuous).integrable_of_hasCompactSupport (μ:=volume) hcomp.mul_left
  have hsi := (hsc.mul hreg.continuous).integrable_of_hasCompactSupport (μ:=volume) hcomp.mul_left
  change Integrable (fun v => transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) at hti
  change Integrable (fun v => sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) at hsi
  rw [retardedMagneticDensity_component hf hc hxy (by simpa only [hr] using ht) i,←integral_add hti hsi]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    have hh := congrArg (fun a : Vec => a i) (physicalMagneticKernel_eulerian_split
      (fderiv ℝ velocity v (s.E (t-coneRadius 0 z,x+z)+cross (velocity v) (s.B (t-coneRadius 0 z,x+z))))
      (show coneRadius 0 z≠0 by simpa [coneRadius] using hz) (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne')
    simp only [PiLp.smul_apply,smul_eq_mul,PiLp.add_apply] at hh
    simp only [hr,hn,
      transportConeCoefficient,sourceConeCoefficient,sourceFixedCoefficient,sourceAngularProfile]
    linear_combination s.f (t-coneRadius 0 z,x+z,v)*hh)

end Magnetic


lemma classical_electric_transport_source_before {d : Datum} {s : Solution} {U t P A M : ℝ}
    (hs : ClassicalBefore d s U) (hm : SmoothOnFiniteHorizons s) (x : Vec) (i : Fin 3)
    (ht : 0<t) (htU : t<U) (hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) :
    s.E (t,x) i=electricBoundaryField (datumBoundarySolution d) t x i+(4*Real.pi)⁻¹*
      ((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v))) := by
  have hti := transport_density_integrable x i htU.le hs.1 hA hP hfA
  have hsi := source_density_integrable x i htU.le hs.1 hs.2.1 hs.2.2.1 hA hP hfA hEB
  have hdens := integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hdens
  simp only [PiLp.proj_apply] at hp
  have hsplit : (∫ z in ball (0:Vec) t,retardedElectricDensity s t x (x+z) i)=
      (∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) := by
    rw [←integral_add hti hsi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact retardedElectricDensity_split x z i hs.1 hs.2.2.2.2.2.2.1 hz0 (by
      simpa only [coneRadius,zero_sub,norm_neg] using (sub_nonneg.mpr (show ‖z‖≤t from
        (show ‖z‖<t by simpa only [mem_ball,dist_zero_right] using hz).le)))
  have hh := congrArg (fun a : Vec => a i) (classical_electric_physical_vector_before hs hm ht htU x)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hh
  have hbd : electricBoundaryField s t x i=electricBoundaryField (datumBoundarySolution d) t x i :=
    classical_electricConeBoundary_datum_before hs ht x i
  rw [hbd,←hp,hsplit] at hh
  exact hh


namespace Magnetic

lemma classical_magnetic_transport_source_before {d : Datum} {s : Solution} {U t P A M : ℝ}
    (hs : ClassicalBefore d s U) (hm : SmoothOnFiniteHorizons s) (x : Vec) (i : Fin 3)
    (ht : 0<t) (htU : t<U) (hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) :
    s.B (t,x) i=magneticBoundaryField (datumBoundarySolution d) t x i+(4*Real.pi)⁻¹*
      ((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v))) := by
  have hti := transport_density_integrable x i htU.le hs.1 hA hP hfA
  have hsi := source_density_integrable x i htU.le hs.1 hs.2.1 hs.2.2.1 hA hP hfA hEB
  have hdens := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hdens
  simp only [PiLp.proj_apply] at hp
  have hsplit : (∫ z in ball (0:Vec) t,retardedMagneticDensity s t x (x+z) i)=
      (∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)) := by
    rw [←integral_add hti hsi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact retardedMagneticDensity_split x z i hs.1 hs.2.2.2.2.2.2.1 hz0 (by
      simpa only [coneRadius,zero_sub,norm_neg] using (sub_nonneg.mpr (show ‖z‖≤t from
        (show ‖z‖<t by simpa only [mem_ball,dist_zero_right] using hz).le)))
  have hh := congrArg (fun a : Vec => a i) (classical_magnetic_physical_vector_before hs hm ht htU x)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hh
  have hbd : magneticBoundaryField s t x i=magneticBoundaryField (datumBoundarySolution d) t x i :=
    classical_magneticConeBoundary_datum_before hs ht x i
  rw [hbd,←hp,hsplit] at hh
  exact hh

end Magnetic


lemma hasDerivAt_vec_component_line {g : Vec → Vec} {x e : Vec} (i : Fin 3)
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun q : ℝ => g (x+q • e) i) ((fderiv ℝ g x e) i) 0 := by
  have hl : HasDerivAt (fun q : ℝ => x+q • e) e 0 := by
    convert ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x using 1 <;> first | rfl | simp
  have hg' : HasFDerivAt g (fderiv ℝ g x) (x+(0:ℝ) • e) := by simpa only [zero_smul,add_zero] using hg.hasFDerivAt
  have hh := hg'.comp_hasDerivAt (0:ℝ) hl
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt (0:ℝ) hh
  simpa only [Function.comp_def,PiLp.proj_apply] using hp

lemma classical_electric_gradient_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
    ∀ (s : Solution) (U t N Q : ℝ) (x : Vec),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → 0≤N → 0≤Q →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*H^2*Q := by
  obtain ⟨B,C,D,hB,hC,hD,hT⟩ := electric_transport_deriv_bound P A M H e i hA hH
  obtain ⟨K,hK,hS⟩ := electric_source_deriv_bound P A M e i hA
  obtain ⟨J,hJ,hJi,hJb⟩ := datum_boundary_global_jets_horizon hd H hH 1
  let c := (4*Real.pi)⁻¹
  have hc : 0≤c := by dsimp [c]; positivity
  refine ⟨J*‖e‖+c*(B+D*Real.log (max 1 H)+K*(H+H^2)),C,c*D,c*K,
    ?_,hC,by positivity,by positivity,?_⟩
  · have hl : 0≤Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
    positivity
  intro s U t N Q x hs hm ht htU hUH hN hQ hfA hP hEB hDF hfN
  have hboundary := (hJb t ⟨ht,htU.le.trans hUH⟩).1.1
  let g := electricBoundaryField (datumBoundarySolution d) t
  have hbd := hasDerivAt_vec_component_line (x:=x) (e:=e) i (hboundary.differentiable (by simp)).differentiableAt
  have hbd_bound : |fderiv ℝ g x e i|≤J*‖e‖ := by
    apply (norm_coordinate_le _ i).trans
    apply (ContinuousLinearMap.le_opNorm _ e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
    simpa only [norm_iteratedFDeriv_one] using (hJb t ⟨ht,htU.le.trans hUH⟩).2 x |>.1
  have htd := hasDerivAt_electric_transport_integral x e i 0 ht htU.le hs.1 hA hN hP hfA hfN
  have hsd := hasDerivAt_electric_source_integral x e i 0 htU.le hs.1 hs.2.1 hs.2.2.1 hA hN hQ hP hfA hEB hDF hfN
  have htotal := hbd.add ((htd.add hsd).const_mul c)
  have heq : (fun q : ℝ => s.E (t,x+q • e) i)=fun q : ℝ =>
      g (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))) := by
    funext q
    exact classical_electric_transport_source_before hs hm (x+q • e) i ht htU hA hP hfA hEB
  change HasDerivAt (fun q : ℝ =>
      g (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)))) _ 0 at htotal
  rw [heq,htotal.deriv]
  have htbound := hT s U t N x ht htU.le hUH hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hfN
  have hsbound := hS s U t H Q N x ht htU.le hUH hQ hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hDF hfN
  rw [htd.deriv] at htbound
  rw [hsd.deriv] at hsbound
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hc]
  apply (add_le_add hbd_bound (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add htbound hsbound)) hc)).trans_eq
  ring


namespace Magnetic

lemma classical_magnetic_gradient_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
    ∀ (s : Solution) (U t N Q : ℝ) (x : Vec),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → 0≤N → 0≤Q →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*H^2*Q := by
  obtain ⟨B,C,D,hB,hC,hD,hT⟩ := magnetic_transport_deriv_bound P A M H e i hA hH
  obtain ⟨K,hK,hS⟩ := magnetic_source_deriv_bound P A M e i hA
  obtain ⟨J,hJ,hJi,hJb⟩ := datum_boundary_global_jets_horizon hd H hH 1
  let c := (4*Real.pi)⁻¹
  have hc : 0≤c := by dsimp [c]; positivity
  refine ⟨J*‖e‖+c*(B+D*Real.log (max 1 H)+K*(H+H^2)),C,c*D,c*K,
    ?_,hC,by positivity,by positivity,?_⟩
  · have hl : 0≤Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
    positivity
  intro s U t N Q x hs hm ht htU hUH hN hQ hfA hP hEB hDF hfN
  have hboundary := (hJb t ⟨ht,htU.le.trans hUH⟩).1.2
  let g := magneticBoundaryField (datumBoundarySolution d) t
  have hbd := hasDerivAt_vec_component_line (x:=x) (e:=e) i (hboundary.differentiable (by simp)).differentiableAt
  have hbd_bound : |fderiv ℝ g x e i|≤J*‖e‖ := by
    apply (norm_coordinate_le _ i).trans
    apply (ContinuousLinearMap.le_opNorm _ e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
    simpa only [norm_iteratedFDeriv_one] using (hJb t ⟨ht,htU.le.trans hUH⟩).2 x |>.2
  have htd := hasDerivAt_magnetic_transport_integral x e i 0 ht htU.le hs.1 hA hN hP hfA hfN
  have hsd := hasDerivAt_magnetic_source_integral x e i 0 htU.le hs.1 hs.2.1 hs.2.2.1 hA hN hQ hP hfA hEB hDF hfN
  have htotal := hbd.add ((htd.add hsd).const_mul c)
  have heq : (fun q : ℝ => s.B (t,x+q • e) i)=fun q : ℝ =>
      g (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))) := by
    funext q
    exact classical_magnetic_transport_source_before hs hm (x+q • e) i ht htU hA hP hfA hEB
  change HasDerivAt (fun q : ℝ =>
      g (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)))) _ 0 at htotal
  rw [heq,htotal.deriv]
  have htbound := hT s U t N x ht htU.le hUH hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hfN
  have hsbound := hS s U t H Q N x ht htU.le hUH hQ hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hDF hfN
  rw [htd.deriv] at htbound
  rw [hsd.deriv] at hsbound
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hc]
  apply (add_le_add hbd_bound (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add htbound hsbound)) hc)).trans_eq
  ring

end Magnetic

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma classical_electric_gradient_volterra_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → 0≤N → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨B,C,D,hB,hC,hD,hT⟩ := electric_transport_deriv_bound P A M H e i hA hH
  obtain ⟨K,hK,hS⟩ := electric_source_deriv_volterra_bound P A M e i hA
  obtain ⟨J,hJ,hJi,hJb⟩ := datum_boundary_global_jets_horizon hd H hH 1
  let c := (4*Real.pi)⁻¹
  have hc : 0≤c := by dsimp [c]; positivity
  refine ⟨J*‖e‖+c*(B+D*Real.log (max 1 H)+K*H),C,c*D,c*K*(1+H),
    ?_,hC,by positivity,by positivity,?_⟩
  · have hl : 0≤Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
    positivity
  intro s U t N x g hs hm ht htU hUH hN hg hg0 hfA hP hEB hDF hfN
  obtain ⟨Q₀,hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f:=g) hg.continuousOn
  let Q := max Q₀ 0
  have hQ : 0≤Q := le_max_right _ _
  have hDFconst : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q := by
    intro u hu y
    have hh : g u≤Q := (le_abs_self _).trans ((hQ₀ u ⟨hu.1.le,hu.2⟩).trans (le_max_left _ _))
    exact ⟨(hDF u hu y).1.trans hh,(hDF u hu y).2.trans hh⟩
  have hboundary := (hJb t ⟨ht,htU.le.trans hUH⟩).1.1
  let b := electricBoundaryField (datumBoundarySolution d) t
  have hbd := hasDerivAt_vec_component_line (x:=x) (e:=e) i (hboundary.differentiable (by simp)).differentiableAt
  have hbd_bound : |fderiv ℝ b x e i|≤J*‖e‖ := by
    apply (norm_coordinate_le _ i).trans
    apply (ContinuousLinearMap.le_opNorm _ e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
    simpa only [norm_iteratedFDeriv_one] using (hJb t ⟨ht,htU.le.trans hUH⟩).2 x |>.1
  have htd := hasDerivAt_electric_transport_integral x e i 0 ht htU.le hs.1 hA hN hP hfA hfN
  have hsd := hasDerivAt_electric_source_integral x e i 0 htU.le hs.1 hs.2.1 hs.2.2.1 hA hN hQ hP hfA hEB hDFconst hfN
  have htotal := hbd.add ((htd.add hsd).const_mul c)
  have heq : (fun q : ℝ => s.E (t,x+q • e) i)=fun q : ℝ =>
      b (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))) := by
    funext q
    exact classical_electric_transport_source_before hs hm (x+q • e) i ht htU hA hP hfA hEB
  change HasDerivAt (fun q : ℝ =>
      b (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)))) _ 0 at htotal
  rw [heq,htotal.deriv]
  have htbound := hT s U t N x ht htU.le hUH hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hfN
  have hsbound := hS s U t H N x g ht htU.le hUH hg hg0 hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hDF hfN
  rw [htd.deriv] at htbound
  rw [hsd.deriv] at hsbound
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hc]
  apply (add_le_add hbd_bound (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add htbound hsbound)) hc)).trans_eq
  ring


namespace Magnetic

lemma classical_magnetic_gradient_volterra_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D K : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧ 0≤K ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → 0≤N → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*N)+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨B,C,D,hB,hC,hD,hT⟩ := magnetic_transport_deriv_bound P A M H e i hA hH
  obtain ⟨K,hK,hS⟩ := magnetic_source_deriv_volterra_bound P A M e i hA
  obtain ⟨J,hJ,hJi,hJb⟩ := datum_boundary_global_jets_horizon hd H hH 1
  let c := (4*Real.pi)⁻¹
  have hc : 0≤c := by dsimp [c]; positivity
  refine ⟨J*‖e‖+c*(B+D*Real.log (max 1 H)+K*H),C,c*D,c*K*(1+H),
    ?_,hC,by positivity,by positivity,?_⟩
  · have hl : 0≤Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
    positivity
  intro s U t N x g hs hm ht htU hUH hN hg hg0 hfA hP hEB hDF hfN
  obtain ⟨Q₀,hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f:=g) hg.continuousOn
  let Q := max Q₀ 0
  have hQ : 0≤Q := le_max_right _ _
  have hDFconst : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q := by
    intro u hu y
    have hh : g u≤Q := (le_abs_self _).trans ((hQ₀ u ⟨hu.1.le,hu.2⟩).trans (le_max_left _ _))
    exact ⟨(hDF u hu y).1.trans hh,(hDF u hu y).2.trans hh⟩
  have hboundary := (hJb t ⟨ht,htU.le.trans hUH⟩).1.2
  let b := magneticBoundaryField (datumBoundarySolution d) t
  have hbd := hasDerivAt_vec_component_line (x:=x) (e:=e) i (hboundary.differentiable (by simp)).differentiableAt
  have hbd_bound : |fderiv ℝ b x e i|≤J*‖e‖ := by
    apply (norm_coordinate_le _ i).trans
    apply (ContinuousLinearMap.le_opNorm _ e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
    simpa only [norm_iteratedFDeriv_one] using (hJb t ⟨ht,htU.le.trans hUH⟩).2 x |>.2
  have htd := hasDerivAt_magnetic_transport_integral x e i 0 ht htU.le hs.1 hA hN hP hfA hfN
  have hsd := hasDerivAt_magnetic_source_integral x e i 0 htU.le hs.1 hs.2.1 hs.2.2.1 hA hN hQ hP hfA hEB hDFconst hfN
  have htotal := hbd.add ((htd.add hsd).const_mul c)
  have heq : (fun q : ℝ => s.B (t,x+q • e) i)=fun q : ℝ =>
      b (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))) := by
    funext q
    exact classical_magnetic_transport_source_before hs hm (x+q • e) i ht htU hA hP hfA hEB
  change HasDerivAt (fun q : ℝ =>
      b (x+q • e) i+c*((∫ z in ball (0:Vec) t,∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))+
       (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)))) _ 0 at htotal
  rw [heq,htotal.deriv]
  have htbound := hT s U t N x ht htU.le hUH hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hfN
  have hsbound := hS s U t H N x g ht htU.le hUH hg hg0 hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 hfA hP hEB hDF hfN
  rw [htd.deriv] at htbound
  rw [hsd.deriv] at hsbound
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hc]
  apply (add_le_add hbd_bound (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add htbound hsbound)) hc)).trans_eq
  ring

end Magnetic

end RVM

end

end OAI
