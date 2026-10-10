import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ElectricConeBoundary
import OAI.Analysis.VlasovMaxwell.Retarded.ReceiverQ

namespace OAI

noncomputable section

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

lemma cross_add_right (a b c : Vec) : cross a (b+c)=cross a b+cross a c :=
  (crossCLM a).map_add b c

def electricBoundaryField (s : Solution) (t : ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i => electricConeBoundary s t x i 0)

def magneticBoundaryField (s : Solution) (t : ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i => magneticConeBoundary s t x i 0)

lemma classical_electric_physical_vector {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) := by
  have hD := integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  ext i
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
  exact (classical_electric_physical_representation hs hm ht x i).trans
    (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
      smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

lemma classical_magnetic_physical_vector {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (x : Vec) :
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) := by
  have hD := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  ext i
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
  exact (classical_magnetic_physical_representation hs hm ht x i).trans
    (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
      smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

def boundaryLorentzForce (s : Solution) (t : ℝ) (x a : Vec) : Vec :=
  electricBoundaryField s t x+cross a (magneticBoundaryField s t x)

lemma classical_physical_force_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce s t x a+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
        retardedElectricDensity s t x (x+z)+cross a (retardedMagneticDensity s t x (x+z)) := by
  have hE := integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hB := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  have hc := (crossCLM a).integral_comp_comm hB
  have hcross : IntegrableOn (fun z => cross a (retardedMagneticDensity s t x (x+z)))
      (ball (0:Vec) t) := by
    simpa only [IntegrableOn,crossCLM_apply] using (crossCLM a).integrable_comp hB
  have hc' : (∫ z in ball (0:Vec) t, cross a (retardedMagneticDensity s t x (x+z))) =
      cross a (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) := by
    simpa only [crossCLM_apply] using hc
  rw [classical_electric_physical_vector hs hm ht x,classical_magnetic_physical_vector hs hm ht x,
    integral_add hE hcross,hc']
  simp only [boundaryLorentzForce,cross_add_right,cross_smul_right]
  module

def datumBoundarySolution (d : Datum) : Solution :=
  ⟨fun p => d.f₀ p.2,fun p => d.E₀ p.2,fun p => d.B₀ p.2⟩

lemma electricConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedElectricFlux s t x i (x+t • n.1)=
      retardedElectricFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedElectricFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold electricConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [rho,current,hf]

lemma magneticConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedMagneticFlux s t x i (x+t • n.1)=
      retardedMagneticFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedMagneticFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold magneticConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [current,hf]

lemma classical_electricConeBoundary_datum {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary (datumBoundarySolution d) t x i 0 :=
  electricConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

lemma classical_magneticConeBoundary_datum {d : Datum} {s : Solution}
    (hs : Classical d s) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary (datumBoundarySolution d) t x i 0 :=
  magneticConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

def forceTransportKernel (r : ℝ) (n a v : Vec) : Vec :=
  (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ • receiverQ a n (n-velocity v)

def forceSourceKernel (r : ℝ) (n a v b : Vec) : Vec :=
  (r*(1-dot n (velocity v))^2)⁻¹ • receiverQ a n (sourceNumerator n (velocity v) b)

lemma physical_force_kernel (r : ℝ) (n a v b : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity v)) • receiverQ a n (physicalElectricKernel r n (velocity v) b) =
      forceTransportKernel r n a v+forceSourceKernel r n a v b := by
  have hd := (cone_denom_pos v n hn).ne'
  have hq := (q_pos v).ne'
  have h1 : (1-dot n (velocity v))*((1-dot (velocity v) (velocity v))/(r^2*(1-dot n (velocity v))^3)) =
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ := by
    rw [velocity_self]
    field_simp
    ring
  have h2 : (1-dot n (velocity v))*(r*(1-dot n (velocity v))^3)⁻¹ =
      (r*(1-dot n (velocity v))^2)⁻¹ := by
    field_simp
  simp only [physicalElectricKernel,receiverQ_add,receiverQ_smul,smul_add,smul_smul,h1,h2,
    forceTransportKernel,forceSourceKernel,sourceNumerator]

lemma forceTransportKernel_bound (r : ℝ) (n w v : Vec) (hn : ‖n‖=1) :
    ‖forceTransportKernel r n (velocity w) v‖ ≤
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ *
        ((1-dot n (velocity v))+2*Real.sqrt (2*(1-dot n (velocity w)))*
          Real.sqrt (2*(1-dot n (velocity v)))) := by
  unfold forceTransportKernel
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (receiverQ_transport_bound w v n hn) (by positivity)

lemma forceSourceKernel_bound (r : ℝ) (n w v E B : Vec) (hr : 0<r) (hn : ‖n‖=1) :
    ‖forceSourceKernel r n (velocity w) v (fderiv ℝ velocity v (E+cross (velocity v) B))‖ ≤
      (10*Real.sqrt (2*(1-dot n (velocity w))))/(r*q v*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hq := q_pos v
  unfold forceSourceKernel
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (receiverQ_source_bound w v E B n hn) (by positivity)).trans_eq
  field_simp

lemma transverse_forceSourceKernel_bound (r : ℝ) (n w v E B : Vec) (hr : 0<r) (hn : ‖n‖=1) :
    ‖transverseProjection w (forceSourceKernel r n (velocity w) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖ ≤
      (15*(1-dot n (velocity w)))/(r*q v*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hq := q_pos v
  unfold forceSourceKernel
  rw [show transverseProjection w (_ • _) = _ • transverseProjection w _ from
    velocityProjection_smul _ _ _,norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (transverse_receiverQ_source_bound w v E B n hn)
    (by positivity)).trans_eq
  field_simp

end RVM

end

end OAI
