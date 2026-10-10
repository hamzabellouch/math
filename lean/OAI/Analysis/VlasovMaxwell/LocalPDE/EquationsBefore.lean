import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ReceiverQCLM

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
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def EquationsBefore (s : Solution) (H : ℝ) : Prop := ∀ t, 0 ≤ t → t < H →
  (∀ x v,
    derivWithin (fun t' => s.f (t', x, v)) (Ici 0) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => s.f (t, y, v)) x i) +
    (∑ i : Fin 3, (s.E (t, x) + cross (velocity v) (s.B (t, x))) i *
      spatialPartial (fun v' => s.f (t, x, v')) v i) = 0) ∧
  (∀ x, derivWithin (fun t' => s.E (t', x)) (Ici 0) t -
    curl (fun y => s.B (t, y)) x = -current (fun z => s.f (t, z)) x) ∧
  (∀ x, derivWithin (fun t' => s.B (t', x)) (Ici 0) t +
    curl (fun y => s.E (t, y)) x = 0) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x = rho (fun z => s.f (t, z)) x) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)

def ClassicalBefore (d : Datum) (s : Solution) (H : ℝ) : Prop :=
  ContDiffOn ℝ 1 s.f particleHalfSpace ∧
  ContDiffOn ℝ 1 s.E fieldHalfSpace ∧ ContDiffOn ℝ 1 s.B fieldHalfSpace ∧
  (∀ t, 0 ≤ t → ∀ z, 0 ≤ s.f (t, z)) ∧
  TimeContinuousL2 s.E ∧ TimeContinuousL2 s.B ∧
  CompactOnFiniteHorizons s ∧ EquationsBefore s H ∧
  (∀ z, s.f (0, z) = d.f₀ z) ∧
  (∀ x, s.E (0, x) = d.E₀ x) ∧ (∀ x, s.B (0, x) = d.B₀ x)

lemma particle_spacetime_vlasov_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s H)
    {t : ℝ} (ht : 0 < t) (hth : t < H) (x v : Vec) :
    fderiv ℝ (particleBySpacetime s.f) ((t,x),v)
      ((1,velocity v),s.E (t,x) + cross (velocity v) (s.B (t,x))) = 0 := by
  have hd := particle_differentiableAt_positive hf ht x v
  rw [fderiv_particleBySpacetime hd, full_directional_derivative hd]
  have he := (heq t (le_of_lt ht) hth).1 x v
  rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he

lemma classical_retarded_electric_integral_identity_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : EquationsBefore s H) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (hth : t < H) (i : Fin 3) :
    (∫ v : Vec, ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y)))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedG x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedG x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedG hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hki : Continuous (fun v => physicalElectricKernel (coneRadius x y) (coneDirection x y)
      (velocity v) (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
        cross (velocity v) (s.B (t-coneRadius x y,y)))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hk
  have hid := classical_retarded_integral_identity
    (L := fun v => ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    simpa only [fderiv_particleBySpacetime hf'] using particle_spacetime_vlasov_before hf heq ht
      ((sub_le_self t (norm_nonneg (x-y))).trans_lt hth) y v
  simpa only [retardedDensity,mul_assoc] using retarded_electric_density_identity hf' hxy hv i

lemma classical_retarded_magnetic_integral_identity_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : EquationsBefore s H) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (hth : t < H) (i : Fin 3) :
    (∫ v : Vec, -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y))))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedH x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedH x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedH hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hkc : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y)))))) :=
    (contDiff_cross (k:=1)).continuous.comp (continuous_const.prodMk hk)
  have hki : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y))))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hkc
  have hid := classical_retarded_integral_identity
    (L := fun v => -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    simpa only [fderiv_particleBySpacetime hf'] using particle_spacetime_vlasov_before hf heq ht
      ((sub_le_self t (norm_nonneg (x-y))).trans_lt hth) y v
  simpa only [retardedDensity,mul_assoc] using retarded_magnetic_density_identity hf' hxy hv i

lemma classical_retarded_electric_moment_identity_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : EquationsBefore s H) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (hth : t < H) (i : Fin 3) :
    ((coneRadius x y)^2)⁻¹*coneDirection x y i*rho (fun z => s.f (t-coneRadius x y,z)) y +
      (coneDirection x y i/coneRadius x y)*
        dirD (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2) (1,0) (t-coneRadius x y,y) -
      (coneRadius x y)⁻¹*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 i) (1,0) (t-coneRadius x y,y) =
    (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
      physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))) i) -
    divergence (fun z => ∫ v : Vec,
      (retardedDensity s.f t x (z,v)*retardedG x (z,v) i) • velocity v) y := by
  have hr : RegularParticle s.f := ⟨hf,hc⟩
  have hvel : ContDiff ℝ 1 (fun v => velocity v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity
  have hfI : Integrable (fun v : Vec => s.f (t-coneRadius x y,y,v)) := by
    simpa only [one_mul] using hr.scalar_moment_integrable (continuous_const (y:=(1:ℝ))) ht.le y
  have htI : Integrable (fun v : Vec => fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) := by
    simpa only [one_mul] using hr.time_moment_integrable (continuous_const (y:=(1:ℝ))) ht y
  have hjI := hr.time_moment_integrable hvel.continuous ht y
  have hsum : Integrable (fun v : Vec =>
      ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i/coneRadius x y)*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) :=
    (hfI.const_mul _).add (htI.const_mul _)
  rw [dirD_rho hr ht y,dirD_current_component hr ht y i,rho]
  rw [← integral_const_mul,← integral_const_mul,← integral_const_mul,
    ← integral_add (hfI.const_mul _) (htI.const_mul _),
    ← integral_sub hsum (hjI.const_mul _)]
  convert classical_retarded_electric_integral_identity_before hf hc heq hxy ht hth i using 1
  congr 1
  funext v
  dsimp only
  ring

lemma classical_retarded_magnetic_moment_identity_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : EquationsBefore s H) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (hth : t < H) (i : Fin 3) :
    -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (current (fun z => s.f (t-coneRadius x y,z)) y) i -
      (coneRadius x y)⁻¹*(coneDirection x y (curlA i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlB i)) (1,0) (t-coneRadius x y,y) -
        coneDirection x y (curlB i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlA i)) (1,0) (t-coneRadius x y,y)) =
      retardedMagneticDensity s t x y i - divergence (retardedMagneticFlux s t x i) y := by
  have hr : RegularParticle s.f := ⟨hf,hc⟩
  have hcv : ContDiff ℝ 1 (fun v : Vec => cross (coneDirection x y) (velocity v) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp
      (contDiff_cross.comp (contDiff_const.prodMk contDiff_velocity))
  have hi := hr.moment_integrable (contDiff_velocity (k:=1)).continuous ht.le y
  have hcross : cross (coneDirection x y) (current (fun z => s.f (t-coneRadius x y,z)) y) i =
      ∫ v : Vec, cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) := by
    have hi' := (crossCLM (coneDirection x y)).integrable_comp hi
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi'
    unfold current
    rw [← integral_cross_left hi]
    simpa only [crossCLM_apply,PiLp.proj_apply,cross_smul_right,PiLp.smul_apply,smul_eq_mul,mul_comm] using he.symm
  have hdt : coneDirection x y (curlA i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlB i)) (1,0) (t-coneRadius x y,y) -
        coneDirection x y (curlB i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlA i)) (1,0) (t-coneRadius x y,y) =
      ∫ v : Vec, cross (coneDirection x y) (velocity v) i*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0) := by
    have hInt (k : Fin 3) : Integrable (fun v : Vec => velocity v k*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) := hr.time_moment_integrable
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).continuous.comp (contDiff_velocity (k:=1)).continuous) ht y
    rw [dirD_current_component hr ht y,dirD_current_component hr ht y,
      ← integral_const_mul,← integral_const_mul,← integral_sub ((hInt _).const_mul _) ((hInt _).const_mul _)]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [cross_apply_cyclic]
    ring
  rw [hcross,hdt,retardedMagneticDensity_component hf hc hxy ht.le i,
    ← integral_const_mul,← integral_const_mul,
    ← integral_sub ((hr.scalar_moment_integrable hcv.continuous ht.le y).const_mul _)
      ((hr.time_moment_integrable hcv.continuous ht y).const_mul _)]
  unfold retardedMagneticFlux
  convert classical_retarded_magnetic_integral_identity_before hf hc heq hxy ht hth i using 1
  congr 1
  funext v
  dsimp only
  ring

lemma classical_positiveTimeShift_maxwell_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a t : ℝ}
    (ha : 0<a) (ht : 0≤t) (hH : a+t < H) (x : Vec) :
    dirD (positiveTimeShift a s.E) (1,0) (t,x)=
      spaceCurl (positiveTimeShift a s.B) (t,x)-
        positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2) (t,x) ∧
    dirD (positiveTimeShift a s.B) (1,0) (t,x) =
      -spaceCurl (positiveTimeShift a s.E) (t,x) ∧
    divergence (fun y => positiveTimeShift a s.E (t,y)) x =
      positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2) (t,x) ∧
    divergence (fun y => positiveTimeShift a s.B (t,y)) x = 0 := by
  have hat : 0<a+t := by linarith
  have heq := hs.2.2.2.2.2.2.2.1 (a+t) hat.le hH
  have hE := field_differentiableAt_positive hs.2.1 hat x
  have hB := field_differentiableAt_positive hs.2.2.1 hat x
  have he := heq.2.1 x
  have hb := heq.2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hat),deriv_time_slice hE] at he
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hat),deriv_time_slice hB] at hb
  have hcE := spaceCurl_positiveTimeShift ha ht (fun p hp => (hm.field_positive hp).1) x
  have hcB := spaceCurl_positiveTimeShift ha ht (fun p hp => (hm.field_positive hp).2) x
  have hsE : (fun y => positiveTimeShift a s.E (t,y))=(fun y => s.E (a+t,y)) :=
    funext (positiveTimeShift_eq ha ht s.E)
  have hsB : (fun y => positiveTimeShift a s.B (t,y))=(fun y => s.B (a+t,y)) :=
    funext (positiveTimeShift_eq ha ht s.B)
  refine ⟨?_,?_,?_,?_⟩
  · unfold dirD
    rw [fderiv_positiveTimeShift ha ht x hE,hcB,positiveTimeShift_eq ha ht]
    exact (sub_eq_iff_eq_add.mp he).trans (by abel)
  · unfold dirD
    rw [fderiv_positiveTimeShift ha ht x hB,hcE]
    exact eq_neg_of_add_eq_zero_left hb
  · rw [hsE,positiveTimeShift_eq ha ht]
    exact heq.2.2.2.1 x
  · rw [hsB]
    exact heq.2.2.2.2 x

lemma classical_shifted_electric_potential_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0≤T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.E (a+T,x) i =
      freeWave (fun y => s.E (a,y) i) (fun y => curl (fun z => s.B (a,z)) y i) (T,x) +
      electricPotentialComponent
        (positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2))
        (positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)) i (T,x) := by
  have hE := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).1)
  have hB := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).2)
  have hρ := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).1)
  have hj := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)
  have hh := maxwell_electric_potential_representation hE hB hj hρ hT
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1 (by linarith [hr.2]) y).1)
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1.le (by linarith [hr.2]) y).2.1)
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1.le (by linarith [hr.2]) y).2.2.1) x i
  rw [positiveTimeShift_eq ha hT] at hh
  simpa only [positiveTimeShift_eq ha (le_refl 0),add_zero,
    spaceCurl_positiveTimeShift ha (le_refl 0) (fun p hp => (hm.field_positive hp).2)] using hh

lemma classical_shifted_magnetic_potential_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0≤T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      magneticPotentialComponent
        (positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)) i (T,x) := by
  have hE := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).1)
  have hB := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).2)
  have hj := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)
  have hh := maxwell_magnetic_potential_representation hE hB hj hT
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1.le (by linarith [hr.2]) y).1)
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1 (by linarith [hr.2]) y).2.1)
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1.le (by linarith [hr.2]) y).2.2.2) x i
  rw [positiveTimeShift_eq ha hT] at hh
  simpa only [positiveTimeShift_eq ha (le_refl 0),add_zero,
    spaceCurl_positiveTimeShift ha (le_refl 0) (fun p hp => (hm.field_positive hp).1)] using hh

lemma contDiff_shifted_moments_before {d : Datum} {s : Solution} {H : ℝ} (hs : ClassicalBefore d s H)
    (hm : SmoothOnFiniteHorizons s) {a : ℝ} (ha : 0<a) :
    ContDiff ℝ ∞ (shiftedRho s a) ∧ ContDiff ℝ ∞ (shiftedCurrent s a) :=
  ⟨contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).1),
   contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)⟩

lemma ClassicalBefore.regularParticle {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) : RegularParticle s.f := ⟨hs.1,hs.2.2.2.2.2.2.1⟩

lemma electricMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ} (ha : 0<a) (hH : a+T < H)
    (x : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (hzt : ‖z‖<T) :
    electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z =
      retardedElectricDensity s (a+T) x (x+z) i -
      divergence (retardedElectricFlux s (a+T) x i) (x+z) := by
  have hc := hs.2.2.2.2.2.2.1
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<a+T-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hp : 0<a+(T-‖z‖) := by linarith
  have hρ := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).1
  have hj := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).2
  have hji : DifferentiableAt ℝ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 i)
      (a+(T-‖z‖),x+z) :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp _ hj).differentiableAt (by simp)
  have herr : (fun p => shiftedCurrent s a p i)=
      positiveTimeShift a (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 i) := by
    funext p
    simp only [shiftedCurrent,positiveTimeShift,positiveTimeExtend,PiLp.smul_apply,smul_eq_mul]
  unfold electricMomentDensity
  rw [herr]
  have hρeq : shiftedRho s a (T-‖z‖,x+z)=rho (fun q => s.f (a+(T-‖z‖),q)) (x+z) :=
    positiveTimeShift_eq ha (sub_nonneg.mpr hzt.le) _ _
  rw [hρeq]
  unfold dirD shiftedRho
  rw [fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ (hρ.differentiableAt (by simp)),
    fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ hji]
  have he := classical_retarded_electric_moment_identity_before hs.1 hc hs.2.2.2.2.2.2.2.1 hxy ht hH i
  rw [← retardedElectricDensity_component hs.1 hc hxy ht.le i] at he
  change _ = _ - divergence (retardedElectricFlux s (a+T) x i) (x+z) at he
  rw [← he]
  simp only [coneRadius_add,coneDirection_add,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
    dirD,show a+T-‖z‖=a+(T-‖z‖) by ring]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma integrated_electricMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) T, electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) =
      (∫ z in ball (0:Vec) T, retardedElectricDensity s (a+T) x (x+z) i) -
      ∫ n : Sphere, T^2*dot n.1 (retardedElectricFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure := by
  have hc := hs.2.2.2.2.2.2.1
  have hρj := contDiff_shifted_moments_before hs hm ha
  have hM := integrableOn_electricMomentDensity hρj.1 hρj.2 hT.le x i
  have hD := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
    (integrableOn_retardedElectricDensity hs.1 hs.2.1 hs.2.2.1 hc hT.le
      (show T<a+T by linarith) x)
  change IntegrableOn (fun z : Vec => retardedElectricDensity s (a+T) x (x+z) i) (ball (0:Vec) T) at hD
  let F : Vec → Vec := fun z => retardedElectricFlux s (a+T) x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) T)]
      (fun z => retardedElectricDensity s (a+T) x (x+z) i -
        electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := electricMomentDensity_actual_before hs hm ha hH x i hz0 (by simpa only [mem_ball_zero_iff] using hz)
    dsimp only [F]
    rw [divergence_add_right]
    linarith
  have hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<a+T → ContDiffAt ℝ 1 F z := by
    intro z hz hzT
    have hxy : x≠x+z := by
      intro h
      apply (norm_pos_iff.mp hz)
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    have hp : x+z ∈ retardedSpaceDomain (a+T) x := ⟨hxy,by rw [coneRadius_add]; linarith⟩
    exact ((contDiffOn_retarded_flux hs.1 hc (by linarith) x i).contDiffAt
      ((isOpen_retardedSpaceDomain (a+T) x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) T) :=
    (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular hT (show T<a+T by linarith) hF hi
    (retarded_flux_tip hs.1 hc (show 0<a+T by linarith) x i)
  have hh : (∫ z in ball (0:Vec) T, divergence F z) =
      (∫ z in ball (0:Vec) T, retardedElectricDensity s (a+T) x (x+z) i) -
      (∫ z in ball (0:Vec) T, electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, T^2*dot n.1 (retardedElectricFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure at hg
  linarith

lemma classical_shifted_electric_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.E (a+T,x) i =
      freeWave (fun y => s.E (a,y) i) (fun y => curl (fun z => s.B (a,z)) y i) (T,x) +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedElectricDensity s (a+T) x (x+z) i) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
        (retardedElectricFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T*n.1 i*rho (fun z => s.f (a,z)) (x+T • n.1) ∂sphereMeasure) -
      waveK (fun y => current (fun z => s.f (a,z)) y i) (T,x) := by
  have hρj := contDiff_shifted_moments_before hs hm ha
  rw [classical_shifted_electric_potential_representation_before hs hm ha hT.le hH x i]
  change _ + electricPotentialComponent (shiftedRho s a) (shiftedCurrent s a) i (T,x)=_
  rw [electricPotentialComponent_ball hρj.1 hρj.2 hT]
  change _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T,
      electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) - _ - _)=_
  rw [integrated_electricMomentDensity_actual_before hs hm ha hT hH x i]
  have hρ0 : (fun n : Sphere => T*n.1 i*shiftedRho s a (0,x+T • n.1)) =
      (fun n : Sphere => T*n.1 i*rho (fun z => s.f (a,z)) (x+T • n.1)) := by
    funext n
    simp only [shiftedRho,positiveTimeShift_eq ha (le_refl 0),add_zero]
  have hj0 : (fun y => shiftedCurrent s a (0,y) i)=(fun y => current (fun z => s.f (a,z)) y i) := by
    funext y
    simp only [shiftedCurrent,positiveTimeShift_eq ha (le_refl 0),add_zero]
  rw [hρ0,hj0]
  ring

lemma magneticMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ} (ha : 0<a) (hH : a+T < H)
    (x : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (hzt : ‖z‖<T) :
    magneticMomentDensity (shiftedCurrent s a) T x i z =
      retardedMagneticDensity s (a+T) x (x+z) i -
      divergence (retardedMagneticFlux s (a+T) x i) (x+z) := by
  have hc := hs.2.2.2.2.2.2.1
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<a+T-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hp : 0<a+(T-‖z‖) := by linarith
  have hj := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).2
  have hji (k : Fin 3) : DifferentiableAt ℝ
      (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) (a+(T-‖z‖),x+z) :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).contDiff.contDiffAt.comp _ hj).differentiableAt (by simp)
  have herr (k : Fin 3) : (fun p => shiftedCurrent s a p k)=
      positiveTimeShift a (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) := by
    funext p
    simp only [shiftedCurrent,positiveTimeShift,positiveTimeExtend,PiLp.smul_apply,smul_eq_mul]
  have hjder (k : Fin 3) : dirD (fun p => shiftedCurrent s a p k) (1,0) (T-‖z‖,x+z) =
      dirD (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) (1,0) (a+(T-‖z‖),x+z) := by
    rw [herr]
    unfold dirD
    rw [fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ (hji k)]
  have hjval : shiftedCurrent s a (T-‖z‖,x+z)=current (fun q => s.f (a+(T-‖z‖),q)) (x+z) :=
    positiveTimeShift_eq ha (sub_nonneg.mpr hzt.le) _ _
  unfold magneticMomentDensity
  rw [hjder,hjder,hjval]
  have he := classical_retarded_magnetic_moment_identity_before hs.1 hc hs.2.2.2.2.2.2.2.1 hxy ht hH i
  rw [← he,cross_apply_cyclic]
  simp only [coneRadius_add,coneDirection_add,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
    show a+T-‖z‖=a+(T-‖z‖) by ring]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma integrated_magneticMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure := by
  have hc := hs.2.2.2.2.2.2.1
  have hρj := contDiff_shifted_moments_before hs hm ha
  have hM := integrableOn_magneticMomentDensity hρj.2 T x i
  have hD : IntegrableOn (fun z : Vec => retardedMagneticDensity s (a+T) x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedMagneticDensity hs.1 hs.2.1 hs.2.2.1 hc hT.le (show T<a+T by linarith) x)
  let F : Vec → Vec := fun z => retardedMagneticFlux s (a+T) x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) T)]
      (fun z => retardedMagneticDensity s (a+T) x (x+z) i -
        magneticMomentDensity (shiftedCurrent s a) T x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := magneticMomentDensity_actual_before hs hm ha hH x i hz0 (by simpa only [mem_ball_zero_iff] using hz)
    dsimp only [F]
    rw [divergence_add_right]
    linarith
  have hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<a+T → ContDiffAt ℝ 1 F z := by
    intro z hz hzT
    have hxy : x≠x+z := by
      intro h
      apply (norm_pos_iff.mp hz)
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    have hp : x+z ∈ retardedSpaceDomain (a+T) x := ⟨hxy,by rw [coneRadius_add]; linarith⟩
    exact ((contDiffOn_retardedMagnetic_flux hs.1 hc (by linarith) x i).contDiffAt
      ((isOpen_retardedSpaceDomain (a+T) x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) T) := (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular hT (show T<a+T by linarith) hF hi
    (retarded_magnetic_flux_tip hs.1 hc (show 0<a+T by linarith) x i)
  have hh : (∫ z in ball (0:Vec) T, divergence F z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure at hg
  linarith

lemma classical_shifted_magnetic_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
        (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) +
      (4*Real.pi)⁻¹ * (∫ n : Sphere,
        T*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlB i) -
        T*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlA i) ∂sphereMeasure) := by
  have hρj := contDiff_shifted_moments_before hs hm ha
  rw [classical_shifted_magnetic_potential_representation_before hs hm ha hT.le hH x i]
  change _ + magneticPotentialComponent (shiftedCurrent s a) i (T,x)=_
  rw [magneticPotentialComponent_ball hρj.2 hT]
  change _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T,
      magneticMomentDensity (shiftedCurrent s a) T x i z) + _)=_
  rw [integrated_magneticMomentDensity_actual_before hs hm ha hT hH x i]
  have hj0 (y : Vec) : shiftedCurrent s a (0,y)=current (fun z => s.f (a,z)) y := by
    simp only [shiftedCurrent,positiveTimeShift_eq ha (le_refl 0),add_zero]
  simp_rw [hj0]
  ring

lemma continuousOn_electricConeBoundary_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (electricConeBoundary s T x i) (Icc 0 (T/2)) := by
  have hc := hs.2.2.2.2.2.2.1
  have hE : ContDiffOn ℝ ∞ s.E (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.1.mono (fun p hp => hp.1)
  have hB : ContDiffOn ℝ ∞ s.B (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.2.mono (fun p hp => hp.1)
  have hcurl := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
    (continuousOn_slab_curl hT (hB.of_le (by decide)))
  have hfree := (continuousOn_freeWave_slab hT hE hcurl x i).mono
    (show Icc 0 (T/2) ⊆ Icc 0 T from fun a ha => ⟨ha.1,by linarith [ha.2]⟩)
  have hflux := continuousOn_electric_flux_boundary hs.1 hc hT x i
  have hdot := (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hflux)
  have hflux' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).pow 2).mul hdot)
  have hrho := continuousOn_cone_boundary_comp hT (hs.regularParticle.rho_continuous_slab hT.le) x
  have hni : Continuous (fun p : ℝ × Vec => p.2 i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_snd
  have hrho' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).mul hni.continuousOn).mul hrho)
  have hj := continuousOn_cone_boundary_comp hT (hs.regularParticle.current_continuous_slab hT.le) x
  have hji := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn hj
  have hj' := continuousOn_integral_sphere hji
  exact ((hfree.sub (hflux'.const_mul ((4*Real.pi)⁻¹))).sub
    (hrho'.const_mul ((4*Real.pi)⁻¹))).sub
      ((((continuousOn_const (c:=T)).sub continuousOn_id).mul hj').const_mul ((4*Real.pi)⁻¹))

lemma continuousOn_magneticConeBoundary_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (magneticConeBoundary s T x i) (Icc 0 (T/2)) := by
  have hc := hs.2.2.2.2.2.2.1
  have hE : ContDiffOn ℝ ∞ s.E (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.1.mono (fun p hp => hp.1)
  have hB : ContDiffOn ℝ ∞ s.B (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.2.mono (fun p hp => hp.1)
  have hcurl := ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
    (continuousOn_slab_curl hT (hE.of_le (by decide)))).neg
  have hfree := (continuousOn_freeWave_slab hT hB hcurl x i).mono
    (show Icc 0 (T/2) ⊆ Icc 0 T from fun a ha => ⟨ha.1,by linarith [ha.2]⟩)
  have hflux := continuousOn_magnetic_flux_boundary hs.1 hc hT x i
  have hdot := (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hflux)
  have hflux' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).pow 2).mul hdot)
  have hj := continuousOn_cone_boundary_comp hT (hs.regularParticle.current_continuous_slab hT.le) x
  have hterm (j k : Fin 3) := (((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).mul
    (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp continuous_snd).continuousOn)).mul
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).continuous.comp_continuousOn hj)
  have hj' := continuousOn_integral_sphere ((hterm (curlA i) (curlB i)).sub (hterm (curlB i) (curlA i)))
  exact (hfree.sub (hflux'.const_mul ((4*Real.pi)⁻¹))).add (hj'.const_mul ((4*Real.pi)⁻¹))

lemma classical_electric_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (hH : T < H) (x : Vec) (i : Fin 3) :
    s.E (T,x) i = electricConeBoundary s T x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedElectricDensity s T x (x+z) i) := by
  have hc := hs.2.2.2.2.2.2.1
  have hD : IntegrableOn (fun z => retardedElectricDensity s T x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1 hc hT.le le_rfl x)
  have hlim := (tendsto_right_of_continuousOn_Icc (show 0<T/2 by linarith)
    (continuousOn_electricConeBoundary_before hs hm hT x i)).add
    ((integral_ball_radius_tendsto hT hD).const_mul ((4*Real.pi)⁻¹))
  have heq : (fun a : ℝ => electricConeBoundary s T x i a + (4*Real.pi)⁻¹ *
      (∫ z in ball (0:Vec) (T-a), retardedElectricDensity s T x (x+z) i)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => s.E (T,x) i) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    have he := classical_shifted_electric_physical_representation_before hs hm ha.1
      (show 0<T-a by linarith [ha.2]) (by linarith) x i
    rw [show a+(T-a)=T by ring] at he
    unfold electricConeBoundary
    linarith
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds |>.symm

lemma classical_magnetic_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (hH : T < H) (x : Vec) (i : Fin 3) :
    s.B (T,x) i = magneticConeBoundary s T x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s T x (x+z) i) := by
  have hc := hs.2.2.2.2.2.2.1
  have hD : IntegrableOn (fun z => retardedMagneticDensity s T x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1 hc hT.le le_rfl x)
  have hlim := (tendsto_right_of_continuousOn_Icc (show 0<T/2 by linarith)
    (continuousOn_magneticConeBoundary_before hs hm hT x i)).add
    ((integral_ball_radius_tendsto hT hD).const_mul ((4*Real.pi)⁻¹))
  have heq : (fun a : ℝ => magneticConeBoundary s T x i a + (4*Real.pi)⁻¹ *
      (∫ z in ball (0:Vec) (T-a), retardedMagneticDensity s T x (x+z) i)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => s.B (T,x) i) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    have he := classical_shifted_magnetic_physical_representation_before hs hm ha.1
      (show 0<T-a by linarith [ha.2]) (by linarith) x i
    rw [show a+(T-a)=T by ring] at he
    unfold magneticConeBoundary
    linarith
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds |>.symm

lemma classical_electric_physical_vector_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) := by
  have hD := integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  ext i
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
  exact (classical_electric_physical_representation_before hs hm ht hH x i).trans
    (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
      smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

lemma classical_magnetic_physical_vector_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x : Vec) :
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) := by
  have hD := integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.2.2.2.1 ht.le le_rfl x
  ext i
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
  exact (classical_magnetic_physical_representation_before hs hm ht hH x i).trans
    (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
      smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

lemma classical_physical_force_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x a : Vec) :
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
  rw [classical_electric_physical_vector_before hs hm ht hH x,classical_magnetic_physical_vector_before hs hm ht hH x,
    integral_add hE hcross,hc']
  simp only [boundaryLorentzForce,cross_add_right,cross_smul_right]
  module

lemma classical_electricConeBoundary_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary (datumBoundarySolution d) t x i 0 :=
  electricConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

lemma classical_magneticConeBoundary_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary (datumBoundarySolution d) t x i 0 :=
  magneticConeBoundary_initial_congr hs.2.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.1
    hs.2.2.2.2.2.2.2.2.2.2 ht x i

lemma ClassicalBefore.energyPrefix {d : Datum} {s : Solution} {H : ℝ} (hs : ClassicalBefore d s H)
    {T : ℝ} (hT : 0 ≤ T) (hH : T ≤ H) : EnergyPrefix s T := by
  refine ⟨hs.1.mono (fun _ hz => hz.1.1),hs.2.1.mono (fun _ hz => hz.1.1),
    hs.2.2.1.mono (fun _ hz => hz.1.1),(fun t ht => hs.2.2.2.1 t ht.1),?_,?_,
    hs.2.2.2.2.2.2.1 T hT,?_,?_⟩
  · obtain ⟨F,hc,he⟩ := hs.2.2.2.2.1
    exact ⟨F,hc.mono Icc_subset_Ici_self,fun t ht => he t ht.1⟩
  · obtain ⟨F,hc,he⟩ := hs.2.2.2.2.2.1
    exact ⟨F,hc.mono Icc_subset_Ici_self,fun t ht => he t ht.1⟩
  · intro t ht x v
    have hh := (hs.2.2.2.2.2.2.2.1 t ht.1.le (ht.2.trans_le hH)).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.2.2.2.2.2.2.2.1 t ht.1.le (ht.2.trans_le hH)).2.1 x
    have hb := (hs.2.2.2.2.2.2.2.1 t ht.1.le (ht.2.trans_le hH)).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

lemma classical_boundaryLorentzForce_datum_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) {t : ℝ} (ht : 0<t) (x a : Vec) :
    boundaryLorentzForce s t x a=boundaryLorentzForce (datumBoundarySolution d) t x a := by
  have hE : electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_electricConeBoundary_datum_before hs ht x i
  have hB : magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
    ext i
    exact classical_magneticConeBoundary_datum_before hs ht x i
  simp only [boundaryLorentzForce,hE,hB]

lemma classical_retarded_force_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, ∫ v : Vec, retardedForceKernel s t x a (x+z) v := by
  rw [classical_physical_force_representation_before hs hm ht hH,classical_boundaryLorentzForce_datum_before hs ht]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  apply physical_lorentz_density hs.1 hs.2.2.2.2.2.2.1
  · intro he
    exact hz0 (add_left_cancel (show x+z=x+0 by simpa using he.symm))
  · rw [coneRadius_add]
    exact sub_nonneg.mpr (show ‖z‖≤t from (mem_ball_zero_iff.mp hz).le)

lemma classical_retarded_force_phase_integral_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ p : Phase, retardedForceKernel s t x a (x+p.1) p.2
        ∂((volume.restrict (ball (0:Vec) t)).prod volume) := by
  rw [classical_retarded_force_representation_before hs hm ht hH]
  congr 2
  symm
  exact integral_prod _ (integrable_joint_retardedForceKernel hs.1 hs.2.1.continuousOn
    hs.2.2.1.continuousOn hs.2.2.2.2.2.2.1 ht.le le_rfl x a)

lemma classical_retarded_force_phase_domain_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {t : ℝ} (ht : 0<t) (hH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ p in retardedPhaseDomain t x,
        s.f (t-‖x-p.1‖,p) • physicalPhaseForce s t x a p := by
  rw [classical_retarded_force_phase_integral_before hs hm ht hH,
    retarded_phase_translate_integral (fun p => retardedForceKernel s t x a p.1 p.2) t x]
  rfl

lemma classical_retarded_force_label_integral_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {T t : ℝ}
    (F : PhaseFlowOn s.E s.B T) (ht : t∈Icc 0 T) (ht0 : 0<t) (hH : t < H) (hTH : T ≤ H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ z in initialConeLabels t x,
        (1-dot (coneDirection x (F.retardedSource ht x z).1)
          (velocity (F.retardedSource ht x z).2))⁻¹ •
          (d.f₀ z • physicalPhaseForce s t x a (F.retardedSource ht x z)) := by
  rw [classical_retarded_force_phase_domain_before hs hm ht0 hH]
  congr 2
  have he := hs.energyPrefix (ht.1.trans ht.2) hTH
  rw [F.retarded_transport_integral he.f_smooth he.vlasov ht x]
  apply setIntegral_congr_fun (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
  intro z hz
  change _ • (s.f (0,z) • _) = _ • (d.f₀ z • _)
  rw [hs.2.2.2.2.2.2.2.2.1]
  rfl

end RVM

end

end OAI
