import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicGlobalScale

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_initial_potential_point : ∃ C : ℝ,0<C ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E D : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → (N+1:ℝ)≤3*(Z:ℝ) →
    ∀ (g₀ : 𝓢(Position,ℝ)),(∫ w,g₀ w^2)=1 →
    (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
    ∀ {c r₀ s : ℝ},0<c → 0<r₀ → 0<s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    retainedInverseOffset D r₀≤(Z:ℝ)^(7/3:ℝ) → ∀ y : Position,
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J => r₀*2^k.val
    P.real {a | C*(Z:ℝ)^(4/3:ℝ)≤potentialOf
      (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s (tailObservation r 0 a)) y}≤r₀^42 := by
  obtain ⟨C,hC,HC⟩ := atomic_global_master_potential
  refine ⟨2*C,by positivity,?_⟩
  intro N J Z hZ ψ g hd hn hmin E D hE hbase hnum g₀ hm hrad hg c r₀ s hc hr₀ hs hq hoff y
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun k => r₀*2^k.val
  let V := fun datum : Fin J → UnorderedArray (N+1) =>
    potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s datum) y
  let B : Set (Fin J → UnorderedArray (N+1)) := {datum | 2*C*(Z:ℝ)^(4/3:ℝ)≤V datum}
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hV : Measurable V := measurable_conditionalPacketPotential_data P Prod.fst
    (tailObservation r 0) g₀.continuous hgs hm hc hr₀ hs y
  have hB : MeasurableSet B := measurableSet_le measurable_const hV
  change P.real (tailObservation r 0 ⁻¹' B)≤r₀^42
  by_contra H
  have hp : r₀^42<P.real (tailObservation r 0 ⁻¹' B) := lt_of_not_ge H
  have hp0 : 0<P.real (tailObservation r 0 ⁻¹' B) := (pow_pos hr₀ 42).trans hp
  have hp1 : P.real (tailObservation r 0 ⁻¹' B)≤1 := measureReal_le_one
  have hr (k : Fin J) : 0<r k := by dsimp [r]; positivity
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn r hr 0 hB
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J 0 => (r₀*2^k.val.val)^(101/100:ℝ))
    (fun k => Real.rpow_pos_of_pos (by positivity) _)
    (hB.preimage (measurable_retainedTailObservation 0))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp0)
  have hoff' := retained_event_offset_le (D:=D) hr₀ J 0
    (by simpa only [pow_zero,mul_one] using hp.le) hp1
  have hEn : E≤0 := EReal.coe_le_coe_iff.mp (hE.trans (Coulomb.atom_unrestricted_bottom_nonpos Z hZ))
  have hue' : Coulomb.form (Coulomb.atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) := by
    rw [←hpEq] at hue
    simp only [pow_zero,mul_one] at hoff'
    linarith only [hue,hoff',hoff,hEn]
  have Hupper := HC Z hZ u hu hum hnum hue' g₀ hm hrad hg hc hr₀ hs hq y
  have Hmean := retainedEvent_potential_mean hd.2.2.1 hn r hr 0 hB u hum hlaw
    g₀.continuous hgs hm hc hr₀ hs y
  have Hlower := le_normalized_event (hB.preimage (measurable_tailObservation r 0))
    (conditionalPacketPotential_integrable P (rawLaw ψ) (observationLaw_rawProjection _)
      (measurable_tailObservation r 0) g₀.continuous hgs hm hc hr₀ hs y) hp0
    (Eventually.of_forall (fun a (ha : a∈tailObservation r 0 ⁻¹' B) => ha))
  rw [←Hmean] at Hlower
  have hz : 0<(Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hZ)
  have hcpos : 0<C*(Z:ℝ)^(4/3:ℝ) := mul_pos hC (Real.rpow_pos_of_pos hz _)
  nlinarith only [Hupper,Hlower,hcpos]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma mixturePacketDensity_explicit_bound {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {A c r s : ℝ}
    (hA : 0≤A) (hAb : ∀ x,g x^2≤A) (hc : 0<c) (hr : 0<r) (hs : 0<s) (hrs : r ≤ s)
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν] (y : Position) :
    mixturePacketDensity ν g c r s y≤(n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A) := by
  have H := integral_mono (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
    (integrable_const ((n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A)))
    (fun x => by simpa only [min_eq_left hrs] using rawPacketDensity_bound hA hAb hc hr hs x y)
  simpa only [mixturePacketDensity,integral_const,probReal_univ,one_smul] using H

lemma initial_width_modulus_identity {c r : ℝ} (_ : 0<c) (hr : 0<r) :
    (c*r*r^packetExponent)^(-3:ℤ)*r^4=(c^3)⁻¹*r^(1-3*packetExponent) := by
  have hwidth : c*r*r^packetExponent=c*r^(1+packetExponent) := by
    rw [Real.rpow_add hr,Real.rpow_one]; ring
  rw [hwidth,zpow_neg,zpow_ofNat,mul_pow,←Real.rpow_mul_natCast hr.le]
  calc
    _=(c^3)⁻¹*(r^4/r^((1+packetExponent)*3)) := by
      simp only [mul_inv_rev,div_eq_mul_inv]
      ring_nf
    _=_ := by
      rw [←Real.rpow_natCast r 4,←Real.rpow_sub hr]
      congr 2
      ring

def initialPacketModulus (A c r : ℝ) : ℝ :=
  3*(A*(c^3)⁻¹*r^(1-3*packetExponent)+r^4)

lemma initialPacketModulus_tendsto (A c : ℝ) :
    Tendsto (initialPacketModulus A c) (𝓝[>] 0) (𝓝 0) := by
  have H := (((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
    (0:ℝ)<1-3*packetExponent)).const_mul (A*(c^3)⁻¹)).add
    ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow 4)).const_mul 3
  convert H using 1 <;> simp only [mul_zero,zero_pow (by decide : 4≠0),add_zero,id_eq]
  funext r
  rfl

theorem initial_potential_mesh_modulus {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ x,g x^2)=1)
    {A c r s Z : ℝ} (hA : 0≤A) (hAb : ∀ x,g x^2≤A)
    (hc : 0<c) (hr : 0<r) (hs : 0<s) (hrs : r ≤ s) (_ : 0≤Z) (hn : (n:ℝ)≤3*Z)
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    {x y : Position} (hxy : ‖x-y‖≤r^3) :
    |potentialOf (mixturePacketDensity ν g c r s) x-potentialOf (mixturePacketDensity ν g c r s) y|≤
      (Z/r)*initialPacketModulus (A*(∫ z in Metric.ball (0:Position) 1,coulombKernel z^2)) c r := by
  let I := ∫ z in Metric.ball (0:Position) 1,coulombKernel z^2
  have hI : 0≤I := integral_nonneg (fun _ => sq_nonneg _)
  have H := potentialOf_lipschitz_bound (mixturePacketDensity_integrable hg hm hc hr hs ν)
    (mixturePacketDensity_nonneg ν g hc hr hs)
    (mixturePacketDensity_explicit_bound hg hgs hA hAb hc hr hs hrs ν) x y
  rw [mixturePacketDensity_mass hg hm hc hr hs ν,Real.norm_eq_abs] at H
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg n
  calc
    _≤((n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A)*I+(n:ℝ))*‖x-y‖ := H
    _≤((n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A)*I+(n:ℝ))*r^3 := by gcongr
    _=(n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*(A*I)+1)*r^3 := by ring
    _≤(3*Z)*((c*r*r^packetExponent)^(-3:ℤ)*(A*I)+1)*r^3 := by gcongr
    _=(Z/r)*initialPacketModulus (A*I) c r := by
      have He := initial_width_modulus_identity hc hr
      apply (mul_right_cancel₀ hr.ne')
      dsimp only [initialPacketModulus]
      calc
        _=3*Z*((A*I)*((c*r*r^packetExponent)^(-3:ℤ)*r^4)+r^4) := by ring
        _=3*Z*((A*I)*((c^3)⁻¹*r^(1-3*packetExponent))+r^4) := by rw [He]
        _=_ := by field_simp
end NeutralAtom
end

end

end OAI
