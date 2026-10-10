import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PhysicalInitialPoint

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

lemma exists_initial_band_mesh {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    ∃ t : Finset Position,(∀ y∈t,r≤‖y‖ ∧ ‖y‖≤2*r) ∧
      (∀ y : Position,r≤‖y‖ → ‖y‖≤2*r → ∃ z∈t,‖y-z‖≤r^3) ∧
      (t.card:ℝ)≤343/r^6 := by
  let S := {y : Position | r≤‖y‖ ∧ ‖y‖≤2*r}
  obtain ⟨t,ht,hcover,hcard⟩ := exists_quantitative_mesh S (R:=2*r) (ε:=r^3)
    (by positivity) (by positivity) (fun _ h => h.2)
  refine ⟨t,fun y hy => ht hy,fun y hy0 hy1 => hcover y ⟨hy0,hy1⟩,?_⟩
  have hroot : 2*r+r^3/3≤7*r/3 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 (n:=2)) hr.le
    nlinarith only [H]
  have Hpow := pow_le_pow_left₀ (by positivity : 0≤2*r+r^3/3) hroot 3
  have H := hcard.trans Hpow
  apply (le_div_iff₀ (pow_pos hr 6)).mpr
  have H' : (t.card:ℝ)*r^9≤343*r^3 := by nlinarith only [H]
  have HH : ((t.card:ℝ)*r^6)*r^3≤343*r^3 := by nlinarith only [H']
  exact (mul_le_mul_iff_left₀ (pow_pos hr 3)).mp HH

theorem initial_posterior_mesh_event {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (raw : Ω → Configuration n)
    {obs : Ω → B} (_ : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ x,g x^2)=1)
    {A c r s Z T : ℝ} (hA : 0≤A) (hAb : ∀ x,g x^2≤A)
    (hc : 0<c) (hr : 0<r) (hr1 : r≤1) (hs : 0<s) (hrs : r ≤ s)
    (hZ : 0≤Z) (hn : (n:ℝ)≤3*Z)
    (hpoint : ∀ y : Position,P.real {a | T≤potentialOf
      (conditionalPacketDensity P raw obs g c r s (obs a)) y}≤r^42) :
    ∃ G : Set B,MeasurableSet G ∧ P.real (obs ⁻¹' Gᶜ)≤343*r^36 ∧
      ∀ a∈G,∀ y : Position,r≤‖y‖ → ‖y‖≤2*r →
        potentialOf (conditionalPacketDensity P raw obs g c r s a) y≤T+
          (Z/r)*initialPacketModulus (A*(∫ z in Metric.ball (0:Position) 1,coulombKernel z^2)) c r := by
  obtain ⟨t,ht,hcover,hcard⟩ := exists_initial_band_mesh hr hr1
  let V : B → Position → ℝ := fun a => potentialOf (conditionalPacketDensity P raw obs g c r s a)
  let Bbad : Position → Set B := fun y => {a | T≤V a y}
  let E : Set B := ⋃ y∈t,Bbad y
  have hbad (y : Position) : MeasurableSet (Bbad y) := measurableSet_le measurable_const
    (measurable_conditionalPacketPotential_data P raw obs hg hgs hm hc hr hs y)
  have hE : MeasurableSet E := t.measurableSet_biUnion (fun y _ => hbad y)
  refine ⟨Eᶜ,hE.compl,?_,?_⟩
  · rw [compl_compl]
    have hpre : obs ⁻¹' E=⋃ y∈t,obs ⁻¹' Bbad y := by simp only [E,preimage_iUnion]
    rw [hpre]
    calc
      _≤∑ y∈t,P.real (obs ⁻¹' Bbad y) := measureReal_biUnion_finset_le _ _
      _≤∑ _y∈t,r^42 := Finset.sum_le_sum (fun y _ => hpoint y)
      _=(t.card:ℝ)*r^42 := by simp
      _≤(343/r^6)*r^42 := mul_le_mul_of_nonneg_right hcard (by positivity)
      _=343*r^36 := by field_simp
  · intro a ha y hy0 hy1
    obtain ⟨z,hz,hzy⟩ := hcover y hy0 hy1
    have hz' : V a z<T := by
      have Hz : a∉Bbad z := fun H => ha (Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,H⟩⟩)
      exact lt_of_not_ge Hz
    have HL := initial_potential_mesh_modulus hg hgs hm hA hAb hc hr hs hrs hZ hn
      (ProbabilityTheory.condDistrib raw obs P a) hzy
    change potentialOf (conditionalPacketDensity P raw obs g c r s a) y≤_
    have HH := le_abs_self (V a y-V a z)
    change |V a y-V a z|≤_ at HL
    linarith only [HL,HH,hz']
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

lemma retainedInverseOffset_seventh_tendsto (D : ℝ) :
    Tendsto (fun r => retainedInverseOffset D r*r^7) (𝓝[>] 0) (𝓝 0) := by
  have H := (retainedInverseOffset_scaled_tendsto D).mul
    (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/50))
  simp only [mul_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0<r := hr
  rw [mul_assoc,←Real.rpow_add hr']
  norm_num [Real.rpow_natCast]

def initialAtomicRadius (ε Z : ℝ) : ℝ := ε*Z^(-(1/3:ℝ))

lemma initialAtomicRadius_pos {ε Z : ℝ} (hε : 0<ε) (hZ : 0<Z) :
    0 < initialAtomicRadius ε Z := mul_pos hε (Real.rpow_pos_of_pos hZ _)

lemma initialAtomicRadius_tendsto {ε : ℝ} (hε : 0<ε) :
    Tendsto (initialAtomicRadius ε) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun Z : ℝ => ε*Z^(-(1/3:ℝ))) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).const_mul ε
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    exact initialAtomicRadius_pos hε hZ

lemma initialAtomicRadius_cubic {ε Z : ℝ} (hZ : 0<Z) :
    Z*(initialAtomicRadius ε Z)^3=ε^3 := by
  rw [initialAtomicRadius,mul_pow,←Real.rpow_mul_natCast hZ.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

lemma initialAtomicRadius_seventh {ε Z : ℝ} (hZ : 0<Z) :
    Z^(7/3:ℝ)*(initialAtomicRadius ε Z)^7=ε^7 := by
  rw [initialAtomicRadius,mul_pow,←Real.rpow_mul_natCast hZ.le]
  calc
    _=ε^7*(Z^(7/3:ℝ)*Z^((-(1/3:ℝ))*7)) := by ring_nf
    _=ε^7 := by rw [←Real.rpow_add hZ]; norm_num

lemma initialAtomicRadius_offset_eventually (D : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,
      retainedInverseOffset D (initialAtomicRadius ε Z)≤Z^(7/3:ℝ) := by
  have H := (retainedInverseOffset_seventh_tendsto D).comp (initialAtomicRadius_tendsto hε)
  have he := H.eventually (gt_mem_nhds (pow_pos hε 7))
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  apply (mul_le_mul_iff_left₀ (pow_pos (initialAtomicRadius_pos hε hZ) 7)).mp
  rw [initialAtomicRadius_seventh hZ]
  exact hz.le

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma initialAtomicRadius_potential_scale {ε Z : ℝ} (hZ : 0<Z) :
    Z^(4/3:ℝ)*initialAtomicRadius ε Z=ε*Z := by
  unfold initialAtomicRadius
  calc
    _=ε*(Z^(4/3:ℝ)*Z^(-(1/3:ℝ))) := by ring
    _=ε*Z := by rw [←Real.rpow_add hZ]; norm_num

theorem physical_initial_event : ∃ εmax : ℝ,0<εmax ∧
    ∀ {ε : ℝ},0<ε → ε≤εmax →
    ∀ (D : ℝ) (g₀ : 𝓢(Position,ℝ)),(∫ w,g₀ w^2)=1 →
    (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
    ∀ {c s : ℝ},0<c → 0<s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    ∃ Zmin : ℕ,∀ (Z : ℕ),Zmin≤Z → ∀ (hZ : 1≤Z) {N J : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → (N+1:ℝ)≤3*(Z:ℝ) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r₀ := initialAtomicRadius ε Z
    let r := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (Fin J → UnorderedArray (N+1)),MeasurableSet G ∧
      P.real (tailObservation r 0 ⁻¹' Gᶜ)≤343*r₀^35 ∧
      ∀ a∈G,∀ y : Position,r₀≤‖y‖ → ‖y‖≤2*r₀ →
        potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s a) y≤
          (1/10:ℝ)*(Z:ℝ)/r₀ := by
  obtain ⟨C,hC,HC⟩ := physical_initial_potential_point
  refine ⟨1/(20*C),by positivity,?_⟩
  intro ε hε hεmax D g₀ hm hrad hg c s hc hs hq
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound g₀.continuous hgs
  let I := ∫ z in Metric.ball (0:Position) 1,coulombKernel z^2
  have ht := initialAtomicRadius_tendsto hε
  have hmod := (initialPacketModulus_tendsto (A*I) c).comp ht
  have hsmall : ∀ᶠ Z : ℝ in atTop,0<Z ∧ initialAtomicRadius ε Z≤1 ∧
      initialAtomicRadius ε Z ≤ s ∧
      retainedInverseOffset D (initialAtomicRadius ε Z)≤Z^(7/3:ℝ) ∧
      initialPacketModulus (A*I) c (initialAtomicRadius ε Z)≤1/20 := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hs),
      initialAtomicRadius_offset_eventually D hε,
      hmod.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20))] with Z hZ h1 hS hδ hM
    exact ⟨hZ,h1.le,hS.le,hδ,hM.le⟩
  obtain ⟨Zmin,hZmin⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hsmall)
  refine ⟨Zmin,?_⟩
  intro Z hZm hZ N J ψ g hd hn hmin E hE hbase hnum
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  obtain ⟨hZr,hr1,hrs,hδ,hM⟩ := hZmin Z hZm
  have hr := initialAtomicRadius_pos hε hZr
  let P := observationLaw J (rawLaw ψ)
  let r₀ := initialAtomicRadius ε Z
  let r := fun k : Fin J => r₀*2^k.val
  have HA : ∀ x,(g₀ x)^2≤A := hAb
  obtain ⟨G,hG,hp,HG⟩ := initial_posterior_mesh_event P Prod.fst (measurable_tailObservation r 0)
    g₀.continuous hgs hm hA HA hc hr hr1 hs hrs hZr.le (by exact_mod_cast hnum)
    (HC Z hZ hd hn hmin hE hbase hnum g₀ hm hrad hg hc hr hs hq hδ)
  refine ⟨G,hG,?_,?_⟩
  · exact hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le hr1 (by decide : 35≤36)) (by norm_num))
  · intro a ha y hy0 hy1
    have H := HG a ha y hy0 hy1
    have hCe : C*ε≤1/20 := by
      have hh := (le_div_iff₀ (by positivity : 0<20*C)).mp hεmax
      nlinarith only [hh]
    have hscale : C*(Z:ℝ)^(4/3:ℝ)=(Z:ℝ)/r₀*(C*ε) := by
      apply (mul_right_cancel₀ hr.ne')
      rw [mul_assoc,initialAtomicRadius_potential_scale hZr]
      dsimp only [r₀]
      field_simp
    change potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s a) y≤_
    rw [hscale] at H
    have HM := mul_le_mul_of_nonneg_left (add_le_add hCe hM) (div_nonneg hZr.le hr.le)
    dsimp only [I] at HM
    calc
      _≤(Z:ℝ)/r₀*(C*ε+initialPacketModulus (A*I) c r₀) := by linarith only [H]
      _≤(Z:ℝ)/r₀*(1/20+1/20) := HM
      _=(1/10:ℝ)*(Z:ℝ)/r₀ := by ring
end NeutralAtom
end

end

end OAI
