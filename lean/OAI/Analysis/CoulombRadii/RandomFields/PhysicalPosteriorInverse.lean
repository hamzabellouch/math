import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.InverseEventContradiction
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorDataMeasurable

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

lemma rawCount_mono {n : ℕ} {S T : Set Position} (x : Configuration n)
    (h : S ⊆ T) : rawCount S x ≤ rawCount T x := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hS : x i ∈ S
  · simp only [Set.indicator_of_mem hS, Set.indicator_of_mem (h hS)]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hS]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem physical_posterior_matching_count (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    (r : Fin J → ℝ), (∀ k, 0 ≤ r k) → ∀ {j : ℕ} (k : Fin J), j ≤ k.val →
    ∀ (y : Position) (a m : ℝ), 0 ≤ a →
    ∀ᵐ z ∂observationLaw J ν,
      rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*a^(6/5:ℝ)+2*(Real.sqrt 3*(r k)^(101/100:ℝ))))
        (observedOrdered r k z) ≤ m →
      |conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation r j) g₀ c r₀ s
        (tailObservation r j z) y-rawPacketDensity g₀ c r₀ s (observedOrdered r k z) y| ≤
        (K₀/(packetWidth c r₀ s y)^4*(Real.sqrt 3*(r k)^(101/100:ℝ)))*m := by
  obtain ⟨K₀,hK₀,H⟩ := physical_posterior_kernel_matching g₀ hg hm
  refine ⟨K₀,hK₀,?_⟩
  intro c r₀ s hc hr₀ hs hscale n J ν inst r hr j k hk y a m ha
  have hrk := hr k
  filter_upwards [H hc hr₀ hs hscale ν r hr k hk y] with z hz hcz
  apply hz.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (rawCount_mono (observedOrdered r k z) ?_).trans hcz
  apply Metric.closedBall_subset_closedBall
  have hb : 0 ≤ a^(6/5:ℝ) := Real.rpow_nonneg ha _
  have he : 0 ≤ Real.sqrt 3*(r k)^(101/100:ℝ) := by positivity
  linarith

theorem physical_posterior_inverse_point (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c A κ Λ M V hl hh η : ℝ}
    (hD : 0 ≤ D) (hc : 0<c) (hA : 0<A) (hκ : 0<κ) (hΛ : 0 ≤ Λ)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hη : 0<η) (hηl : η<hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ}, 0<r₀ → 0<s → s<s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ (j : ℕ), r₀*2^j ≤ s → ∀ (k : RetainedScales J j) (y : Position), y≠0 →
    r₀ ≤ ‖y‖ → Coulomb.atomicCellScale y ≤ A*(r₀*2^j) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let a := Coulomb.atomicCellScale y
    let w := packetWidth c r₀ s y
    let ell := (r₀*2^k.val.val)^(101/100:ℝ)
    let count := fun z : ObservationSample (N+1) J =>
      rawCount (Metric.closedBall y (2*w+2*a^(6/5:ℝ)+2*(Real.sqrt 3*ell)))
        (observedOrdered (fun l : Fin J => r₀*2^l.val) k.val z)
    let μ := fun z : ObservationSample (N+1) J =>
      conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
        (tailObservation (fun l : Fin J => r₀*2^l.val) j) g₀ c r₀ s
        (tailObservation (fun l : Fin J => r₀*2^l.val) j z)
    let field := fun z : ObservationSample (N+1) J => (Z:ℝ)*coulombKernel y-potentialOf (μ z) y
    κ*a^(1+packetExponent) ≤ w → w/a ≤ V*s^packetExponent →
    ell ≤ Λ*a^(101/100:ℝ) → ∀ {h : ℝ}, h∈Icc hl hh →
    (observationLaw J (rawLaw ψ)).real
      {z | count z ≤ M*a^(-3:ℝ) ∧ Coulomb.tfScalarDensity h/a^6 ≤ μ z y ∧ field z ≤ (h-2*η)/a^4}
        ≤ (r₀*2^j)^42 ∧
    (observationLaw J (rawLaw ψ)).real
      {z | count z ≤ M*a^(-3:ℝ) ∧ μ z y ≤ Coulomb.tfScalarDensity h/a^6 ∧ (h+2*η)/a^4 ≤ field z}
        ≤ (r₀*2^j)^42 := by
  obtain ⟨K₀,hK₀,Hmatch⟩  := physical_posterior_matching_count g₀ hg hm
  obtain ⟨s₀,hs₀,hs₀1,Hfail⟩ := physical_retained_inverse_event g₀ hg hm hrad
    hD hc hA hκ hΛ hM hV hK₀.le hη hηl hlh
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale j hrj k y hy hry hya
  dsimp only
  intro hw hwa hell h hh'
  have := rawLaw_isProbability hd.2.2.1 hn
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun l => r₀*2^l.val
  let obs : ObservationSample (N+1) J → (Fin J → UnorderedArray (N+1)) := tailObservation r j
  let a := Coulomb.atomicCellScale y
  let w := packetWidth c r₀ s y
  let ell := (r k.val)^(101/100:ℝ)
  let m := M*a^(-3:ℝ)
  let ball := Metric.closedBall y (2*w+2*a^(6/5:ℝ)+2*(Real.sqrt 3*ell))
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := by
    apply HasCompactSupport.intro (K:=Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    exact hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)
  let μ := conditionalPacketDensity P Prod.fst obs g₀ c r₀ s
  let H := fun datum => (Z:ℝ)*coulombKernel y-potentialOf (μ datum) y
  have hH : Measurable H := measurable_const.sub
    (measurable_conditionalPacketPotential_data P Prod.fst obs g₀.continuous hgs hm hc hr₀ hs y)
  have ha : 0 < a := Coulomb.atomicCellScale_pos hy
  have hmatch := Hmatch hc hr₀ hs hscale (rawLaw ψ) r
    (fun _ => by dsimp [r]; positivity) k.val k.property y a m ha.le
  have Hfail' (B : Set (Fin J → UnorderedArray (N+1))) :=
    Hfail Z hZ hd hn hmin hE hbase hr₀ hs hss hscale j hrj k y hy hry hya hw hwa hell hh' (B:=B)
  exact retained_inverse_gate_transfer (rawLaw ψ) r k measurableSet_closedBall
    (measurable_packetKernel_center g₀.continuous hc hr₀ hs y) (μ:=fun datum => μ datum y) hH
    (by simpa only [rawPacketDensity] using hmatch)
    (fun hB hcnt hgate hfld => (Hfail' _ hB hcnt (Or.inl ⟨hgate,hfld⟩)).le)
    (fun hB hcnt hgate hfld => (Hfail' _ hB hcnt (Or.inr ⟨hgate,hfld⟩)).le)
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace NeutralAtom

lemma mixturePacketDensity_measurable {n : ℕ} (ν : Measure (Configuration n)) [SFinite ν]
    {g : Position → ℝ} (hg : Continuous g) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) :
    Measurable (mixturePacketDensity ν g c r₀ s) :=
  (continuous_rawPacketDensity hg hc hr hs).stronglyMeasurable.integral_prod_left'.measurable

lemma conditionalPacketPotential_continuous {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (datum : B) :
    Continuous (potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum)) := by
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  exact potentialOf_continuous (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketDensity_nonneg P raw obs g hc hr hs datum) (HA datum)

lemma measurable_conditionalPacketPotential_joint {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) :
    Measurable (fun dy : B × Position => potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s dy.1) dy.2) := by
  let u := fun y : Position => fun datum : B => potentialOf
    (conditionalPacketDensity P raw obs g c r₀ s datum) y
  have hcont : ∀ datum, Continuous (fun y => u y datum) :=
    conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs
  have hmeas : ∀ y, Measurable (u y) :=
    measurable_conditionalPacketPotential_data P raw obs hg hgs hm hc hr hs
  have H : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  change Measurable (Function.uncurry u ∘ (Prod.swap : B × Position → Position × B))
  exact Measurable.comp H measurable_swap

lemma atomic_screened_ballCloud_submean {ρ : Position → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) (hp : ∀ x,0≤ρ x) {A : ℝ} (hA : ∀ x,ρ x≤A)
    (Z : ℝ) {a : ℝ} (ha : 0<a) (y : Position) (hy : a≤‖y‖) :
    Z*coulombKernel y-potentialOf ρ y ≤ ∫ z,
      (Z*coulombKernel z-potentialOf ρ z)*Coulomb.ballCloud y a 1 z := by
  have hnI : Integrable (fun z => coulombKernel z*Coulomb.ballCloud y a 1 z) := by
    have H := Coulomb.coulomb_convolution_integrable (Coulomb.ballCloud_integrable a 1 y)
      (Coulomb.ballCloud_measurable a 1 y) (fun z => Coulomb.uniformBall_nonneg ha zero_le_one (z-y))
      (fun z => Coulomb.uniformBall_le ha zero_le_one (z-y)) ha (0:Position)
    simpa only [Coulomb.coulombKernel,coulombKernel,zero_sub,norm_neg] using H
  have he : (∫ z,coulombKernel z*Coulomb.ballCloud y a 1 z)=coulombKernel y := by
    have H := Coulomb.ballCloud_coulomb ha zero_le_one y (0:Position) (by simpa only [zero_sub,norm_neg] using hy)
    simpa only [Coulomb.coulombKernel,coulombKernel,zero_sub,norm_neg,one_mul] using H
  have hK := Coulomb.coulomb_convolution_integrable hi hm hp hA (by norm_num : (0:ℝ)<1) y
  have H := Coulomb.potentialOf_ballCloud_le hi hm hp ha y hK
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (hnI.const_mul Z) (Coulomb.potentialOf_ballCloud_integrable hi hm ha y),
    integral_const_mul,he]
  linarith

lemma conditionalPacketField_submean {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (datum : B)
    (Z : ℝ) {a : ℝ} (ha : 0<a) (y : Position) (hy : a≤‖y‖) :
    Z*coulombKernel y-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y ≤
      (4*Real.pi/3*a^3)⁻¹*∫ z in Metric.closedBall y a,
      Z*coulombKernel z-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) z := by
  let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
  have hi : Integrable ρ := mixturePacketDensity_integrable hg hm hc hr hs _
  have hρm : Measurable ρ := mixturePacketDensity_measurable _ hg hc hr hs
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  have hp : ∀ x,0≤ρ x := conditionalPacketDensity_nonneg P raw obs g hc hr hs datum
  have H := atomic_screened_ballCloud_submean hi hρm hp (HA datum) Z ha y hy
  rw [Coulomb.integral_ballCloud] at H
  exact H
end NeutralAtom

end

end OAI
