import OAI.MathematicalPhysics.Boltzmann.Branching.SubmersionNullPreimage
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Separation.Regular

namespace OAI

/-! # Transport of the compact submersion estimate to the actual parameter space -/

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasurableSpace E] [BorelSpace E]
  [MeasureSpace P] [BorelSpace P] [IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [IsAddHaarMeasure (volume : Measure Q)]

/-- The domain coordinates may differ from the output plus complementary coordinates.
Only compact-local convergence of the derivatives is needed. -/
theorem compact_pullback_zero_coordinates (e : E ≃L[ℝ] P × Q)
    {μ : Measure E} [IsAddHaarMeasure μ]
    {O K Z : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O) (hZ : μ Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Surjective (φ' x))
    (hconv : ∀ C : Set E, IsCompact C → C ⊆ O → TendstoUniformlyOn Φ' φ' atTop C)
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x) ∂μ) atTop (𝓝 0) := by
  let ν : Measure (P × Q) := (volume : Measure P).prod volume
  let em := e.toHomeomorph.toMeasurableEquiv
  have hmap : μ.map e = addHaarScalarFactor (μ.map e) ν • ν :=
    isAddLeftInvariant_eq_smul _ _
  have hZ' : ν (e '' Z) = 0 := by
    apply (absolutelyContinuous_isAddHaarMeasure ν (μ.map e))
    change (μ.map em) (e '' Z) = 0
    rw [em.map_apply]
    simpa only [em,Homeomorph.toMeasurableEquiv_coe,ContinuousLinearEquiv.coe_toHomeomorph,
      e.injective.preimage_image] using hZ
  let Oe := e.symm ⁻¹' O
  have hOe : IsOpen Oe := hO.preimage e.symm.continuous
  have hKe : IsCompact (e '' K) := hK.image e.continuous
  have hKeO : e '' K ⊆ Oe := by
    rintro _ ⟨x,hx,rfl⟩
    simpa only [Oe,mem_preimage,e.symm_apply_apply] using hKO hx
  obtain ⟨U,hU,hKU,hUO⟩ := hKe.exists_isOpen_closure_subset (hOe.mem_nhdsSet.mpr hKeO)
  have hUO' : U ⊆ Oe := subset_closure.trans hUO
  let D := fun n y => (Φ' n (e.symm y)).comp e.symm.toContinuousLinearMap
  let D₀ := fun y => (φ' (e.symm y)).comp e.symm.toContinuousLinearMap
  let precomp : (E →L[ℝ] P) →L[ℝ] ((P × Q) →L[ℝ] P) :=
    (ContinuousLinearMap.compL ℝ (P × Q) E P).flip e.symm.toContinuousLinearMap
  have hd : ∀ n, ∀ y ∈ U, HasFDerivAt (fun y => Φ n (e.symm y)) (D n y) y := by
    intro n y hy
    exact (hder n (e.symm y) (hUO' hy)).comp y e.symm.hasFDerivAt
  have hc : ∀ y ∈ U, ContinuousAt D₀ y := by
    intro y hy
    exact precomp.continuous.continuousAt.comp
      ((hcont (e.symm y) (hUO' hy)).comp e.symm.continuousAt)
  have hr : ∀ y ∈ e '' K \ e '' Z, Surjective (D₀ y) := by
    rintro y ⟨⟨x,hx,rfl⟩,hz⟩
    have hxn : x ∉ Z := fun h => hz ⟨x,h,rfl⟩
    intro w
    obtain ⟨z,hz⟩ := hreg x ⟨hx,hxn⟩ w
    refine ⟨e z,?_⟩
    change φ' (e.symm (e x)) (e.symm (e z)) = w
    simpa only [e.symm_apply_apply] using hz
  have hv : ∀ y ∈ U, ∀ r > 0, ball y r ⊆ U →
      TendstoUniformlyOn D D₀ atTop (ball y r) := by
    intro y hy r hr hball
    have hclosed : closedBall y r ⊆ Oe := by
      rw [← closure_ball y hr.ne']
      exact (closure_mono hball).trans hUO
    let C := e.symm '' closedBall y r
    have hC : IsCompact C := (isCompact_closedBall y r).image e.symm.continuous
    have hCO : C ⊆ O := by
      rintro _ ⟨z,hz,rfl⟩
      exact hclosed hz
    have hv₁ := (hconv C hC hCO).comp e.symm
    have hv₂ := precomp.uniformContinuous.comp_tendstoUniformlyOn hv₁
    exact hv₂.mono (fun z hz => ⟨z,ball_subset_closedBall hz,rfl⟩)
  have ht := compact_surjective_pullback_zero hU hKe hKU hZ' hd hc hr hv
    hB hM hg (fun n y hy => hρ n (e.symm y) (hUO' hy)) hgM hL
  have hscale := ENNReal.Tendsto.const_mul
    (a := (addHaarScalarFactor (μ.map e) ν : ℝ≥0∞)) ht (Or.inr ENNReal.coe_ne_top)
  simp only [mul_zero] at hscale
  convert hscale using 1
  funext n
  have heq := em.restrict_map μ (e '' K)
  have hi := lintegral_map_equiv
    (fun y => ρ n (e.symm y)*g n (Φ n (e.symm y))) em
    (μ := μ.restrict (em ⁻¹' (e '' K)))
  rw [← heq] at hi
  simp only [em,Homeomorph.toMeasurableEquiv_coe,ContinuousLinearEquiv.coe_toHomeomorph] at hi
  rw [hmap,Measure.restrict_smul,lintegral_smul_measure] at hi
  simpa only [e.injective.preimage_image,e.symm_apply_apply,ENNReal.smul_def,smul_eq_mul,ν] using hi.symm

end BoltzmannNonuniqueness.GainPullback

end

end OAI
