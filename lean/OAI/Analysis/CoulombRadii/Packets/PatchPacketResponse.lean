import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalDensity
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchResponse
import OAI.Analysis.CoulombRadii.Packets.PatchKernelDuality

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

theorem master_kernel_patch_response (g : 𝓢(NeutralAtom.Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z, g z^2)=1) :
    ∃ C D E : ℝ, 0<C ∧ 0<D ∧ 0<E ∧
    ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent≤1/4 →
    ∀ {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
      {a b t : ℝ} (ha : 0<a) (hb : 0<b) (_ : 18*b≤a)
      (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
      (hn : ∀ j, 20*a≤‖S.position j-y‖),
    2*NeutralAtom.packetWidth c r₀ s y≤a →
    4*NeutralAtom.packetWidth c r₀ s y<t-4*b →
    ∀ (spin : Spins m) (x : Configuration m),
    SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖} →
    let w := NeutralAtom.packetWidth c r₀ s y
    let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
    let v := patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y
    let d := C*(2*w/a)*((a^4)⁻¹+max (-v) 0)
    let e := Real.sqrt ((D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x)
    let I := ∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*χ z
    tfScalarDensity (v-d)*(∫ z, χ z)-e≤I ∧
    I≤tfScalarDensity (v+d)*(∫ z, χ z)+e ∧
    |(∫ z, χ z)-1|≤E*(c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent) := by
  obtain ⟨C,hC,HC⟩ := exists_patch_tested_reaction_enclosure
  obtain ⟨D,hD,HD⟩ := master_kernel_patch_gap g hg hm
  obtain ⟨E,hE,HE⟩ := NeutralAtom.master_kernel_estimates g hg hm
  refine ⟨C,D,E,hC,hD,hE,?_⟩
  intro c r₀ s hc hr hs hq J m k S u a b t ha hb hsmall ht y hn hw hball spin x hcs
  let w := NeutralAtom.packetWidth c r₀ s y
  let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht.2 y hn)
  let ρ := localTFDensity measurableSet_ball W
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  have hwp : 0<w := NeutralAtom.packetWidth_pos hc hr hs y
  obtain ⟨hsp,hamp,_,hχi,hχmass⟩ := HE hc hr hs hq y
  have hχm : Measurable χ := (((NeutralAtom.continuous_packetKernel g.continuous hc hr hs).comp
    (continuous_id.prodMk (continuous_const (y := y)))).measurable)
  have Hresponse := HC S (u.coreSlice spin x).normalized ha hb hsmall ht y hcs hn
    (show 0≤2*w by positivity) hw χ hχm hχi
    (fun z => NeutralAtom.packetKernel_nonneg g hc hr hs z y) (E/w^3) hamp
    (fun z hz => by simpa only [norm_sub_rev] using hsp z hz)
  have Hdual := HD hc hr hs hq S u ha hb ht.2 y hn hball spin x
  have hρi : Integrable ρ := (tfExtend_integrable measurableSet_ball (localTFMinimizer measurableSet_ball W)).congr
    (tfDensity_ae_tfExtend measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)).symm
  have htestρ : Integrable (fun z => ρ z*χ z) := hρi.mul_bdd hχm.aestronglyMeasurable
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hamp z))
  have htestσ : Integrable (fun z => σ z*χ z) :=
    (retainedFineDensity_integrable hb _ _).mul_bdd hχm.aestronglyMeasurable
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hamp z))
  have heq : (∫ z, (σ z-ρ z)*χ z)=(∫ z, σ z*χ z)-(∫ z, ρ z*χ z) := by
    simp_rw [sub_mul]
    rw [integral_sub htestσ htestρ]
  change (∫ z, (σ z-ρ z)*χ z)^2≤(D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x at Hdual
  rw [heq] at Hdual
  have hpos : 0≤(D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x :=
    mul_nonneg (by positivity) (patchSliceTFGap_nonneg S u ha hb ht.2 y hn spin x)
  have Habs : |(∫ z, σ z*χ z)-(∫ z, ρ z*χ z)|≤
      Real.sqrt ((D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hpos]
    exact Hdual
  have HH := abs_le.mp Habs
  dsimp only at Hresponse ⊢
  refine ⟨?_,?_,hχmass⟩ <;> dsimp only [ρ,W,σ,χ,w] at Hresponse HH ⊢ <;> linarith [Hresponse.1,Hresponse.2]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

theorem master_kernel_patch_array_response (g : 𝓢(NeutralAtom.Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z, g z^2)=1) :
    ∃ C D E F : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧
    ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent≤1/4 →
    ∀ {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
      {a b t : ℝ} (ha : 0<a) (hb : 0<b) (_ : 18*b≤a)
      (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
      (hn : ∀ j, 20*a≤‖S.position j-y‖),
    2*NeutralAtom.packetWidth c r₀ s y≤a →
    ∀ (spin : Spins m) (x : Configuration m),
    SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖} →
    let w := NeutralAtom.packetWidth c r₀ s y
    let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
    let v := patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y
    let d := C*(2*w/a)*((a^4)⁻¹+max (-v) 0)
    let e := Real.sqrt ((D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      (F/w^4*(2*b))*localCount (Metric.closedBall y (2*w+2*b)) x
    tfScalarDensity (v-d)*(∫ z, χ z)-e≤∑ i, χ (position x i) ∧
    (∑ i, χ (position x i))≤tfScalarDensity (v+d)*(∫ z, χ z)+e ∧
    |(∫ z, χ z)-1|≤E*(c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent) := by
  obtain ⟨C,D,E,hC,hD,hE,H⟩ := master_kernel_patch_response g hg hm
  obtain ⟨F,hF,HF⟩ := NeutralAtom.master_kernel_estimates g hg hm
  refine ⟨C,D,E,F,hC,hD,hE,hF,?_⟩
  intro c r₀ s hc hr hs hq J m k S u a b t ha hb hsmall ht y hn hw spin x hcs
  let w := NeutralAtom.packetWidth c r₀ s y
  let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
  have hpw : 0<w := NeutralAtom.packetWidth_pos hc hr hs y
  have hball : 4*w<t-4*b := by dsimp only [w]; linarith [ht.1]
  have HH := H hc hr hs hq S u ha hb hsmall ht y hn hw hball spin x hcs
  obtain ⟨hsp,hamp,hL,_,_⟩ := HF hc hr hs hq y
  have hχm : Measurable χ := (((NeutralAtom.continuous_packetKernel g.continuous hc hr hs).comp
    (continuous_id.prodMk (continuous_const (y := y)))).measurable)
  have hmatch := patchFine_kernel_matching hb (show 0≤F/w^4 by positivity)
    (show 2*w+2*b<t-7*b by dsimp only [w]; linarith [ht.1]) χ hχm hamp y
    (fun z hz => by by_contra hn; have HH := hsp z hn; rw [norm_sub_rev] at HH; linarith)
    hL x
  have habs := abs_le.mp hmatch
  dsimp only at HH ⊢
  refine ⟨?_,?_,HH.2.2⟩ <;> dsimp only [χ,w] at habs ⊢ <;> linarith [HH.1,HH.2.1]

lemma shifted_negative_feedback_mono {θ A : ℝ} (_ : 0≤θ) (hθ1 : θ≤1) :
    Monotone (fun v : ℝ => v+θ*(A+max (-v) 0)) := by
  intro v w hvw
  change v+θ*(A+max (-v) 0)≤w+θ*(A+max (-w) 0)
  by_cases hv : 0≤v
  · have hw : 0≤w := hv.trans hvw
    rw [max_eq_right (by linarith : -v≤0),max_eq_right (by linarith : -w≤0)]
    linarith
  · by_cases hw : 0≤w
    · rw [max_eq_left (by linarith : 0≤-v),max_eq_right (by linarith : -w≤0)]
      nlinarith [mul_le_mul_of_nonneg_right hθ1 (show 0≤-v by linarith)]
    · rw [max_eq_left (by linarith : 0≤-v),max_eq_left (by linarith : 0≤-w)]
      nlinarith [mul_nonneg (show 0≤1-θ by linarith) (show 0≤w-v by linarith)]

theorem tf_response_center_exclusion {v θ A M e I L U : ℝ}
    (hθ : 0≤θ) (hθ1 : θ≤1) (hM : 0≤M) (hU : 0≤U)
    (hlower : tfScalarDensity (v-θ*(A+max (-v) 0))*M-e≤I)
    (hupper : I≤tfScalarDensity (v+θ*(A+max (-v) 0))*M+e) :
    (tfScalarDensity (L+θ*(A+max (-L) 0))*M+e<I → L<v) ∧
    (I<tfScalarDensity (U-θ*A)*M-e → v<U) := by
  constructor
  · intro hI
    by_contra hnot
    have hvL : v≤L := le_of_not_gt hnot
    have HH := mul_le_mul_of_nonneg_right
      (tfScalarDensity_mono (shifted_negative_feedback_mono (A := A) hθ hθ1 hvL)) hM
    linarith
  · intro hI
    by_contra hnot
    have hUv : U≤v := le_of_not_gt hnot
    have hv : 0≤v := hU.trans hUv
    rw [max_eq_right (by linarith : -v≤0),add_zero] at hlower
    have HH := mul_le_mul_of_nonneg_right (tfScalarDensity_mono
      (show U-θ*A≤v-θ*A by linarith)) hM
    linarith

end Coulomb

end

end OAI
