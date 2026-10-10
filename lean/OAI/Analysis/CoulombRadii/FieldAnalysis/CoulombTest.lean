import Mathlib
import OAI.Analysis.CoulombRadii.Packets.CoulombKernel
import OAI.Analysis.CoulombRadii.ThomasFermi.TfExtendNonneg

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ in
lemma tfCoulomb_cauchy (f g : TFLp (volume.restrict Ω)) :
    (tfCoulomb Ω f g)^2 ≤ tfCoulomb Ω f f*tfCoulomb Ω g g := by
  have H (t : ℝ) : 0 ≤ tfCoulomb Ω g g*(t*t)+(2*tfCoulomb Ω f g)*t+tfCoulomb Ω f f := by
    have hh := tfCoulomb_self_nonneg hΩ (f+t • g)
    change 0 ≤ (tfCoulombContinuous hΩ) (f+t • g) (f+t • g) at hh
    simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hh
    change 0 ≤ tfCoulomb Ω f f+t*tfCoulomb Ω g f+t*(tfCoulomb Ω f g+t*tfCoulomb Ω g g) at hh
    rw [tfCoulomb_symm g f] at hh
    nlinarith only [hh]
  have hh := discrim_le_zero H
  dsimp [discrim] at hh
  nlinarith only [hh]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfExtend_toLp {q : Space → ℝ} (hΩ : MeasurableSet Ω)
    (hq : MemLp q TFExponent (volume.restrict Ω)) (hs : ∀ x∉Ω, q x=0) :
    tfExtend Ω (hq.toLp q) =ᵐ[volume] q := by
  filter_upwards [(ae_restrict_iff' hΩ).mp hq.coeFn_toLp] with x hx
  by_cases hy : x∈Ω
  · simpa only [tfExtend,indicator_of_mem hy] using hx hy
  · simp only [tfExtend,indicator_of_notMem hy,hs x hy]

def testCharge (χ : Space → ℝ) : Space → ℝ :=
  fun x => -(NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_continuous {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (testCharge χ) :=
  (NeutralAtom.continuous_coordinateLaplacian (hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top))).neg.div_const _

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_compact {χ : Space → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (testCharge χ) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (by simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn,neg_zero,zero_div])

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_zero {χ : Space → ℝ} {x : Space} (hx : x∉tsupport χ) :
    testCharge χ x=0 := by
  simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,neg_zero,zero_div]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_potential {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (y : Space) :
    (∫ x, coulombKernel (y-x)*testCharge χ x)=χ y := by
  have H := NeutralAtom.integral_translated_coulombKernel_laplacian hχ hc y
  have he : (fun x => coulombKernel (y-x)*testCharge χ x)=
      (fun x => -(NeutralAtom.coulombKernel (x-y)*NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)) := by
    funext x
    simp only [testCharge,coulombKernel,NeutralAtom.coulombKernel,norm_sub_rev]
    ring
  rw [he,integral_div,integral_neg,H]
  field_simp

include hΩ in
lemma tfCoulomb_testCharge {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ⊆Ω) (f : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f (((testCharge_continuous hχ).memLp_of_hasCompactSupport (testCharge_compact hc)).restrict (s := Ω) |>.toLp (testCharge χ))=
      ∫ x, tfExtend Ω f x*χ x := by
  let hm : MemLp (testCharge χ) TFExponent (volume.restrict Ω) :=
    ((testCharge_continuous hχ).memLp_of_hasCompactSupport (testCharge_compact hc)).restrict (s := Ω)
  have he := tfExtend_toLp hΩ hm (fun x hx => testCharge_zero (fun h => hx (hs h)))
  have hep := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp he
  change _ =ᵐ[(volume : Measure Space).prod volume] _ at hep
  unfold tfCoulomb
  rw [Measure.volume_eq_prod]
  have hi := tfCoulomb_integrable hΩ f (hm.toLp (testCharge χ))
  rw [Measure.volume_eq_prod] at hi
  have hpair : (fun p : Space × Space => tfExtend Ω f p.1 * tfExtend Ω (hm.toLp (testCharge χ)) p.2 * coulombKernel (p.1 - p.2)) =ᵐ[(volume : Measure Space).prod volume]
      (fun p => tfExtend Ω f p.1 * testCharge χ p.2 * coulombKernel (p.1 - p.2)) := by
    filter_upwards [hep] with p hp
    change tfExtend Ω (hm.toLp (testCharge χ)) p.2 = testCharge χ p.2 at hp
    rw [hp]
  rw [integral_congr_ae hpair,integral_prod _ (hi.congr hpair)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show (fun y => tfExtend Ω f x*testCharge χ y*coulombKernel (x-y))=
      (fun y => tfExtend Ω f x*(coulombKernel (x-y)*testCharge χ y)) by funext y; ring,
    integral_const_mul,testCharge_potential hχ hc]

include hΩ in

lemma coulomb_smooth_test {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ⊆Ω) (f : TFLp (volume.restrict Ω)) :
    (∫ x, tfExtend Ω f x*χ x)^2 ≤ tfCoulomb Ω f f*(∫ x, testCharge χ x*χ x) := by
  let hm : MemLp (testCharge χ) TFExponent (volume.restrict Ω) :=
    ((testCharge_continuous hχ).memLp_of_hasCompactSupport (testCharge_compact hc)).restrict (s := Ω)
  let g : TFLp (volume.restrict Ω) := hm.toLp (testCharge χ)
  have hg : tfExtend Ω g =ᵐ[volume] testCharge χ :=
    tfExtend_toLp hΩ hm (fun x hx => testCharge_zero (fun h => hx (hs h)))
  have He := tfCoulomb_testCharge hΩ hχ hc hs f
  have Hgg := tfCoulomb_testCharge hΩ hχ hc hs g
  change tfCoulomb Ω g g = _ at Hgg
  have Hg : (∫ x, tfExtend Ω g x*χ x) = ∫ x, testCharge χ x*χ x :=
    integral_congr_ae (hg.mono (fun x hx => congrArg (·*χ x) hx))
  rw [Hg] at Hgg
  have H := tfCoulomb_cauchy hΩ f g
  rwa [He,Hgg] at H

include hΩ in
lemma raw_coulomb_smooth_test {χ σ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆Ω)
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hσs : ∀ x∉Ω, σ x=0) :
    (∫ x, σ x*χ x)^2 ≤ coulombBilinear σ σ*(∫ x, testCharge χ x*χ x) := by
  let f := hσ.toLp σ
  have he : tfExtend Ω f =ᵐ[volume] σ := tfExtend_toLp hΩ hσ hσs
  have H := coulomb_smooth_test hΩ hχ hc hs f
  have Hc : tfCoulomb Ω f f = coulombBilinear σ σ := by
    exact coulombBilinear_congr_ae he he
  rw [Hc] at H
  rwa [integral_congr_ae (he.mono (fun x hx => congrArg (·*χ x) hx))] at H

end Coulomb

end

end
end

end OAI
