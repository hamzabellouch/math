import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralEuclideanBridge

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralWholeL2_pairing (f : CentralL2) (ψ : R3 → ℝ) :
    (∫ x,centralWholeL2 f x*ψ x)=
      ∫ x,f x*ψ (centralEuclideanCLE.symm x) ∂centralMeasure := by
  calc
    (∫ x,centralWholeL2 f x*ψ x)=∫ x,centralZeroExtension f x*ψ x := by
      apply integral_congr_ae
      filter_upwards [centralWholeL2_ae f] with x hx
      rw [hx]
    _ = ∫ x,centralClosed.indicator f (centralEuclideanCLE x)*ψ (centralEuclideanCLE.symm (centralEuclideanCLE x)) := by
      simp only [centralZeroExtension,centralEuclideanCLE.symm_apply_apply]
    _ = ∫ x,centralClosed.indicator f x*ψ (centralEuclideanCLE.symm x) :=
      centralEuclidean_integral (fun x => centralClosed.indicator f x*ψ (centralEuclideanCLE.symm x))
    _ = ∫ x,f x*ψ (centralEuclideanCLE.symm x) ∂centralMeasure := by
      change _=∫ x in centralClosed,f x*ψ (centralEuclideanCLE.symm x)
      rw [←integral_indicator centralClosed_compact.measurableSet]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈centralClosed <;> simp [hx]

theorem central_euclidean_weak_partial (s : Fin 3 → ℝ) (p : centralEnergySpace s)
    (ψ : R3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆centralEuclideanCLE ⁻¹' centralClosed)
    (i : Fin 3) :
    (∫ x,centralWholeL2 (centralAmbientComponent s i.succ p.val) x*ψ x)=
      -(∫ x,centralWholeL2 (centralAmbientComponent s 0 p.val) x*
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  let φ : centralSmoothFunctions := ⟨fun x => ψ (centralEuclideanCLE.symm x),
    hψ.comp centralEuclideanCLE.symm.contDiff⟩
  have hφc : HasCompactSupport φ := hc.comp_homeomorph centralEuclideanCLE.symm.toHomeomorph
  have hφs : tsupport φ⊆centralClosed := by
    intro x hx
    have hpre := tsupport_comp_subset_preimage ψ centralEuclideanCLE.symm.continuous hx
    have hmem := hs hpre
    simpa only [mem_preimage,centralEuclideanCLE.apply_symm_apply] using hmem
  have he := central_distributional_derivative s p φ hφc hφs i
  rw [L2.inner_def,L2.inner_def] at he
  have hleft : (∫ x,inner ℝ (centralSmoothJet φ 0 x) (centralAmbientComponent s i.succ p.val x) ∂centralMeasure)=
      ∫ x,centralAmbientComponent s i.succ p.val x*ψ (centralEuclideanCLE.symm x) ∂centralMeasure := by
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae φ 0] with x hx
    rw [hx]
    rfl
  have hright : (∫ x,inner ℝ (centralSmoothJet φ i.succ x) (centralAmbientComponent s 0 p.val x) ∂centralMeasure)=
      ∫ x,centralAmbientComponent s 0 p.val x*
        fderiv ℝ ψ (centralEuclideanCLE.symm x) (EuclideanSpace.basisFun (Fin 3) ℝ i) ∂centralMeasure := by
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae φ i.succ] with x hx
    rw [hx,centralJetField_succ,Real.inner_apply]
    rw [centralEuclidean_partial (hψ.differentiable (by simp))]
    exact mul_comm _ _
  rw [hleft,hright] at he
  simpa only [centralWholeL2_pairing] using he

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma weak_partial_of_smooth_representative (f F : WholeL2) {U : Set R3}
    (hU : IsOpen U) (v : R3) (g : R3 → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (heq : (f : R3 → ℝ)=ᵐ[volume.restrict U] g)
    (hweak : ∀ ψ : R3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ⊆U → (∫ x,F x*ψ x)=-(∫ x,f x*fderiv ℝ ψ x v)) :
    ∀ᵐ x∂volume,x∈U → F x=fderiv ℝ g x v := by
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hloc := ((Lp.memLp F).locallyIntegrable (by norm_num : (1:ℝ≥0∞)≤2)).sub hdg.locallyIntegrable
  have heq' := (ae_restrict_iff' hU.measurableSet).mp heq
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn U) (by
    intro ψ hψ hc hsp
    have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψF : Integrable (fun x => ψ x*F x) :=
      (hψ.continuous.memLp_of_hasCompactSupport (p := 2) hc).integrable_mul (Lp.memLp F)
    have hψg : Integrable (fun x => ψ x*fderiv ℝ g x v) :=
      (hψ.continuous.mul hdg).integrable_of_hasCompactSupport hc.mul_right
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := ψ) (g := g) (v := v)
      ((hdψ.mul hg.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
      hψg ((hψ.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => hψ.differentiable (by simp) x)
      (fun x _ => hg.differentiable (by simp) x)
    have hreplace : (∫ x,f x*fderiv ℝ ψ x v)=(∫ x,g x*fderiv ℝ ψ x v) := by
      apply integral_congr_ae
      filter_upwards [heq'] with x hx
      by_cases hxu : x∈U
      · rw [hx hxu]
      · have hzero := fderiv_of_notMem_tsupport ℝ (fun hh => hxu (hsp hh))
        rw [hzero]
        simp
    have hw := hweak ψ hψ hc hsp
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub]
    rw [integral_sub hψF hψg]
    have hswap : (∫ x,ψ x*F x)=∫ x,F x*ψ x := by simp only [mul_comm]
    rw [hswap,hw,hreplace,he]
    simp only [mul_comm,sub_self])
  filter_upwards [hz] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

theorem central_smooth_representative_jets (s : Fin 3 → ℝ) (p : centralEnergySpace s)
    {U : Set R3} (hU : IsOpen U) (hs : U⊆centralEuclideanCLE ⁻¹' centralClosed)
    (g : R3 → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (heq : (centralWholeL2 (centralAmbientComponent s 0 p.val) : R3 → ℝ)=ᵐ[volume.restrict U] g) :
    ∀ i : Fin 3,∀ᵐ x∂volume,x∈U →
      centralWholeL2 (centralAmbientComponent s i.succ p.val) x=
        fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  intro i
  exact weak_partial_of_smooth_representative _ _ hU _ g hg heq
    (fun ψ hψ hc hsp => central_euclidean_weak_partial s p ψ hψ hc (hsp.trans hs) i)

end ScalarConductivity

end
end

end OAI
