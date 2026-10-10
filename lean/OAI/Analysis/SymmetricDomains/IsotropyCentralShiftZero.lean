import Mathlib
import OAI.Analysis.SymmetricDomains.IsotropyCompleteGeneratorsTotally

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology

 theorem bounded_rotated_flow_generator_zero {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (a q : ℝ → A) (d : A) (c : ℝ)
    (ha0 : a 0=1) (hq0 : q 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hda : ∀ t, HasDerivAt a (d*a t) t)
    (hdq : ∀ t, HasDerivAt q ((Complex.I • ((c : ℂ) • (1 : A)-d))*q t) t)
    (hbd : Bornology.IsBounded (Set.range (fun z : ℂ => a z.re*q z.im))) : d=0 := by
  let s : ℝ → ℂ := fun t => Complex.exp (((c*t : ℝ) : ℂ)*Complex.I)
  let b : ℝ → A := fun t => s t • q (-t)
  have hs0 : s 0=1 := by simp [s]
  have hsn (t : ℝ) : ‖s t‖=1 := Complex.norm_exp_ofReal_mul_I (c*t)
  have hsd (t : ℝ) : HasDerivAt s (((c : ℂ)*Complex.I)*s t) t := by
    have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
    convert ((h.const_mul (c : ℂ)).mul_const Complex.I).cexp using 1 <;>
      simp [s,Complex.ofReal_mul,mul_comm]
  have hdb (t : ℝ) : HasDerivAt b ((Complex.I • d)*b t) t := by
    have hq := (hdq (-t)).scomp t (hasDerivAt_neg t)
    have hb := (hsd t).smul hq
    change HasDerivAt b _ t at hb
    have he : s t • (- (Complex.I • ((c : ℂ) • (1 : A)-d)*q (-t))) +
        ((c : ℂ)*Complex.I*s t) • q (-t) = (Complex.I • d)*b t := by
      simp only [b, smul_mul_assoc, mul_smul_comm, one_mul, smul_sub, smul_smul,
        smul_neg, sub_mul]
      module
    rw [neg_one_smul] at hb
    exact he ▸ hb
  apply bounded_complex_flow_generator_zero a b d ha0 (by simp [b,hs0,hq0]) ham hda hdb
  obtain ⟨C,hC⟩ := (isBounded_iff_forall_norm_le.mp hbd)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,?_⟩
  rintro x ⟨z,rfl⟩
  change ‖a z.re*b z.im‖ ≤ C
  rw [show a z.re*b z.im=s z.im • (a z.re*q (-z.im)) by simp [b],norm_smul,hsn,one_mul]
  exact hC _ ⟨star z,by simp⟩

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem isotropy_central_shift_zero {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : U) (c : ℝ)
    (hXp : X p.val=0) (hYp : Y p.val=0)
    (hrel : fderiv ℂ Y p.val=Complex.I • ((c : ℂ) • (1 : Affine n →L[ℂ] Affine n)-fderiv ℂ X p.val)) : X=0 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  obtain ⟨q,hq,hq0,hqm,rfl⟩ := hY
  have hfixA := oneParameter_fixed_of_generator_zero hU a ha hbd ha0 ham p hXp
  have hfixQ := oneParameter_fixed_of_generator_zero hU q hq hbd hq0 hqm p hYp
  let A : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (a t).derivativeAt p
  let Q : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (q t).derivativeAt p
  have hA0 : A 0=1 := by dsimp only [A]; rw [ha0,derivativeAt_one hU]
  have hQ0 : Q 0=1 := by dsimp only [Q]; rw [hq0,derivativeAt_one hU]
  have hAm (s t : ℝ) : A (s+t)=A s*A t := by
    dsimp only [A]
    rw [ham,derivativeAt_mul hU,hfixA]
    rfl
  have hAd (t : ℝ) : HasDerivAt A ((fderiv ℂ (infinitesimalGenerator a) p.val)*A t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham t p
    rw [hfixA] at hd
    exact hd
  have hQd (t : ℝ) : HasDerivAt Q
      ((Complex.I • ((c : ℂ) • (1 : Affine n →L[ℂ] Affine n)-fderiv ℂ (infinitesimalGenerator a) p.val))*Q t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd q hq hq0 hqm t p
    rw [hfixQ,hrel] at hd
    exact hd
  have hbounded : Bornology.IsBounded (Set.range (fun z : ℂ => A z.re*Q z.im)) := by
    apply ((compact_faithful_isotropy hU hc.isPreconnected hbd Γ hhol p).1.isBounded).subset
    rintro _ ⟨z,rfl⟩
    refine ⟨a z.re*q z.im,?_,?_⟩
    · change (a z.re).toHomeomorph ((q z.im).toHomeomorph p)=p
      rw [hfixQ,hfixA]
    · change (a z.re*q z.im).derivativeAt p=A z.re*Q z.im
      rw [derivativeAt_mul hU,hfixQ]
      rfl
  have hz := bounded_rotated_flow_generator_zero A Q
    (fderiv ℂ (infinitesimalGenerator a) p.val) c hA0 hQ0 hAm hAd hQd hbounded
  exact IsCompleteGenerator.eq_zero_of_zero_jet hU hc hbd ⟨a,ha,ha0,ham,rfl⟩ p hXp hz

end Biholomorph
end Release061

end

end OAI
