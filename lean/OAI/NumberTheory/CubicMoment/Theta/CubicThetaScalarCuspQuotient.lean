import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarCuspCutoff
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTranslatedCuspStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoffBounds

namespace OAI

/-! Scaled scalar cusp cutoffs descend to the actual quotient in
every arithmetic cusp, using normality of the principal group. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaScalarCusp_norm {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖cubicThetaScalarCusp N p‖≤1 := by
  by_cases h : ∃ r, cubicThetaScalarCuspTerm N r p≠0
  · obtain ⟨r,hr⟩ := h
    have he : cubicThetaScalarCusp N p=cubicThetaScalarCuspTerm N r p := by
      apply tsum_eq_single
      intro t ht
      by_contra htn
      exact ht (cubicThetaIncomingRows_unique hp (cubicThetaScalarCuspTerm_high hN htn)
        (cubicThetaScalarCuspTerm_high hN hr))
    rw [he]
    exact cubicThetaCuspCutoff_norm _
  · have hz : ∀ r, cubicThetaScalarCuspTerm N r p=0 := by simpa only [not_exists,not_not] using h
    simp only [cubicThetaScalarCusp,hz,tsum_zero,norm_zero,zero_le_one]

def cubicThetaScalarCuspAt (δ : SL(2,Eisenstein)) (N : ℝ) (p : CubicThetaPoint) : ℂ :=
  cubicThetaScalarCusp N (δ⁻¹ • p).val

lemma cubicThetaScalarCuspAt_invariant (δ : SL(2,Eisenstein)) (N : ℝ)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaScalarCuspAt δ N (g • p)=cubicThetaScalarCuspAt δ N p := by
  have he : δ⁻¹ • (g • p)=cubicThetaPrincipalConjugate δ g • (δ⁻¹ • p) := by
    change δ⁻¹ • (g.val • p)=(δ⁻¹*g.val*δ) • (δ⁻¹ • p)
    simp only [mul_smul,smul_inv_smul]
  unfold cubicThetaScalarCuspAt
  rw [he]
  exact cubicThetaScalarCusp_invariant N (cubicThetaPrincipalConjugate δ g) (δ⁻¹ • p).property

def cubicThetaScalarCuspQuotient (δ : SL(2,Eisenstein)) (N : ℝ) (q : CubicThetaQuotient) : ℂ :=
  cubicThetaScalarCuspAt δ N (cubicThetaQuotientLift q)

lemma cubicThetaScalarCuspQuotient_apply (δ : SL(2,Eisenstein)) (N : ℝ) (p : CubicThetaPoint) :
    cubicThetaScalarCuspQuotient δ N (cubicThetaQuotientMap p)=cubicThetaScalarCuspAt δ N p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaScalarCuspQuotient
  rw [← hg,cubicThetaScalarCuspAt_invariant]

lemma cubicThetaScalarCuspQuotient_continuous (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N) :
    Continuous (cubicThetaScalarCuspQuotient δ N) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaScalarCuspQuotient δ N ∘ cubicThetaQuotientMap=cubicThetaScalarCuspAt δ N :=
    funext (cubicThetaScalarCuspQuotient_apply δ N)
  rw [he]
  have hc : Continuous (fun p : CubicThetaPoint => cubicThetaScalarCusp N p.val) :=
    (cubicThetaScalarCusp_smooth hN).continuousOn.comp_continuous continuous_subtype_val
      (fun p => p.property)
  exact hc.comp (continuous_const_smul δ⁻¹)

lemma cubicThetaScalarCuspQuotient_norm (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N)
    (q : CubicThetaQuotient) : ‖cubicThetaScalarCuspQuotient δ N q‖≤1 :=
  cubicThetaScalarCusp_norm hN (δ⁻¹ • cubicThetaQuotientLift q).property

end CubicFirstMoment

end

end OAI
