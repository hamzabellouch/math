import Mathlib
import OAI.Analysis.WeakInfiniteness.CompatibleInverse
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools2
import OAI.Analysis.WeakInfiniteness.UniversePerturbation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped CStarAlgebra

section

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def UniformPerturbationOne_any (σ : ℝ) : Prop :=
  ∀ p q h k c : A, ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → 0 ≤ h → 0 ≤ k → 0 ≤ c →
    star p*p*h=h → q*star q*k=k →
    CuntzSubequiv (diagonalCopies 1 c) (diagonalCopies 1 h) →
    CuntzSubequiv (diagonalCopies 1 c) (diagonalCopies 1 k) →
    ∀ (T : A) (η α : ℝ), 0 < η → 0 < α →
      ∃ y : A, ‖y‖ ≤ 1 ∧
        ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
          α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖

lemma exists_uniformPerturbationOne_any (hA : Exact A)
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a)) :
    ∃ σ : ℝ,0 < σ ∧ σ < 1 ∧ UniformPerturbationOne_any A σ := by
  obtain ⟨σ,hσ,hσ1,h⟩ := exists_uniform_perturbation_constant_any
  exact ⟨σ,hσ,hσ1,h A hA 1 (by norm_num) (fun a ha _ => hpi a ha)⟩

end

section Algebra

variable {B : Type*} [CStarAlgebra B]

lemma metric_column_expansion_any (F C g e p y Z : B) (η : ℝ)
    (hFCg : F*C*g=p) (hge : g*e=e) (hZ : Z=1+(η : ℂ) • (g*y*g)) :
    F*C*Z*e=F*C*e+(η : ℂ) • (p*y*e) := by
  rw [hZ,mul_add,add_mul,mul_one,mul_smul_comm,smul_mul_assoc]
  congr 2
  calc
    F*C*(g*y*g)*e = (F*C*g)*y*(g*e) := by simp only [mul_assoc]
    _ = p*y*e := by rw [hFCg,hge]

lemma metric_column_update_any (F C g e p y Z W : B) (η : ℝ)
    (hFCg : F*C*g=p) (hge : g*e=e) (hZ : Z=W+(η : ℂ) • (g*y*g)) :
    F*C*Z*e=F*C*W*e+(η : ℂ) • (p*y*e) := by
  rw [hZ,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  congr 2
  calc
    F*C*(g*y*g)*e = (F*C*g)*y*(g*e) := by simp only [mul_assoc]
    _ = p*y*e := by rw [hFCg,hge]

end Algebra

section Unitization

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_snd_mul_inr_any (u : Unitization ℂ A) (a : A) :
    ((u*(a : Unitization ℂ A)).snd : Unitization ℂ A)=u*(a : Unitization ℂ A) := by
  apply unitization_inr_snd_of_fst_eq_zero
  simp only [Unitization.fst_mul,Unitization.fst_inr,mul_zero]

lemma exists_compatible_metric_perturbations_any
    {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hτ : 0 < τ)
    (hpert : UniformPerturbationOne_any A σ)
    (g F₁ F₂ C₁ C₂ : Unitization ℂ A) (hg : ‖g‖ ≤ 1) (hgsa : IsSelfAdjoint g)
    (p₁ p₂ e f h₁ h₂ k₁ k₂ d₁ d₂ : A)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hph₁ : star p₁*p₁*h₁=h₁) (hph₂ : star p₂*p₂*h₂=h₂)
    (hek₁ : e*star e*k₁=k₁) (hfk₂ : f*star f*k₂=k₂)
    (hdh₁ : CuntzSubequiv (diagonalCopies 1 d₁) (diagonalCopies 1 h₁))
    (hdh₂ : CuntzSubequiv (diagonalCopies 1 d₂) (diagonalCopies 1 h₂))
    (hdk₁ : CuntzSubequiv (diagonalCopies 1 d₁) (diagonalCopies 1 k₁))
    (hdk₂ : CuntzSubequiv (diagonalCopies 1 d₂) (diagonalCopies 1 k₂))
    (hge : g*(e : Unitization ℂ A)=(e : Unitization ℂ A))
    (hgf : g*(f : Unitization ℂ A)=(f : Unitization ℂ A))
    (hFC₁ : F₁*C₁*g=(p₁ : Unitization ℂ A))
    (hFC₂ : F₂*C₂*g=(p₂ : Unitization ℂ A)) :
    ∃ Z W z w : Unitization ℂ A,
      Z=1+g*z*g ∧ W=1+g*w*g ∧ star Z*W=1 ∧
      ‖Z‖ ≤ 2 ∧ ‖W‖ ≤ 2 ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        τ ≤ ‖π d₁‖ → σ/16 ≤ ‖(Unitization.starLift π) (F₁*C₁*Z*(e : Unitization ℂ A))‖) ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        τ ≤ ‖π d₂‖ → σ^2/128 ≤ ‖(Unitization.starLift π) (F₂*C₂*W*(f : Unitization ℂ A))‖) := by
  let B := Unitization ℂ A
  let η : ℝ := 1/8
  let η' : ℝ := σ/128
  have hη : 0 < η := by norm_num [η]
  have hη' : 0 < η' := by dsimp [η']; positivity
  let T₁ : A := (F₁*C₁*(e : B)).snd
  have hT₁ : (T₁ : B)=F₁*C₁*(e : B) := inr_snd_mul_inr_any _ _
  obtain ⟨y,hy,hytest⟩ := hpert p₁ e h₁ k₁ d₁ hp₁ he hh₁ hk₁ hd₁ hph₁ hek₁ hdh₁ hdk₁ T₁ η τ hη hτ
  let a₁ : B := (η : ℂ) • (y : B)
  have ha₁ : ‖a₁‖ ≤ 1/8 := by
    dsimp only [a₁,η]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/8),Unitization.norm_inr]
    nlinarith
  let Z₁ : B := 1+g*a₁*g
  have hZ₁ : ‖Z₁‖ ≤ 9/8 := (norm_factored_perturbation_le g a₁ hg).trans (by linarith)
  obtain ⟨w₁,hw₁,hleft₁,hright₁⟩ := exists_factored_inverse g (star a₁) hg
    (by simpa only [norm_star] using ha₁) (by norm_num : (1/8 : ℝ) < 1)
  have hw₁' : ‖w₁‖ ≤ 1/7 := by norm_num at hw₁; exact hw₁
  let W₁ : B := 1+g*w₁*g
  have hstarZ₁ : star Z₁=1+g*star a₁*g := by
    dsimp only [Z₁]
    rw [star_add,star_one,star_mul,star_mul,hgsa.star_eq]
    simp only [mul_assoc]
  have hW₁Z₁ : star W₁*Z₁=1 := by
    have h := congrArg star hleft₁
    simpa only [← hstarZ₁,star_mul,star_star,star_one] using h
  have hfirst (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (hπ : τ ≤ ‖π d₁‖) :
      σ/8 ≤ ‖(Unitization.starLift π) (F₁*C₁*Z₁*(e : B))‖ := by
    have hz : Z₁=1+(η : ℂ) • (g*(y : B)*g) := by simp only [Z₁,a₁,mul_smul_comm,smul_mul_assoc]
    rw [metric_column_expansion_any F₁ C₁ g (e : B) (p₁ : B) (y : B) Z₁ η hFC₁ hge hz,← hT₁]
    rw [← Unitization.inr_mul,← Unitization.inr_mul,← Unitization.inr_smul,← Unitization.inr_add,
      starLift_inr_apply_general]
    simpa only [η,div_eq_mul_inv,one_mul] using hytest H π hπ
  let T₂ : A := (F₂*C₂*W₁*(f : B)).snd
  have hT₂ : (T₂ : B)=F₂*C₂*W₁*(f : B) := inr_snd_mul_inr_any _ _
  obtain ⟨y',hy',hytest'⟩ := hpert p₂ f h₂ k₂ d₂ hp₂ hf hh₂ hk₂ hd₂ hph₂ hfk₂ hdh₂ hdk₂ T₂ η' τ hη' hτ
  let w : B := w₁+(η' : ℂ) • (y' : B)
  have hw : ‖w‖ ≤ 1/4 := by
    have hn : ‖(η' : ℂ) • (y' : B)‖ ≤ η' := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη',Unitization.norm_inr]
      nlinarith
    have hsum := norm_add_le w₁ ((η' : ℂ) • (y' : B))
    dsimp only [η'] at hn
    dsimp only [w]
    linarith
  obtain ⟨z,hz,hleft,hright⟩ := exists_factored_inverse g (star w) hg
    (by simpa only [norm_star] using hw) (by norm_num : (1/4 : ℝ) < 1)
  have hz' : ‖z‖ ≤ 1/3 := by norm_num at hz; exact hz
  let Z : B := 1+g*z*g
  let W : B := 1+g*w*g
  have hstarW : star W=1+g*star w*g := by
    dsimp only [W]
    rw [star_add,star_one,star_mul,star_mul,hgsa.star_eq]
    simp only [mul_assoc]
  have hZW : Z*star W=1 := by simpa only [hstarW] using hright
  have hstarZW : star Z*W=1 := by
    have h := congrArg star hleft
    simpa only [← hstarW,star_mul,star_star,star_one] using h
  have hW : W=W₁+(η' : ℂ) • (g*(y' : B)*g) := by
    simp only [W,W₁,w,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,add_assoc]
  have hdiff : ‖F₁*C₁*(Z-Z₁)*(e : B)‖ ≤ 3/2*η' :=
    normalized_inverse_difference_bound g z Z Z₁ W W₁ (p₁ : B) F₁ C₁ (e : B) (y' : B)
      hη'.le hg hz' hZ₁ (by simpa only [Unitization.norm_inr] using hp₁)
      (by simpa only [Unitization.norm_inr] using he) (by simpa only [Unitization.norm_inr] using hy')
      hgsa rfl hFC₁ hZW hW₁Z₁ hW
  refine ⟨Z,W,z,w,rfl,rfl,hstarZW,?_,?_,?_,?_⟩
  · exact (norm_factored_perturbation_le g z hg).trans (by linarith)
  · exact (norm_factored_perturbation_le g w hg).trans (by linarith)
  · intro H π hπ
    have ht := hfirst H π hπ
    have hnorm := norm_sub_norm_le ((Unitization.starLift π) (F₁*C₁*Z₁*(e : B)))
      ((Unitization.starLift π) (F₁*C₁*Z*(e : B)))
    have hc : ‖(Unitization.starLift π) (F₁*C₁*Z₁*(e : B))-
        (Unitization.starLift π) (F₁*C₁*Z*(e : B))‖ ≤ 3/2*η' := by
      rw [← map_sub]
      have halg : F₁*C₁*Z₁*(e : B)-F₁*C₁*Z*(e : B)= -(F₁*C₁*(Z-Z₁)*(e : B)) := by noncomm_ring
      rw [halg,map_neg,norm_neg]
      exact (NonUnitalStarAlgHom.norm_apply_le (Unitization.starLift π).toNonUnitalStarAlgHom _).trans hdiff
    dsimp only [η'] at hc
    linarith
  · intro H π hπ
    rw [metric_column_update_any F₂ C₂ g (f : B) (p₂ : B) (y' : B) W W₁ η' hFC₂ hgf hW,← hT₂]
    rw [← Unitization.inr_mul,← Unitization.inr_mul,← Unitization.inr_smul,← Unitization.inr_add,
      starLift_inr_apply_general]
    have ht := hytest' H π hπ
    dsimp only [η'] at ht
    nlinarith

end Unitization

end

end WeakPureInfiniteness
end

end OAI
