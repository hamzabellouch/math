import Mathlib
import OAI.Analysis.Commutator.MatrixGNS
import OAI.Analysis.Commutator.MatrixUnitaryAlphabet

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (p : Matrix I I ℂ) (hp : IsStarProjection p)
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  (e : G ≃ projectionIndices p hp)

def stageAlphabet (g : G) : A := φ (projectionAlphabet p hp e g)

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_star_mul (g : G) : star (stageAlphabet φ p hp e g)*stageAlphabet φ p hp e g=φ p := by
  rw [stageAlphabet,←map_star,←map_mul,projectionAlphabet_star_mul]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_support (g : G) : stageAlphabet φ p hp e g*φ p=stageAlphabet φ p hp e g := by
  rw [stageAlphabet,←map_mul,projectionAlphabet_support]

include hτ h1 in
omit [StarOrderedRing A] in
lemma stageAlphabet_centered (g : G) (hg : g≠0) : τ (stageAlphabet φ p hp e g)=0 := by
  rw [stageAlphabet,TracialGNS.stage_trace τ hτ h1 φ,projectionAlphabet_trace,ite_eq_right hg,mul_zero]

include hτ h1 in
omit [StarOrderedRing A] in
lemma stageAlphabet_gram (g h : G) : τ (star (stageAlphabet φ p hp e g)*stageAlphabet φ p hp e h)=
    if g=h then τ (φ p) else 0 := by
  by_cases heq : g=h
  · subst h
    rw [stageAlphabet_star_mul,ite_eq_left rfl]
  · rw [ite_eq_right heq,stageAlphabet,stageAlphabet,←map_star,←map_mul,
      TracialGNS.stage_trace τ hτ h1 φ,projectionAlphabet_gram,ite_eq_right heq,mul_zero]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_norm_le (g : G) : ‖stageAlphabet φ p hp e g‖≤1 := by
  have h := CStarRing.norm_star_mul_self (x := stageAlphabet φ p hp e g)
  rw [stageAlphabet_star_mul] at h
  have hp1 := (hp.map φ).norm_le (φ p)
  nlinarith [norm_nonneg (stageAlphabet φ p hp e g)]

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

def normalizedStageAlphabet (g : G) : A := (((Real.sqrt α)⁻¹:ℝ):ℂ) • stageAlphabet φ p hp e g

include hα in
lemma normalization_sq : ((((Real.sqrt α)⁻¹:ℝ):ℂ))^2=(α:ℂ)⁻¹ := by
  rw [←Complex.ofReal_pow,inv_pow,Real.sq_sqrt hα.le,Complex.ofReal_inv]

include hτ h1 hα hατ in
lemma normalizedStageAlphabet_orthonormal :
    Orthonormal ℂ (fun g : G => TracialGNS.algebraVector τ (normalizedStageAlphabet φ p hp e α g)) := by
  apply orthonormal_iff_ite.mpr
  intro g h
  simp only [normalizedStageAlphabet,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,TracialGNS.inner_algebraVector,stageAlphabet_gram τ hτ h1]
  by_cases heq : g=h
  · rw [ite_eq_left heq,ite_eq_left heq,hατ]
    rw [←mul_assoc,←sq,normalization_sq α hα,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hα.ne')]
  · rw [ite_eq_right heq,ite_eq_right heq,mul_zero,mul_zero]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma normalizedStageAlphabet_norm_le (g : G) : ‖normalizedStageAlphabet φ p hp e α g‖≤(Real.sqrt α)⁻¹ := by
  rw [normalizedStageAlphabet,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg α))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (stageAlphabet_norm_le φ p hp e g)
    (inv_nonneg.mpr (Real.sqrt_nonneg α))

include hα in
omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma normalizedStageAlphabet_star_mul (g : G) :
    star (normalizedStageAlphabet φ p hp e α g)*normalizedStageAlphabet φ p hp e α g=
      ((α:ℂ)⁻¹) • φ p := by
  rw [normalizedStageAlphabet,star_smul,smul_mul_smul_comm,Complex.star_def,Complex.conj_ofReal,
    stageAlphabet_star_mul,←sq,normalization_sq α hα]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma normalizedStageAlphabet_support (g : G) :
    normalizedStageAlphabet φ p hp e α g*φ p=normalizedStageAlphabet φ p hp e α g := by
  rw [normalizedStageAlphabet,smul_mul_assoc,stageAlphabet_support]

include hτ h1 in
omit [StarOrderedRing A] in
lemma normalizedStageAlphabet_centered (g : G) (hg : g≠0) :
    τ (normalizedStageAlphabet φ p hp e α g)=0 := by
  rw [normalizedStageAlphabet,map_smul,stageAlphabet_centered τ hτ h1 φ p hp e g hg,smul_zero]

include hτ h1 hατ in
omit [StarOrderedRing A] in
lemma projection_rank : (Fintype.card (projectionIndices p hp):ℝ)=α*Fintype.card I := by
  have hd : (Fintype.card I:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (projectionIndices p hp):ℂ)=(α:ℂ)*Fintype.card I := by
    rw [←hατ,TracialGNS.stage_trace τ hτ h1 φ,projection_trace p hp]
    field_simp
  have hr := congrArg Complex.re hc
  simpa using hr

include hτ h1 hα hατ hp in
theorem exists_normalized_corner_alphabet (N : ℕ)
    (hN : (N+1:ℝ)≤α*Fintype.card I) :
    ∃ m : ℕ, N ≤ m ∧ ∃ x : Fin m → A,
      Orthonormal ℂ (fun i => TracialGNS.algebraVector τ (x i)) ∧
      ∀ i, τ (x i)=0 ∧ x i*φ p=x i ∧ star (x i)*x i=((α:ℂ)⁻¹) • φ p ∧
        ‖x i‖≤(Real.sqrt α)⁻¹ := by
  let r := Fintype.card (projectionIndices p hp)
  have hrN : N+1≤r := by
    have h := hN.trans_eq (projection_rank τ hτ h1 φ p hp α hατ).symm
    exact_mod_cast h
  have hr : 0<r := by omega
  let : NeZero r := ⟨hr.ne'⟩
  let e : ZMod r ≃ projectionIndices p hp := Fintype.equivOfCardEq (by rw [ZMod.card])
  let J := {g : ZMod r // g≠0}
  let m := Fintype.card J
  have hm : m=r-1 := by
    dsimp only [m,J]
    rw [Fintype.card_subtype_compl (fun g : ZMod r => g=0),Fintype.card_subtype_eq,ZMod.card]
  let b : Fin m ≃ J := (Fintype.equivFin J).symm
  let x : Fin m → A := fun i => normalizedStageAlphabet φ p hp e α (b i).val
  refine ⟨m,by omega,x,?_,?_⟩
  · exact (normalizedStageAlphabet_orthonormal τ hτ h1 φ p hp e α hα hατ).comp
      (fun i => (b i).val) (Subtype.val_injective.comp b.injective)
  · intro i
    exact ⟨normalizedStageAlphabet_centered τ hτ h1 φ p hp e α _ (b i).property,
      normalizedStageAlphabet_support φ p hp e α _,
      normalizedStageAlphabet_star_mul φ p hp e α hα _,
      normalizedStageAlphabet_norm_le φ p hp e α _⟩

end Kadison.MatrixCorners

end

end
end

end OAI
