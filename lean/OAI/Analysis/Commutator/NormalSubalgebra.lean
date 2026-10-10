import Mathlib
import OAI.Analysis.Commutator.NormalGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology InnerProductSpace

namespace Kadison.NormalSubalgebra

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N≤M)

def inclusion : N →⋆ₐ[ℂ] M := StarSubalgebra.inclusion hNM

@[simp] lemma inclusion_apply (a : N) : (inclusion M N hNM a:H →L[ℂ] H)=(a:H →L[ℂ] H) := rfl

variable (τ : M →ₚ[ℂ] ℂ)

def trace : N →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (inclusion M N hNM).toLinearMap
  monotone' := fun _ _ h => τ.monotone h

@[simp] lemma trace_apply (a : N) : trace M N hNM τ a=τ (inclusion M N hNM a) := rfl

lemma normal (hτ : NormalGNS.BoundedWOTContinuous M τ) :
    NormalGNS.BoundedWOTContinuous N (trace M N hNM τ) := by
  intro C
  let f : {T : H →WOT[ℂ] H // T.toCLM∈N ∧ ‖T.toCLM‖≤C} →
      {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    fun a => ⟨a.val,hNM a.property.1,a.property.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact (hτ C).comp hf

lemma tracial (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (a b : N) :
    trace M N hNM τ (a*b)=trace M N hNM τ (b*a) := by
  simpa only [trace_apply,map_mul] using hτ (inclusion M N hNM a) (inclusion M N hNM b)

lemma one (hone : τ 1=1) : trace M N hNM τ 1=1 := by rw [trace_apply,map_one,hone]

lemma faithful (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (a : N)
    (ha : trace M N hNM τ (star a*a)=0) : a=0 := by
  have he := hfaith (inclusion M N hNM a) (by simpa only [trace_apply,map_mul,map_star] using ha)
  apply Subtype.ext
  exact congrArg (fun x : M => (x : H →L[ℂ] H)) he

lemma vector_norm (a : N) :
    ‖algebraVector (trace M N hNM τ) a‖=‖algebraVector τ (inclusion M N hNM a)‖ := by
  have hi : inner ℂ (algebraVector (trace M N hNM τ) a) (algebraVector (trace M N hNM τ) a)=
      inner ℂ (algebraVector τ (inclusion M N hNM a)) (algebraVector τ (inclusion M N hNM a)) := by
    exact (inner_algebraVector (trace M N hNM τ) a a).trans
      (inner_algebraVector τ (inclusion M N hNM a) (inclusion M N hNM a)).symm
  have hr := congrArg (RCLike.re : ℂ → ℝ) hi
  have hs := (norm_sq_eq_re_inner (𝕜:=ℂ) (algebraVector (trace M N hNM τ) a)).trans
    (hr.trans (norm_sq_eq_re_inner (𝕜:=ℂ) (algebraVector τ (inclusion M N hNM a))).symm)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end Kadison.NormalSubalgebra

end

end
end

end OAI
