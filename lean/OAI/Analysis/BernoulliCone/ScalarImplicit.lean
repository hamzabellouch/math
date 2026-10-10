import OAI.Analysis.BernoulliCone.UpperParameter

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma real_linear_invertible {L:ℝ→L[ℝ] ℝ} (hL:L 1≠0) :L.IsInvertible := by
  have he:∀s:ℝ,L s=s*L 1:=fun s=>by simpa using L.map_smul s (1:ℝ)
  let R:ℝ→L[ℝ] ℝ:=(L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g:=R)
  · apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.comp_apply,R,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.comp_apply,R,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [he]
    field_simp
    rw [he]
    ring
lemma scalar_implicit {F:E×ℝ→ℝ} {x:E} {l ρ:ℝ}
    (hF:ContDiffAt ℝ ∞ F (x,l)) (hd:HasDerivAt (fun s:ℝ=>F (x,s)) ρ l) (hρ:ρ≠0) :
    ∃ψ:E→ℝ, ContDiffAt ℝ ∞ ψ x ∧ ψ x=l ∧
      ∀ᶠ y in 𝓝 x,F (y,ψ y)=F (x,l) := by
  have hc:HasDerivAt (fun s:ℝ=>F (x,s)) ((fderiv ℝ F (x,l)) (0,1)) l := by
    exact (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_const l x).prodMk (hasDerivAt_id l))
  have hl:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1=ρ := by
    simpa using hc.unique hd
  have hi:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible:=
    real_linear_invertible (by rw [hl]; exact hρ)
  exact ⟨hF.implicitFunction (by simp) hi,hF.contDiffAt_implicitFunction (by simp) hi,
    hF.implicitFunction_apply_self (by simp) hi,hF.eventually_apply_implicitFunction (by simp) hi⟩
/-- The local uniqueness clause of the scalar implicit-function theorem is
needed for a smooth extension up to one side of a genuine seam. -/
lemma scalar_implicit_unique {F:E×ℝ→ℝ} {x:E} {l ρ:ℝ}
    (hF:ContDiffAt ℝ ∞ F (x,l)) (hd:HasDerivAt (fun s:ℝ=>F (x,s)) ρ l) (hρ:ρ≠0) :
    ∃ψ:E→ℝ, ContDiffAt ℝ ∞ ψ x ∧ ψ x=l ∧
      (∀ᶠ y in 𝓝 x,F (y,ψ y)=F (x,l)) ∧
      ∀ᶠ z in 𝓝 (x,l), F z=F (x,l) ↔ ψ z.1=z.2 := by
  have hc:HasDerivAt (fun s:ℝ=>F (x,s)) ((fderiv ℝ F (x,l)) (0,1)) l :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_const l x).prodMk (hasDerivAt_id l))
  have hl:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1=ρ := by
    simpa using hc.unique hd
  have hi:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible:=
    real_linear_invertible (by rw [hl]; exact hρ)
  exact ⟨hF.implicitFunction (by simp) hi,hF.contDiffAt_implicitFunction (by simp) hi,
    hF.implicitFunction_apply_self (by simp) hi,
    hF.eventually_apply_implicitFunction (by simp) hi,
    hF.eventually_apply_eq_iff_implicitFunction (by simp) hi⟩
end Bernoulli.Foliation

end
end

end OAI
