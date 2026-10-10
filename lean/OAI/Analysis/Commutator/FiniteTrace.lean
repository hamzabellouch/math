import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.FiniteFactorComparison

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FiniteTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

def restrict : M →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp M.toStarSubalgebra.subtype.toLinearMap
  monotone' := fun _ _ h => τ.monotone h

@[simp] lemma restrict_apply (a : M) : restrict M τ a=τ (a : H →L[ℂ] H) := rfl

lemma projection_trace_pos
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) : 0<(τ p).re := by
  have hn := τ.map_nonneg hp.nonneg
  apply lt_of_le_of_ne hn.1
  intro heq
  have hz : τ p=0 := Complex.ext heq.symm hn.2.symm
  apply hpn
  apply hfaith p hpM
  rwa [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

lemma restrict_tracial (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a)) :
    ∀ a b : M, restrict M τ (a*b)=restrict M τ (b*a) :=
  fun a b => hτ a a.property b b.property

lemma restrict_faithful (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0) :
    ∀ a : M, restrict M τ (star a*a)=0 → a=0 :=
  fun a ha => Subtype.ext (hfaith a a.property ha)

theorem noMinimal_of_small (hM : FactorCorner.IsFactor M)
    (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    (hsmall : ∀ ε : ℝ, 0<ε → ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε) :
    DiffuseProjection.HasNoMinimalProjections M := by
  intro p hpM hp hpn
  obtain ⟨q,hqM,hq,hqn,hqt⟩ := hsmall (τ p).re (projection_trace_pos M τ hfaith hpM hp hpn)
  have hle : τ q≤τ p := ⟨hqt.le,(τ.map_nonneg hq.nonneg).2.symm.trans (τ.map_nonneg hp.nonneg).2⟩
  obtain ⟨v,hvi⟩ := PartialIsometryOrder.finite_factor_comparison M hM (restrict M τ)
    (restrict_tracial M τ hτ) (restrict_faithful M τ hfaith) hqM hpM hq hp hle
  have htrace : τ v.final=τ q := by
    have h := (v.trace_initial_final (restrict M τ) (restrict_tracial M τ hτ)).symm
    change τ v.final=τ v.initial at h
    rwa [hvi] at h
  have hpos : 0<(τ v.final).re := by rw [htrace]; exact projection_trace_pos M τ hfaith hqM hq hqn
  refine ⟨v.final,v.final_mem,v.final_projection,?_,?_,v.target_le⟩
  · intro hz
    rw [hz,map_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · intro heq
    rw [heq] at htrace
    exact (ne_of_lt hqt) (congrArg Complex.re htrace.symm)

end Kadison.FiniteTrace

end

end
end

end OAI
