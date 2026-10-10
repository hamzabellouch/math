import Mathlib
import OAI.Analysis.Commutator.FactorComparison
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma initial_mem (v : Link M e f) : v.initial∈M := M.mul_mem (M.star_mem' v.mem) v.mem

lemma final_mem (v : Link M e f) : v.final∈M := M.mul_mem v.mem (M.star_mem' v.mem)

lemma trace_initial_final (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (v : Link M e f) : τ ⟨v.initial,v.initial_mem⟩=τ ⟨v.final,v.final_mem⟩ :=
  hτ (star (⟨v.val,v.mem⟩ : M)) ⟨v.val,v.mem⟩

end Link

lemma faithful_projection (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p)
    (hz : τ ⟨p,hpM⟩=0) : p=0 := by
  have hsq : star (⟨p,hpM⟩ : M)*⟨p,hpM⟩=⟨p,hpM⟩ := by
    apply Subtype.ext
    change star p*p=p
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  have hzero := hfaith ⟨p,hpM⟩ (by rw [hsq]; exact hz)
  exact congrArg Subtype.val hzero

theorem finite_factor_comparison (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hle : τ ⟨e,heM⟩≤τ ⟨f,hfM⟩) :
    ∃ v : Link M e f, v.initial=e := by
  obtain ⟨v,hv⟩ := factor_comparison M hM heM hfM he hf
  refine ⟨v,?_⟩
  rcases hv with hv|hv
  · exact hv
  · have htf : (⟨v.final,v.final_mem⟩ : M)=⟨f,hfM⟩ := Subtype.ext hv
    have hti : τ ⟨v.initial,v.initial_mem⟩=τ ⟨f,hfM⟩ := by
      rw [v.trace_initial_final τ hτ,htf]
    have hmem : e-v.initial∈M := M.sub_mem heM v.initial_mem
    have hnonneg : 0≤τ ⟨e-v.initial,hmem⟩ := τ.map_nonneg
      (show (0 : M)≤⟨e-v.initial,hmem⟩ from sub_nonneg.mpr v.source_le)
    have hzero : τ ⟨e-v.initial,hmem⟩=0 := by
      apply le_antisymm ?_ hnonneg
      change τ ((⟨e,heM⟩ : M)-⟨v.initial,v.initial_mem⟩)≤0
      rw [map_sub,hti]
      exact sub_nonpos.mpr hle
    exact (sub_eq_zero.mp (faithful_projection M τ hfaith hmem
      (v.residual_source_projection he) hzero)).symm

theorem finite_factor_equivalence (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (heq : τ ⟨e,heM⟩=τ ⟨f,hfM⟩) :
    ∃ v∈M, star v*v=e ∧ v*star v=f := by
  obtain ⟨v,hvi⟩ := finite_factor_comparison M hM τ hτ hfaith heM hfM he hf heq.le
  have hti : τ ⟨v.initial,v.initial_mem⟩=τ ⟨e,heM⟩ :=
    congrArg τ (Subtype.ext hvi)
  have htf : τ ⟨v.final,v.final_mem⟩=τ ⟨f,hfM⟩ :=
    (v.trace_initial_final τ hτ).symm.trans (hti.trans heq)
  have hmem : f-v.final∈M := M.sub_mem hfM v.final_mem
  have hzero : τ ⟨f-v.final,hmem⟩=0 := by
    change τ ((⟨f,hfM⟩ : M)-⟨v.final,v.final_mem⟩)=0
    rw [map_sub,htf,sub_self]
  have hvf := (sub_eq_zero.mp (faithful_projection M τ hfaith hmem
    (v.residual_target_projection hf) hzero)).symm
  exact ⟨v.val,v.mem,hvi,hvf⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
