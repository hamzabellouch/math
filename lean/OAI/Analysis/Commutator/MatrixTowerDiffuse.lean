import Mathlib
import OAI.Analysis.Commutator.MatrixColumnCorner
import OAI.Analysis.Commutator.MatrixTower

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hfaith in
lemma projection_trace_positive {p : M} (hp : IsStarProjection p) (hpn : p≠0) :
    0<(τ p).re := by
  have hn := τ.map_nonneg hp.nonneg
  apply lt_of_le_of_ne hn.1
  intro heq
  apply hpn
  apply hfaith
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  exact Complex.ext heq.symm hn.2.symm

include hτ hfaith in
lemma diffuse_of_small (hfac : FactorCorner.IsFactor M)
    (hsmall : ∀ ε : ℝ,0<ε → ∃ q : M,IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε) :
    DiffuseProjection.HasNoMinimalProjections M := by
  intro p hpM hp hpn
  let p' : M := ⟨p,hpM⟩
  have hp' : IsStarProjection p' := ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩
  have hpn' : p'≠0 := fun h => hpn (congrArg Subtype.val h)
  obtain ⟨q,hq,hqn,hqt⟩ := hsmall (τ p').re (projection_trace_positive M τ hfaith hp' hpn')
  have hle : τ q≤τ p' := ⟨hqt.le,(τ.map_nonneg hq.nonneg).2.symm.trans (τ.map_nonneg hp'.nonneg).2⟩
  have hq' : IsStarProjection (q : H →L[ℂ] H) := hq.map M.toStarSubalgebra.subtype
  obtain ⟨v,hvi⟩ := PartialIsometryOrder.finite_factor_comparison M hfac τ hτ hfaith
    q.property hpM hq' hp hle
  have htrace : τ ⟨v.final,v.final_mem⟩=τ q := by
    rw [←v.trace_initial_final τ hτ]
    exact congrArg τ (Subtype.ext hvi)
  have hpos : 0<(τ ⟨v.final,v.final_mem⟩).re := by
    rw [htrace]; exact projection_trace_positive M τ hfaith hq hqn
  refine ⟨v.final,v.final_mem,v.final_projection,?_,?_,v.target_le⟩
  · intro hz
    have hz' : (⟨v.final,v.final_mem⟩:M)=0 := Subtype.ext hz
    rw [hz',map_zero] at hpos
    exact lt_irrefl _ hpos
  · intro heq
    have heq' : (⟨v.final,v.final_mem⟩:M)=p' := Subtype.ext heq
    rw [heq'] at htrace
    exact (ne_of_lt hqt) (congrArg Complex.re htrace.symm)

include hτ hone in
lemma small_of_stages (F : ℕ → Stage M)
    (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) {ε : ℝ} (hε : 0<ε) :
    ∃ q : M,IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε := by
  obtain ⟨N,hN,hNε⟩ := Real.exists_nat_pos_inv_lt hε
  obtain ⟨n,hn⟩ := hsize N
  let i : (F n).I := Classical.choice inferInstance
  let q := (F n).hom (Matrix.single i i 1)
  have hqt : τ q=(Fintype.card (F n).I:ℂ)⁻¹ :=
    MatrixColumnCorner.trace_minimal τ hτ hone (F n).hom i
  have hq : IsStarProjection q := (MatrixColumnCorner.minimal_projection i).map (F n).hom
  refine ⟨q,hq,?_,?_⟩
  · intro hz
    rw [hz,map_zero] at hqt
    exact (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero (α:=(F n).I))) hqt.symm
  · rw [hqt,show (Fintype.card (F n).I:ℂ)=((Fintype.card (F n).I:ℝ):ℂ) by simp,
      ←Complex.ofReal_inv,Complex.ofReal_re]
    exact (inv_anti₀ (by exact_mod_cast hN) (by exact_mod_cast hn.le)).trans_lt hNε

include hτ hfaith hone in
lemma diffuse_of_stages (hfac : FactorCorner.IsFactor M) (F : ℕ → Stage M)
    (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) :
    DiffuseProjection.HasNoMinimalProjections M :=
  diffuse_of_small M τ hτ hfaith hfac (fun _ hε => small_of_stages M τ hτ hone F hsize hε)

end Kadison.MatrixTower

end

end
end

end OAI
