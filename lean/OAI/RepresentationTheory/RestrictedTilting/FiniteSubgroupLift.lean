import OAI.RepresentationTheory.RestrictedTilting.RestrictedLift
import OAI.RepresentationTheory.RestrictedTilting.CoordinateTensor

namespace OAI

namespace FiberFunctorProof
universe u v
variable (k : Type u) [Field k]
variable {E : Type v} [AddGroup E] [Fintype E]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

 

theorem finite_subgroup_polynomial_lift (l : E →+ k) (hl : Function.Injective l)
    (σ : Representation k (Multiplicative E) (ι → k)) :
    ∃ ρ : Representation k (Multiplicative k) (ι → k),
      ∃ P : Matrix ι ι (Polynomial k),
        (∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t))) ∧
        (∀ i j, (P i j).natDegree ≤ Fintype.card E - 1) ∧
        (∀ a : E, ρ (Multiplicative.ofAdd (l a)) = σ (Multiplicative.ofAdd a)) := by
  classical
  let H := l.range
  let e : E ≃+ H := AddMonoidHom.ofInjective hl
  let σH := σ.comp (AddEquiv.toMultiplicative e.symm).toMonoidHom
  let R : Multiplicative H →* Matrix ι ι k := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σH
  let P := liftEntry H R
  let ρ : Representation k (Multiplicative k) (ι → k) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (extendedRepresentation H R)
  have heval (t : k) : LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)) = liftMatrix H R t := by
    exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
  refine ⟨ρ,P,fun t => (heval t).symm,fun i j => ?_,fun a => ?_⟩
  · have hc : Fintype.card H = Fintype.card E := Fintype.card_congr e.toEquiv.symm
    by_cases hz : P i j = 0
    · simp only [hz, Polynomial.natDegree_zero, Nat.zero_le]
    · have hd := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (liftEntry_degree H R i j)
      rw [hc] at hd
      omega
  · apply LinearMap.toMatrix'.injective
    rw [heval]
    have hla : l a = ((e a : H) : k) := rfl
    rw [hla, liftMatrix_at_subgroup]
    change LinearMap.toMatrix' (σ (Multiplicative.ofAdd (e.symm (e a)))) = _
    rw [e.symm_apply_apply]
end FiberFunctorProof

end OAI
