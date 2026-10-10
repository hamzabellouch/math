import OAI.Algebra.OddKaplansky.GreedyLift

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
open Submodule
variable {K : Type portUniverse1} {D : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommRing D] [Fintype S] [sectionInstance57 : LinearOrder S]
variable (ε : D →+* K) (unitLift : ∀ d : D, ε d ≠ 0 → IsUnit d)
variable (E : Matrix S S D) (hE : E*E=E)
def E₀ : Matrix S S K := E.map ε
lemma E₀_idem
    {K : Type contextUniverse1}
    {D : Type contextUniverse2}
    {S : Type contextUniverse3}
    [contextInstance3 : Field.{contextUniverse1} K]
    [contextInstance4 : CommRing.{contextUniverse2} D]
    [contextInstance5 : Fintype.{contextUniverse3} S]
    [LinearOrder.{contextUniverse3} S]
    (ε : @RingHom.{contextUniverse2, contextUniverse1} D K
  (@Semiring.toNonAssocSemiring.{contextUniverse2} D
    (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4)))
  (@Semiring.toNonAssocSemiring.{contextUniverse1} K
    (@CommSemiring.toSemiring.{contextUniverse1} K
      (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance3)))))
    (E : Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (hE : @Eq.{max (contextUniverse2 + 1) (contextUniverse3 + 1)} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
  (@HMul.hMul.{max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3, max contextUniverse2 contextUniverse3} (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D) (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (Matrix.{contextUniverse3, contextUniverse3, contextUniverse2} S S D)
    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{contextUniverse2, contextUniverse3, contextUniverse3, contextUniverse3} S S S D contextInstance5
      (@Distrib.toMul.{contextUniverse2} D
        (@instDistribOfSemiring.{contextUniverse2} D
          (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
      (@Semiring.toAddCommMonoid.{contextUniverse2} D
        (@CommSemiring.toSemiring.{contextUniverse2} D (@CommRing.toCommSemiring.{contextUniverse2} D contextInstance4))))
    E E)
  E) : E₀ ε E*E₀ ε E=E₀ ε E := by
  change E.map ε*E.map ε=E.map ε
  rw [← Matrix.map_mul,hE]
abbrev I := GreedyLift.I (E₀ ε E)
abbrev J := GreedyLift.J (E₀ ε E)
def columns : I ε E ⊕ J ε E → (S → D) := Sum.elim (fun i => E.col i.val) (fun j => (1-E).col j.val)
def indices : S ≃ I ε E ⊕ J ε E := GreedyLift.indices (E₀ ε E) (E₀_idem ε E hE)

def Q : Matrix S S D := fun s t => columns ε E (indices ε E hE t) s
lemma Q_map : (Q ε E hE).map ε=GreedyLift.matrix (E₀ ε E) (E₀_idem ε E hE) := by
  funext s t
  change ε (columns ε E (indices ε E hE t) s) = GreedyLift.columns (E₀ ε E) (indices ε E hE t) s
  cases hi : indices ε E hE t with
  | inl i => rfl
  | inr j =>
    change ε ((1-E) s j.val)=(1-E₀ ε E) s j.val
    simp only [Matrix.sub_apply,map_sub,E₀,Matrix.map_apply,Matrix.one_apply]
    by_cases h : s=j.val <;> simp [h]
include unitLift in
lemma Q_det_unit : IsUnit (Q ε E hE).det := by
  apply unitLift
  rw [RingHom.map_det]
  change ((Q ε E hE).map ε).det ≠ 0
  rw [Q_map]
  exact GreedyLift.matrix_det _ _
def equiv : (S → D) ≃ₗ[D] (S → D) :=
  Matrix.toLin'OfInv (Matrix.nonsing_inv_mul (Q ε E hE) (Q_det_unit ε unitLift E hE))
    (Matrix.mul_nonsing_inv (Q ε E hE) (Q_det_unit ε unitLift E hE))
lemma equiv_apply (x : S → D) : equiv ε unitLift E hE x=(Q ε E hE).mulVec x := rfl
lemma equiv_symm_apply (x : S → D) : (equiv ε unitLift E hE).symm x=(Q ε E hE)⁻¹.mulVec x := rfl

def basis : Module.Basis (I ε E ⊕ J ε E) D (S → D) :=
  ((Pi.basisFun D S).map (equiv ε unitLift E hE)).reindex (indices ε E hE)
lemma basis_apply (i : I ε E ⊕ J ε E) : basis ε unitLift E hE i=columns ε E i := by
  rw [basis,Module.Basis.reindex_apply,Module.Basis.map_apply,Pi.basisFun_apply,equiv_apply,Matrix.mulVec_single_one]
  funext s
  change columns ε E (indices ε E hE ((indices ε E hE).symm i)) s=columns ε E i s
  rw [Equiv.apply_symm_apply]
lemma basis_inl (i : I ε E) : basis ε unitLift E hE (Sum.inl i)=E.col i.val := basis_apply ε unitLift E hE _
lemma basis_inr (j : J ε E) : basis ε unitLift E hE (Sum.inr j)=(1-E).col j.val := basis_apply ε unitLift E hE _
lemma fixed_inl (i : I ε E) : Matrix.toLin' E (basis ε unitLift E hE (Sum.inl i))=basis ε unitLift E hE (Sum.inl i) := by
  rw [basis_inl]
  change (E*E).col i.val=E.col i.val
  rw [hE]
lemma killed_inr (j : J ε E) : Matrix.toLin' E (basis ε unitLift E hE (Sum.inr j))=0 := by
  rw [basis_inr]
  change (E*(1-E)).col j.val=0
  rw [mul_sub,mul_one,hE,sub_self]
  rfl
lemma image_independent : LinearIndependent D (fun i : I ε E => basis ε unitLift E hE (Sum.inl i)) :=
  (basis ε unitLift E hE).linearIndependent.comp Sum.inl Sum.inl_injective
lemma image_span : span D (Set.range (fun i : I ε E => basis ε unitLift E hE (Sum.inl i)))=LinearMap.range (Matrix.toLin' E) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro x ⟨i,rfl⟩
    exact ⟨basis ε unitLift E hE (Sum.inl i),fixed_inl ε unitLift E hE i⟩
  · rintro x ⟨y,rfl⟩
    have hy := congrArg (fun z : S → D => Matrix.toLin' E z) ((basis ε unitLift E hE).sum_repr y)
    rw [← hy,map_sum,Fintype.sum_sum_type]
    simp only [map_smul,fixed_inl,killed_inr,smul_zero,Finset.sum_const_zero,add_zero]
    apply Submodule.sum_mem
    intro i _
    exact smul_mem _ _ (subset_span ⟨i,rfl⟩)
def imageBasis : Module.Basis (I ε E) D (LinearMap.range (Matrix.toLin' E)) :=
  (Module.Basis.span (image_independent ε unitLift E hE)).map (LinearEquiv.ofEq _ _ (image_span ε unitLift E hE))
lemma imageBasis_apply (i : I ε E) : (imageBasis ε unitLift E hE i : S → D)=E.col i.val := by
  simp only [imageBasis,Module.Basis.map_apply,LinearEquiv.ofEq,Module.Basis.span_apply,basis_inl]
  rfl
end
end OddKaplansky.GreedyRing

end

end OAI
