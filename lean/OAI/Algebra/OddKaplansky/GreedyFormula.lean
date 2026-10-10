import OAI.Algebra.OddKaplansky.GreedyRectangle

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {D : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommRing D] [Fintype S] [LinearOrder S]
variable (ε : D →+* K) (unitLift : ∀ d : D, ε d ≠ 0 → IsUnit d)
variable (E : Matrix S S D) (hE : E*E=E)
lemma inverse_basis (i : I ε E ⊕ J ε E) :
    (equiv ε unitLift E hE).symm (basis ε unitLift E hE i)=Pi.single ((indices ε E hE).symm i) 1 := by
  rw [basis,Module.Basis.reindex_apply,Module.Basis.map_apply,LinearEquiv.symm_apply_apply,Pi.basisFun_apply]

lemma imageBasis_coordinate (i : I ε E) (x : LinearMap.range (Matrix.toLin' E)) :
    (imageBasis ε unitLift E hE).equivFun x i =
      (equiv ε unitLift E hE).symm (x : S → D) ((indices ε E hE).symm (Sum.inl i)) := by
  let F : LinearMap.range (Matrix.toLin' E) →ₗ[D] D :=
    LinearMap.proj i ∘ₗ (imageBasis ε unitLift E hE).equivFun.toLinearMap
  let G : LinearMap.range (Matrix.toLin' E) →ₗ[D] D :=
    LinearMap.proj ((indices ε E hE).symm (Sum.inl i)) ∘ₗ
      (equiv ε unitLift E hE).symm.toLinearMap ∘ₗ (LinearMap.range (Matrix.toLin' E)).subtype
  have hh : F=G := by
    apply (imageBasis ε unitLift E hE).ext
    intro j
    change (imageBasis ε unitLift E hE).equivFun (imageBasis ε unitLift E hE j) i =
      (equiv ε unitLift E hE).symm (imageBasis ε unitLift E hE j : S → D) ((indices ε E hE).symm (Sum.inl i))
    rw [imageBasis_apply,← basis_inl ε unitLift E hE j,inverse_basis]
    simp [Pi.single_apply,eq_comm]
  exact congrArg (fun L => L x) hh

lemma inverse_first_projection (i : I ε E) (x : S → D) :
    (equiv ε unitLift E hE).symm (Matrix.toLin' E x) ((indices ε E hE).symm (Sum.inl i))=
      (equiv ε unitLift E hE).symm x ((indices ε E hE).symm (Sum.inl i)) := by
  let F : (S → D) →ₗ[D] D := LinearMap.proj ((indices ε E hE).symm (Sum.inl i)) ∘ₗ
    (equiv ε unitLift E hE).symm.toLinearMap ∘ₗ Matrix.toLin' E
  let G : (S → D) →ₗ[D] D := LinearMap.proj ((indices ε E hE).symm (Sum.inl i)) ∘ₗ
    (equiv ε unitLift E hE).symm.toLinearMap
  have hh : F=G := by
    apply (basis ε unitLift E hE).ext
    intro a
    cases a with
    | inl j => simp only [F,G,LinearMap.comp_apply,fixed_inl]
    | inr j =>
      change (equiv ε unitLift E hE).symm (Matrix.toLin' E (basis ε unitLift E hE (Sum.inr j))) _ = _
      rw [killed_inr,map_zero]
      change 0=(equiv ε unitLift E hE).symm (basis ε unitLift E hE (Sum.inr j)) _
      rw [inverse_basis]
      simp
  exact congrArg (fun L => L x) hh
variable {W : Type portUniverse4} {N : Type portUniverse5} [Fintype W] [LinearOrder W] [Fintype N] [LinearOrder N]
variable (hpair : Fintype.card N*Fintype.card S=Fintype.card W*Fintype.card (I ε E))
lemma coordinateEquiv_symm_formula (y : W → LinearMap.range (Matrix.toLin' E)) (n : N) (s : S) :
    (coordinateEquiv ε unitLift E hE hpair).symm y n s =
      (imageBasis ε unitLift E hE).equivFun (y (pairing ε E hpair (n,s)).1) (pairing ε E hpair (n,s)).2 := rfl
lemma rectangleY_formula (n : N) (w : W) (v : S → D) (s : S) :
    rectangleY ε unitLift E hE hpair n w v s =
      if (pairing ε E hpair (n,s)).1=w then
        (Q ε E hE)⁻¹.mulVec v ((indices ε E hE).symm (Sum.inl (pairing ε E hpair (n,s)).2)) else 0 := by
  let : DecidableEq W := Classical.decEq W
  let : DecidableEq N := Classical.decEq N
  change (coordinateEquiv ε unitLift E hE hpair).symm (Pi.single w ((Matrix.toLin' E).rangeRestrict v)) n s = _
  rw [coordinateEquiv_symm_formula]
  by_cases hw : (pairing ε E hpair (n,s)).1=w
  · rw [ite_eq_left hw,Pi.single_apply,ite_eq_left hw,imageBasis_coordinate]
    change (equiv ε unitLift E hE).symm (Matrix.toLin' E v) _ = _
    exact (inverse_first_projection ε unitLift E hE (pairing ε E hpair (n,s)).2 v).trans
      (congrFun (equiv_symm_apply ε unitLift E hE v) ((indices ε E hE).symm (Sum.inl (pairing ε E hpair (n,s)).2)))
  · rw [ite_eq_right hw,Pi.single_apply,ite_eq_right hw,map_zero]
    rfl
lemma coordinateEquiv_formula (x : N → S → D) (w : W) :
    (coordinateEquiv ε unitLift E hE hpair x w : S → D) =
      ∑ i : I ε E, x ((pairing ε E hpair).symm (w,i)).1 ((pairing ε E hpair).symm (w,i)).2 • E.col i.val := by
  change ((imageBasis ε unitLift E hE).equivFun.symm
    (fun i => x ((pairing ε E hpair).symm (w,i)).1 ((pairing ε E hpair).symm (w,i)).2) : S → D) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,imageBasis_apply]

lemma rectangleJ_formula (w : W) (n : N) (v : S → D) (s : S) :
    rectangleJ ε unitLift E hE hpair w n v s =
      ∑ i : I ε E, if ((pairing ε E hpair).symm (w,i)).1=n then
        v ((pairing ε E hpair).symm (w,i)).2 * E s i.val else 0 := by
  let : DecidableEq W := Classical.decEq W
  let : DecidableEq N := Classical.decEq N
  change (coordinateEquiv ε unitLift E hE hpair (Pi.single n v) w : S → D) s = _
  rw [coordinateEquiv_formula]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hn : ((pairing ε E hpair).symm (w,i)).1=n <;> simp [hn]
end
end OddKaplansky.GreedyRing

end

end OAI
