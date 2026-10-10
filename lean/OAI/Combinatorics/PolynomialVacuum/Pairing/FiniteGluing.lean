import OAI.Combinatorics.PolynomialVacuum.Pairing.SeamWeight

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

private theorem decorated_illegal {M H : ℕ} [NeZero M] (κ : Fin H → ℂ)
    (d : Fin H → (ZMod M → Spin) → ℂ) (c : StackCoordinates M H)
    (hc : ¬∀v∈bandSites M H,LocalIce (coordinatesCurrent c) v) : decoratedStackWeight κ d c=0 := by
  have hz : stackLocalWeight c.1 c.2.1 c.2.2=0 := by
    by_contra hh
    exact hc (stack_ice_of_weight_ne_zero _ _ _ hh)
  simp [decoratedStackWeight,hz]

private theorem decorated_sum_closed {M H : ℕ} [NeZero M] (κ : Fin H → ℂ)
    (d : Fin H → (ZMod M → Spin) → ℂ) :
    (∑c : StackCoordinates M H,if EmptyStackBoundary c then decoratedStackWeight κ d c else 0)=
      ∑c : ClosedStack M H,decoratedStackWeight κ d c.val.val := by
  let P : StackCoordinates M H → Prop:=fun c=>∀v∈bandSites M H,LocalIce (coordinatesCurrent c) v
  have hh:=Fintype.sum_subtype_add_sum_subtype P (fun c : StackCoordinates M H=>
    if EmptyStackBoundary c then decoratedStackWeight κ d c else 0)
  have hz : (∑c : {c : StackCoordinates M H // ¬P c},if EmptyStackBoundary c.val then
      decoratedStackWeight κ d c.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [decorated_illegal κ d c.val c.property]
    simp
  rw [hz,add_zero] at hh
  rw [← hh]
  change (∑c : LegalStack M H,if EmptyStackBoundary c.val then decoratedStackWeight κ d c.val else 0)=_
  have he:=Fintype.sum_subtype_add_sum_subtype (fun c : LegalStack M H=>EmptyStackBoundary c.val)
    (fun c : LegalStack M H=>if EmptyStackBoundary c.val then decoratedStackWeight κ d c.val else 0)
  have hez : (∑c : {c : LegalStack M H // ¬EmptyStackBoundary c.val},
      if EmptyStackBoundary c.val.val then decoratedStackWeight κ d c.val.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right c.property
  rw [hez,add_zero] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro c _
  exact ite_eq_left c.property

 

theorem physical_finite_gluing (N H L k : ℕ) (hH : 0<H) (hL : L<H)
    (κ : ℂ) (hκ : κ≠0) :
    layerProduct (fun j=>decoratedTransfer N (seamTwists H L j) (seamDecoration L k κ j))
      (fun _=>.zero) (fun _=>.zero)=
    ∑S : BoundedSystem (internalEdges (bandSites (N+1) H)),
      if ∀P∈S.val.val,Separates P (0,L) (-(k : ZMod (N+1)),L) then
        (κ+κ⁻¹)^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0 := by
  rw [decorated_coordinates]
  change (∑c : StackCoordinates (N+1) H,
    if EmptyStackBoundary c then decoratedStackWeight (seamTwists H L) (seamDecoration L k κ) c else 0)=_
  rw [decorated_sum_closed]
  simp_rw [decorated_weight_current _ L k hL κ]
  rw [← (closedStackEquiv (M:=N+1) hH).symm.sum_comp]
  have he : (∑q : ClosedDomainFlow (bandSites (N+1) H),
      currentWeight (coordinatesCurrent ((closedStackEquiv (M:=N+1) hH).symm q).val.val)
        (0,L) (-(k : ZMod (N+1)),L) κ)=
      ∑q : ClosedDomainFlow (bandSites (N+1) H),currentWeight q.val.val (0,L) (-(k : ZMod (N+1)),L) κ := by
    apply Finset.sum_congr rfl
    intro q _
    have h:=congrArg (fun r : ClosedDomainFlow (bandSites (N+1) H)=>r.val.val)
      ((closedStackEquiv (M:=N+1) hH).apply_symm_apply q)
    rw [← h]
    rfl
  rw [he,← (closedDomainEquiv (bandSites (N+1) H)).sum_comp]
  exact finite_current_partition _ _ _ κ hκ

end PolynomialVacuumAlgebra

end OAI
