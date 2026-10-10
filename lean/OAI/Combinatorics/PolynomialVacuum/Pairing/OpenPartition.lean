import OAI.Combinatorics.PolynomialVacuum.Pairing.StackReindex
import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenEquiv

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

private theorem illegal_coordinate_weight {M H : ℕ} [NeZero M] (c : StackCoordinates M H)
    (hi : ¬∀v∈bandSites M H,LocalIce (coordinatesCurrent c) v) :
    domainWeight (bandSites M H) (coordinatesCurrent c)=0 := by
  by_contra hw
  have he : stackLocalWeight c.1 c.2.1 c.2.2≠0 := by
    rw [coordinatesCurrent,domainWeight,stack_local_domain] at hw
    exact (mul_ne_zero_iff.mp hw).1
  exact hi (stack_ice_of_weight_ne_zero _ _ _ he)

private theorem coordinate_sum_legal {M H : ℕ} [NeZero M] (inp out : ZMod M → Spin) :
    (∑c : StackCoordinates M H,if matchesBoundary c.1 inp out then
      domainWeight (bandSites M H) (coordinatesCurrent c) else 0)=
    ∑c : LegalStack M H,if matchesBoundary c.val.1 inp out then
      domainWeight (bandSites M H) (coordinatesCurrent c.val) else 0 := by
  let P : StackCoordinates M H → Prop:=fun c=>∀v∈bandSites M H,LocalIce (coordinatesCurrent c) v
  have hh:=Fintype.sum_subtype_add_sum_subtype P (fun c : StackCoordinates M H=>
    if matchesBoundary c.1 inp out then domainWeight (bandSites M H) (coordinatesCurrent c) else 0)
  have hz : (∑c : {c : StackCoordinates M H // ¬P c},if matchesBoundary c.val.1 inp out then
      domainWeight (bandSites M H) (coordinatesCurrent c.val) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [illegal_coordinate_weight c.val c.property]
    split_ifs <;> rfl
  rw [hz,add_zero] at hh
  exact hh.symm

theorem physicalTransfer_pow_flows (N H : ℕ) (hH : 0<H) (out inp : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) zeta^H) out inp=
      ∑q : BandFlow (N+1) H,
        if matchesBoundary (recoverVertical H q.val) (cylinderState N inp) (cylinderState N out) then
          domainWeight (bandSites (N+1) H) q.val else 0 := by
  rw [physicalTransfer_pow_coordinates,coordinate_sum_legal,← (stackFlowEquiv (M:=N+1) hH).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  change (if matchesBoundary (recoverVertical H q.val) _ _ then
    domainWeight _ (coordinatesCurrent (recoverCoordinates q.val)) else 0)=_
  have he : coordinatesCurrent (recoverCoordinates (H:=H) q.val)=q.val :=
    recover_stack q.val q.property.1 q.property.2
  rw [he]
end PolynomialVacuumAlgebra
namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

private theorem closed_zero_boundary (r : Edge M →₀ ℤ) (hr : activeSites r⊆bandSites M H)
    (i : ZMod M) : r ((i,0),0)=0 ∧ r ((i,(H : ℤ)),0)=0 := by
  have hz (v : Vertex M) (hv : v∉bandSites M H) (k : Fin 3) : orientedFlow r (v,k)=0 := by
    by_contra hh
    exact hv (hr ((mem_activeSites r v).mpr ⟨k,hh⟩))
  constructor
  · have hh:=hz (.down i (-1)) (by simp [mem_bandSites,InBand,vertexLayer]) 0
    simpa [orientedFlow_down,edgeOf] using hh
  · simpa only [orientedFlow_up] using hz (.up i H) (by simp [mem_bandSites,InBand,vertexLayer]) 0

theorem closed_boundary_match (q r : Edge M →₀ ℤ) (hr : activeSites r⊆bandSites M H)
    (inp out : ZMod M → Spin) :
    matchesBoundary (recoverVertical H (q+r)) inp out ↔ matchesBoundary (recoverVertical H q) inp out := by
  have h0 : recoverVertical H (q+r) 0=recoverVertical H q 0 := by
    funext i
    simp only [recoverVertical,Fin.val_zero,Nat.cast_zero,Finsupp.add_apply,(closed_zero_boundary r hr i).1,add_zero]
  have hH : recoverVertical H (q+r) (Fin.last H)=recoverVertical H q (Fin.last H) := by
    funext i
    simp only [recoverVertical,Fin.val_last,Finsupp.add_apply,(closed_zero_boundary r hr i).2,add_zero]
  simp only [matchesBoundary,h0,hH]

 

theorem band_partition_arcs_boundary (inp out : ZMod M → Spin) :
    (∑q : BandFlow M H,if matchesBoundary (recoverVertical H q.val) inp out then
      domainWeight (bandSites M H) q.val else 0)=
    ∑S : ArcSystem (bandSites M H),if matchesBoundary (recoverVertical H S.current) inp out then S.weight else 0 := by
  rw [← (openFlowEquiv (M:=M) (H:=H)).sum_comp]
  change (∑B : ArcClosedData (bandSites M H),if matchesBoundary (recoverVertical H B.current) inp out then
    domainWeight (bandSites M H) B.current else 0)=_
  simp_rw [ArcClosedData.current,closed_boundary_match _ _ (ArcClosedData.closed_subset _)]
  change (∑B : ArcClosedData (bandSites M H),if matchesBoundary (recoverVertical H B.1.current) inp out then
    domainWeight (bandSites M H) B.current else 0)=_
  simp_rw [ArcClosedData.weight_factor]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  change (∑r : ClosedDomainFlow _,if matchesBoundary (recoverVertical H S.current) inp out then
    S.weight*uniformSeamWeight r.val.val else 0)=_
  split_ifs with h
  · rw [← Finset.mul_sum,closed_domain_partition_one,mul_one]
  · simp only [Finset.sum_const_zero]
end PolynomialVacuumCylinder
namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

theorem physicalTransfer_pow_arcs (N H : ℕ) (hH : 0<H) (out inp : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) zeta^H) out inp=
    ∑S : ArcSystem (bandSites (N+1) H),
      if matchesBoundary (recoverVertical H S.current) (cylinderState N inp) (cylinderState N out)
      then S.weight else 0 := by
  rw [physicalTransfer_pow_flows N H hH,band_partition_arcs_boundary]
end PolynomialVacuumAlgebra

end OAI
