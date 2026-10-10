import OAI.Combinatorics.PolynomialVacuum.Cylinder.ClosedCancellation
import OAI.Combinatorics.PolynomialVacuum.Cylinder.LayerCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ}

noncomputable def domainOccupation (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) : ℕ :=
  (D ∩ activeSites q).card
noncomputable def domainTurn (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) : ℤ :=
  ∑v∈D,localTurn q v
noncomputable def domainWeight (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) : ℂ :=
  (∏v∈D,localCurrentWeight q v) * zeta^(columnTotal q 1)

theorem localIce_iff_triple (q : Edge M →₀ ℤ) (v : Vertex M) :
    LocalIce q v ↔ IceTriple (orientedFlow q (v,0)) (orientedFlow q (v,1)) (orientedFlow q (v,2)) := by
  have ht : ∀j : Fin 3,arrowTriple (orientedFlow q (v,0)) (orientedFlow q (v,1))
      (orientedFlow q (v,2)) j=orientedFlow q (v,j) := by intro j; fin_cases j <;> rfl
  simp only [LocalIce,IceTriple,ht]

theorem occupation_eq_indicator (q : Edge M →₀ ℤ) (v : Vertex M) :
    vertexOccupation (orientedFlow q (v,0)) (orientedFlow q (v,1)) (orientedFlow q (v,2))=
      if v∈activeSites q then 1 else 0 := by
  have hz : (orientedFlow q (v,0)=0 ∧ orientedFlow q (v,1)=0 ∧ orientedFlow q (v,2)=0) ↔ v∉activeSites q := by
    rw [mem_activeSites]
    constructor
    · rintro ⟨h0,h1,h2⟩ ⟨k,hk⟩
      fin_cases k <;> simp_all
    · intro h
      push Not at h
      exact ⟨h 0,h 1,h 2⟩
  simp only [vertexOccupation,hz]
  split_ifs <;> simp_all

theorem local_weight_shape (q : Edge M →₀ ℤ) (v : Vertex M) (hv : LocalIce q v) :
    localCurrentWeight q v=xStar^(if v∈activeSites q then (1 : ℕ) else 0)*loopTurnPhase (localTurn q v) := by
  simp only [localCurrentWeight,arrowVertexWeight,ite_eq_left ((localIce_iff_triple q v).mp hv),
    occupation_eq_indicator,localTurn]

private theorem phase_product (D : Finset (Vertex M)) (f : Vertex M → ℤ) :
    (∏v∈D,loopTurnPhase (f v))=loopTurnPhase (∑v∈D,f v) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert v D hv ih => simp [hv,ih]

theorem local_product_shape (D : Finset (Vertex M)) (q : Edge M →₀ ℤ)
    (hi : ∀v∈D,LocalIce q v) :
    (∏v∈D,localCurrentWeight q v)=xStar^domainOccupation D q*loopTurnPhase (domainTurn D q) := by
  rw [Finset.prod_congr rfl (fun v hv => local_weight_shape q v (hi v hv))]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,phase_product]
  have hc : (∑v∈D,if v∈activeSites q then (1 : ℕ) else 0)=domainOccupation D q := by
    simp [domainOccupation]
  rw [hc]
  rfl

theorem localTurn_of_not_active (q : Edge M →₀ ℤ) (v : Vertex M) (hv : v∉activeSites q) :
    localTurn q v=0 := by
  have hz : ∀k,orientedFlow q (v,k)=0 := by simpa only [mem_activeSites,not_exists,not_not] using hv
  simp [localTurn,hz]

theorem domainWeight_closed (D : Finset (Vertex M)) (q : Edge M →₀ ℤ)
    (hi : ∀v,LocalIce q v) (hc : activeSites q⊆D) : domainWeight D q=uniformSeamWeight q := by
  have hn : domainOccupation D q=(activeSites q).card := by
    rw [domainOccupation,Finset.inter_eq_right.mpr hc]
  have ht : domainTurn D q=flowTurn q := by
    symm
    apply Finset.sum_subset hc
    intro v _ hv
    exact localTurn_of_not_active q v hv
  rw [domainWeight,local_product_shape D q (fun v _ => hi v),hn,ht]
  rfl

end PolynomialVacuumCylinder

end OAI
