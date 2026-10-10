import OAI.Combinatorics.PolynomialVacuum.Cylinder.DomainWeight
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackProperties

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]
noncomputable def bandVertexEquiv : (Fin H × ZMod M × Bool) ≃ {v : Vertex M // v∈bandSites M H} :=
  Equiv.ofBijective (fun p=>⟨if p.2.2 then .down p.2.1 p.1.val else .up p.2.1 p.1.val,by
    rw [mem_bandSites]
    cases p.2.2 <;> simp [InBand,vertexLayer,Nat.cast_nonneg,p.1.isLt]⟩) ⟨by
      rintro ⟨j,i,b⟩ ⟨k,l,c⟩ he
      have hh:=congrArg Subtype.val he
      cases b <;> cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hh
      · obtain ⟨rfl,hj⟩:=Vertex.up.inj hh
        have hj' : j=k := Fin.ext (Int.ofNat_inj.mp hj)
        subst k; rfl
      · cases hh
      · cases hh
      · obtain ⟨rfl,hj⟩:=Vertex.down.inj hh
        have hj' : j=k := Fin.ext (Int.ofNat_inj.mp hj)
        subst k; rfl,by
      intro v
      have hv : 0≤vertexLayer v.val ∧ vertexLayer v.val<(H : ℤ) := (mem_bandSites H v.val).mp v.property
      rcases v with ⟨v,hv'⟩
      cases v with
      | up i j =>
        refine ⟨⟨⟨j.toNat,by dsimp [vertexLayer] at hv; omega⟩,i,false⟩,Subtype.ext ?_⟩
        change Vertex.up i (j.toNat : ℤ)=Vertex.up i j
        congr 1
        dsimp [vertexLayer] at hv
        omega
      | down i j =>
        refine ⟨⟨⟨j.toNat,by dsimp [vertexLayer] at hv; omega⟩,i,true⟩,Subtype.ext ?_⟩
        change Vertex.down i (j.toNat : ℤ)=Vertex.down i j
        congr 1
        dsimp [vertexLayer] at hv
        omega⟩

theorem band_product (f : Vertex M → ℂ) :
    (∏v∈bandSites M H,f v)=∏j : Fin H,∏i : ZMod M,f (.up i j.val)*f (.down i j.val) := by
  have he:= (bandVertexEquiv (M:=M) (H:=H)).prod_comp (fun v=>f v.val)
  rw [Fintype.prod_prod_type] at he
  simp only [Fintype.prod_prod_type,Fintype.prod_bool] at he
  rw [Finset.prod_coe_sort] at he
  change (∏j : Fin H,∏i : ZMod M,f (.down i j.val)*f (.up i j.val))=_ at he
  simpa only [mul_comm] using he.symm

theorem stack_local_domain (v : Fin (H+1) → ZMod M → Spin) (a k : Fin H → ZMod M → Spin) :
    (∏p∈bandSites M H,localCurrentWeight (stackCurrent v a k) p)=stackLocalWeight v a k :=
  band_product _
end PolynomialVacuumCylinder

end OAI
