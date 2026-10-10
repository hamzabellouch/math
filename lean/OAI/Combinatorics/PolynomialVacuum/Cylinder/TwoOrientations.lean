import OAI.Combinatorics.PolynomialVacuum.Cylinder.CycleRigidity

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem LocalIce.value_range {q : Edge M →₀ ℤ} {v : Vertex M} (h : LocalIce q v) (k : Fin 3) :
    orientedFlow q (v,k)=0 ∨ orientedFlow q (v,k)=1 ∨ orientedFlow q (v,k)= -1 := by
  rcases h with hz | ⟨i,o,hio,h⟩
  · exact Or.inl (hz k)
  · rw [h]
    split_ifs <;> omega

theorem LocalIce.neg {q : Edge M →₀ ℤ} {v : Vertex M} (h : LocalIce q v) : LocalIce (-q) v := by
  rcases h with hz | ⟨i,o,hio,h⟩
  · left; intro k; simp [hz,map_neg]
  · right
    refine ⟨o,i,hio.symm,?_⟩
    intro k
    simp only [map_neg,Finsupp.neg_apply,h]
    ring

namespace ClosedNetwork
variable (C : ClosedNetwork M) (v : C.sites)

theorem component_ne_zero : C.componentFlow (C.polygon v)≠0 := by
  intro h
  have he:=C.component_oriented_at v v (Equiv.Perm.SameCycle.refl _ _) (C.exit v)
  rw [h,map_zero,Finsupp.zero_apply] at he
  simp [Ne.symm (C.distinct v)] at he

 

theorem two_orientations (r : Edge M →₀ ℤ) (hr : ∀ u,LocalIce r u)
    (hs : r.support=(C.polygon v).val) :
    r=C.componentFlow (C.polygon v) ∨ r= -C.componentFlow (C.polygon v) := by
  have hc := C.current_on_cycle v r (allLocalIce_conserved r hr) hs.subset
  have hq := C.component_oriented_at v v (Equiv.Perm.SameCycle.refl _ _) (C.enter v)
  have hn : orientedFlow r (v.val,C.enter v)≠0 := by
    intro hz
    have he := (orientedFlow_eq_zero_iff r (v.val,C.enter v)).mp hz
    have hqz : orientedFlow (C.componentFlow (C.polygon v)) (v.val,C.enter v)=0 := by
      apply (orientedFlow_eq_zero_iff _ _).mpr
      apply Finsupp.notMem_support_iff.mp
      rw [C.componentFlow_support _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),← hs]
      exact Finsupp.notMem_support_iff.mpr he
    simp only [ite_eq_right (C.distinct v),ite_true,zero_sub] at hq
    omega
  rcases (hr v.val).value_range (C.enter v) with hz | hp | hm
  · exact (hn hz).elim
  · right; simpa [hp] using hc
  · left; simpa [hm] using hc

end ClosedNetwork
end PolynomialVacuumCylinder

end OAI
