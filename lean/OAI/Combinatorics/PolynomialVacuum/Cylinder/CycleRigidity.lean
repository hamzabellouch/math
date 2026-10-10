import OAI.Combinatorics.PolynomialVacuum.Cylinder.IceCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem flow_support_mono_zero (r q : Edge M →₀ ℤ) (hs : r.support⊆q.support)
    (g : Germ M) (hz : orientedFlow q g=0) : orientedFlow r g=0 := by
  apply (orientedFlow_eq_zero_iff r g).mpr
  have hq := (orientedFlow_eq_zero_iff q g).mp hz
  by_contra hr
  exact (Finsupp.mem_support_iff.mp (hs (Finsupp.mem_support_iff.mpr hr))) hq

private theorem sum_pair_of_zero (f : Fin 3 → ℤ) (i o : Fin 3) (hio : i≠o)
    (hz : ∀ k,k≠i → k≠o → f k=0) : ∑ k,f k=f i+f o := by
  have h : (∑ k∈({i,o} : Finset (Fin 3)),f k)=∑ k,f k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    exact hz k hk.1 hk.2
  simpa [hio] using h.symm

namespace ClosedNetwork
variable (C : ClosedNetwork M) (v : C.sites) (r : Edge M →₀ ℤ)
  (hr : Conserved r) (hs : r.support⊆(C.polygon v).val)
include hr hs

omit hr in
private theorem other_zero (u : C.sites) (hu : C.next.SameCycle v u) (k : Fin 3)
    (hi : k≠C.enter u) (ho : k≠C.exit u) : orientedFlow r (u.val,k)=0 := by
  apply flow_support_mono_zero r (C.componentFlow (C.polygon v))
    (by rw [C.componentFlow_support _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)]; exact hs)
  rw [C.component_oriented_at v u hu]
  simp [hi,ho]

private theorem balance (u : C.sites) (hu : C.next.SameCycle v u) :
    orientedFlow r (u.val,C.enter u)+orientedFlow r (u.val,C.exit u)=0 := by
  rw [← sum_pair_of_zero _ _ _ (C.distinct u) (C.other_zero v r hs u hu)]
  exact hr.sum_zero u.val

private theorem enter_next_value (u : C.sites) (hu : C.next.SameCycle v u) :
    orientedFlow r ((C.next u).val,C.enter (C.next u))=orientedFlow r (u.val,C.enter u) := by
  rw [C.matching,← C.incident]
  change orientedFlow r (reverseGerm (u.val,C.exit u))=_
  rw [orientedFlow_reverse]
  have h:=C.balance v r hr hs u hu
  omega

private theorem enter_iterate (j : ℕ) :
    orientedFlow r ((C.next^[j] v).val,C.enter (C.next^[j] v))=orientedFlow r (v.val,C.enter v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rw [C.enter_next_value v r hr hs]
    · exact ih
    · refine ⟨(j : ℤ),?_⟩; simp only [zpow_natCast,Equiv.Perm.coe_pow]

private theorem enter_value (u : C.sites) (hu : C.next.SameCycle v u) :
    orientedFlow r (u.val,C.enter u)=orientedFlow r (v.val,C.enter v) := by
  obtain ⟨j,_,hj⟩:=hu.exists_pow_eq'
  have h:=C.enter_iterate v r hr hs j
  simpa only [← Equiv.Perm.coe_pow,hj] using h

 

theorem current_on_cycle : r=
    (-orientedFlow r (v.val,C.enter v)) • C.componentFlow (C.polygon v) := by
  apply orientedFlow_injective
  ext g
  rcases g with ⟨x,k⟩
  by_cases hx : x∈(C.polygon v).vertices
  · let u : C.sites:=⟨x,C.polygon_vertices_subset v hx⟩
    have hu : C.next.SameCycle v u := (C.mem_polygon_vertices v u).mp hx
    have he := C.enter_value v r hr hs u hu
    have hb := C.balance v r hr hs u hu
    rw [map_zsmul,Finsupp.smul_apply,smul_eq_mul,C.component_oriented_at v u hu]
    change orientedFlow r (u.val,k)=_
    by_cases hi : k=C.enter u
    · subst k
      simp only [ite_eq_right (C.distinct u),ite_true,zero_sub,mul_neg,neg_neg,mul_one]
      exact he
    · by_cases ho : k=C.exit u
      · subst k
        simp only [ite_true,ite_eq_right hi,sub_zero,mul_one]
        omega
      · rw [C.other_zero v r hs u hu k hi ho]
        simp [hi,ho]
  · have hz:=flow_zero_outside_vertices r (C.polygon v) hs x hx k
    have hq:=flow_zero_outside_vertices (C.componentFlow (C.polygon v)) (C.polygon v)
      (by rw [C.componentFlow_support _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)]) x hx k
    rw [hz,map_zsmul,Finsupp.smul_apply,hq,smul_zero]

end ClosedNetwork

end PolynomialVacuumCylinder

end OAI
