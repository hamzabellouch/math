import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
namespace ClosedNetwork
variable {M : ℕ} (C : ClosedNetwork M)

theorem polygon_eq_iff (v u : C.sites) : C.polygon v=C.polygon u ↔ C.next.SameCycle v u := by
  constructor
  · intro he
    apply (C.mem_polygon_vertices v u).mp
    rw [he]
    exact (C.mem_polygon_vertices u u).mpr (Equiv.Perm.SameCycle.refl _ _)
  · exact C.polygon_eq_of_sameCycle v u

noncomputable def cycleSites (v : C.sites) : Finset C.sites :=
  Finset.univ.filter (fun u => C.polygon u=C.polygon v)

theorem mem_cycleSites (v u : C.sites) : u∈C.cycleSites v ↔ C.next.SameCycle v u := by
  simp only [cycleSites,Finset.mem_filter,Finset.mem_univ,true_and,C.polygon_eq_iff]
  exact ⟨fun h => h.symm,fun h => h.symm⟩

theorem cycleSites_eq_orbit (v : C.sites) :
    C.cycleSites v=(Finset.range (C.period v)).image (fun j => C.next^[j] v) := by
  ext u
  rw [C.mem_cycleSites]
  constructor
  · intro h
    obtain ⟨j,_,hj⟩:=h.exists_pow_eq'
    refine Finset.mem_image.mpr ⟨j%C.period v,by simpa using Nat.mod_lt j (C.period_pos v),?_⟩
    rw [show C.period v=Function.minimalPeriod C.next v from rfl,Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using hj
  · intro hu
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hu
    refine ⟨(j : ℤ),?_⟩
    simp only [zpow_natCast,Equiv.Perm.coe_pow]

noncomputable def componentFlow (P : Polygon M) : Edge M →₀ ℤ :=
  ∑ u∈Finset.univ.filter (fun u : C.sites => C.polygon u=P),dartFlow (u.val,C.exit u)

theorem componentFlow_word (v : C.sites) : C.componentFlow (C.polygon v)=
    wordFlow (C.germ v) (C.word (C.period v) v) := by
  change (∑ u∈C.cycleSites v,dartFlow (u.val,C.exit u))=_
  rw [C.cycleSites_eq_orbit,Finset.sum_image,C.word_flow]
  intro i hi j hj he
  exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) he

theorem flow_sum_components : C.flow=∑ P∈C.polygons,C.componentFlow P := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun u _ => Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)
    (fun u : C.sites => dartFlow (u.val,C.exit u))

theorem componentFlow_support (P : Polygon M) (hP : P∈C.polygons) :
    (C.componentFlow P).support=P.val := by
  obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hP
  rw [C.componentFlow_word,simple_word_support _ _ (C.orbit_nodup v) (C.orbit_terminal v)]
  rfl

end ClosedNetwork
end PolynomialVacuumCylinder

end OAI
