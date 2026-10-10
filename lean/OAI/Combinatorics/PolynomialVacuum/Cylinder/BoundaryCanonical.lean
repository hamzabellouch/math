import OAI.Combinatorics.PolynomialVacuum.Cylinder.BoundaryUniqueness

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ} {D : Finset (Vertex M)} {q : Edge M →₀ ℤ}
namespace BoundaryDecomposition
variable (B : BoundaryDecomposition D q)

theorem arcs_nodup : B.arcs.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply B.pairwise.imp
  intro A C hd he
  subst C
  exact Finset.disjoint_left.mp hd A.start_mem A.start_mem

theorem arcs_perm (C : BoundaryDecomposition D q) : B.arcs.Perm C.arcs :=
  List.perm_of_nodup_nodup_toFinset_eq B.arcs_nodup C.arcs_nodup (B.arcs_unique C)

 

theorem closed_unique (C : BoundaryDecomposition D q) : B.closed=C.closed := by
  have hs := ((B.arcs_perm C).map BoundaryArc.current).sum_eq
  have he := B.reconstruction.symm.trans C.reconstruction
  rw [hs] at he
  exact add_left_cancel he

 

theorem arcs_empty_of_boundary_zero
    (hz : ∀g : Germ M,g.1∈D → (reverseGerm g).1∉D → orientedFlow q g=0) : B.arcs=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro A hA
  have hh := B.on_arc A hA A.start.1 A.start_mem A.start.2
  have hh' : orientedFlow q A.start= -1 := hh.trans A.current_at_start
  rw [hz A.start A.startInside A.startOutside] at hh'
  omega

include B in
theorem global_ice_of_boundary_zero
    (hz : ∀g : Germ M,g.1∈D → (reverseGerm g).1∉D → orientedFlow q g=0) : ∀v,LocalIce q v := by
  have he := B.reconstruction
  rw [B.arcs_empty_of_boundary_zero hz] at he
  simp only [List.map_nil,List.sum_nil,zero_add] at he
  rw [he]
  exact B.ice
end BoundaryDecomposition
end PolynomialVacuumCylinder

end OAI
