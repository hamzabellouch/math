import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkFromFlow
import OAI.Combinatorics.PolynomialVacuum.Bridge.FiniteOpenPath

namespace OAI

namespace PolynomialVacuumCylinder
open Classical

 

structure OpenNetwork (M : ℕ) where
  sites : Finset (Vertex M)
  enter : sites → Fin 3
  exit : sites → Fin 3
  distinct : ∀ v,enter v≠exit v
  matching : ∀ v w,neighbor v.val (exit v)=w.val → enter w=exit v

namespace OpenNetwork
variable {M : ℕ} (C : OpenNetwork M)

noncomputable def next (v : C.sites) : Option C.sites :=
  if h : neighbor v.val (C.exit v)∈C.sites then some ⟨neighbor v.val (C.exit v),h⟩ else none

theorem next_some (v w : C.sites) : C.next v=some w ↔ neighbor v.val (C.exit v)=w.val := by
  unfold next
  split_ifs with h
  · simp only [Option.some.injEq,Subtype.ext_iff]
  · constructor
    · simp
    · intro hh
      exact (h (hh ▸ w.property)).elim

theorem next_none (v : C.sites) : C.next v=none ↔ neighbor v.val (C.exit v)∉C.sites := by
  unfold next
  split_ifs <;> simp_all

theorem next_injective (u v w : C.sites) (hu : C.next u=some w) (hv : C.next v=some w) : u=v := by
  have heu := (C.next_some u w).mp hu
  have hev := (C.next_some v w).mp hv
  have hmu := C.matching u w heu
  have hmv := C.matching v w hev
  apply Subtype.ext
  calc
    u.val=neighbor w.val (C.enter w) := by rw [hmu,← heu,neighbor_neighbor]
    _=v.val := by rw [hmv,← hev,neighbor_neighbor]

def Source (a : C.sites) : Prop := neighbor a.val (C.enter a)∉C.sites

theorem source_no_predecessor (a : C.sites) (ha : C.Source a) (u : C.sites) : C.next u≠some a := by
  intro h
  have he := (C.next_some u a).mp h
  have hm := C.matching u a he
  apply ha
  rw [hm,← he,neighbor_neighbor]
  exact u.property

noncomputable def pathLength (a : C.sites) (ha : C.Source a) : ℕ :=
  PolynomialVacuumOpenPath.exitTime C.next C.next_injective a (C.source_no_predecessor a ha)
noncomputable def pathSite (a : C.sites) (ha : C.Source a) : Fin (C.pathLength a ha) → C.sites :=
  PolynomialVacuumOpenPath.pathAt C.next C.next_injective a (C.source_no_predecessor a ha)

theorem pathLength_pos (a : C.sites) (ha : C.Source a) : 0<C.pathLength a ha :=
  PolynomialVacuumOpenPath.exitTime_pos _ _ _ _

theorem pathSite_injective (a : C.sites) (ha : C.Source a) : Function.Injective (C.pathSite a ha) :=
  PolynomialVacuumOpenPath.pathAt_injective _ _ _ _

theorem pathSite_start (a : C.sites) (ha : C.Source a) :
    C.pathSite a ha ⟨0,C.pathLength_pos a ha⟩=a :=
  PolynomialVacuumOpenPath.pathAt_start _ _ _ _

theorem pathSite_next (a : C.sites) (ha : C.Source a) (i j : Fin (C.pathLength a ha))
    (hij : j.val=i.val+1) : neighbor (C.pathSite a ha i).val (C.exit (C.pathSite a ha i))=
      (C.pathSite a ha j).val :=
  (C.next_some _ _).mp (PolynomialVacuumOpenPath.pathAt_next _ _ _ _ i j hij)

theorem pathSite_exit (a : C.sites) (ha : C.Source a) (i : Fin (C.pathLength a ha))
    (hi : i.val+1=C.pathLength a ha) :
    neighbor (C.pathSite a ha i).val (C.exit (C.pathSite a ha i))∉C.sites :=
  (C.next_none _).mp (PolynomialVacuumOpenPath.pathAt_exit _ _ _ _ i hi)
end OpenNetwork

end PolynomialVacuumCylinder

end OAI
