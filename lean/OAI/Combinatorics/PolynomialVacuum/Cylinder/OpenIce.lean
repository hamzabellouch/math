import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenNetwork

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

noncomputable def activeInside (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) : Finset (Vertex M) :=
  activeSites q ∩ D

namespace OpenIce
variable (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) (hq : ∀v∈D,LocalIce q v)
include hq

theorem occupied (v : activeInside D q) : ∃i o : Fin 3,i≠o ∧ ∀k,orientedFlow q (v.val,k)=
    (if k=o then 1 else 0)-(if k=i then 1 else 0) := by
  have hv := Finset.mem_inter.mp v.property
  rcases hq v.val hv.2 with hz | hp
  · obtain ⟨k,hk⟩:=(mem_activeSites q v.val).mp hv.1
    exact (hk (hz k)).elim
  · exact hp

noncomputable def enter (v : activeInside D q) : Fin 3 := (occupied D q hq v).choose
noncomputable def exit (v : activeInside D q) : Fin 3 := (occupied D q hq v).choose_spec.choose

theorem distinct (v : activeInside D q) : enter D q hq v≠exit D q hq v :=
  (occupied D q hq v).choose_spec.choose_spec.1

theorem at_slot (v : activeInside D q) (k : Fin 3) :
    orientedFlow q (v.val,k)=(if k=exit D q hq v then 1 else 0)-(if k=enter D q hq v then 1 else 0) :=
  (occupied D q hq v).choose_spec.choose_spec.2 k

theorem at_enter (v : activeInside D q) : orientedFlow q (v.val,enter D q hq v)= -1 := by
  rw [at_slot D q hq]; simp [distinct D q hq v]
theorem at_exit (v : activeInside D q) : orientedFlow q (v.val,exit D q hq v)=1 := by
  rw [at_slot D q hq]; simp [Ne.symm (distinct D q hq v)]

theorem matching (v w : activeInside D q)
    (h : neighbor v.val (exit D q hq v)=w.val) : enter D q hq w=exit D q hq v := by
  have hh := orientedFlow_reverse q (v.val,exit D q hq v)
  rw [at_exit D q hq] at hh
  change orientedFlow q (neighbor v.val (exit D q hq v),exit D q hq v)= -1 at hh
  rw [h,at_slot D q hq] at hh
  split_ifs at hh <;> omega

noncomputable def network : OpenNetwork M where
  sites:=activeInside D q
  enter:=enter D q hq
  exit:=exit D q hq
  distinct:=distinct D q hq
  matching:=matching D q hq

 

theorem exit_outside_domain (v : activeInside D q)
    (h : neighbor v.val (exit D q hq v)∉activeInside D q) :
    neighbor v.val (exit D q hq v)∉D := by
  intro hd
  apply h
  apply Finset.mem_inter.mpr ⟨?_,hd⟩
  apply (mem_activeSites q _).mpr
  refine ⟨exit D q hq v,?_⟩
  have hh:=orientedFlow_reverse q (v.val,exit D q hq v)
  rw [at_exit D q hq] at hh
  change orientedFlow q (neighbor v.val (exit D q hq v),exit D q hq v)= -1 at hh
  rw [hh]
  norm_num

theorem enter_outside_domain (v : activeInside D q)
    (h : neighbor v.val (enter D q hq v)∉activeInside D q) :
    neighbor v.val (enter D q hq v)∉D := by
  intro hd
  apply h
  apply Finset.mem_inter.mpr ⟨?_,hd⟩
  apply (mem_activeSites q _).mpr
  refine ⟨enter D q hq v,?_⟩
  have hh:=orientedFlow_reverse q (v.val,enter D q hq v)
  rw [at_enter D q hq] at hh
  change orientedFlow q (neighbor v.val (enter D q hq v),enter D q hq v)=1 at hh
  rw [hh]
  norm_num
end OpenIce
end PolynomialVacuumCylinder

end OAI
