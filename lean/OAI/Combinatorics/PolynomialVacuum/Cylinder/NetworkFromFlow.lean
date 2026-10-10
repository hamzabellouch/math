import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkCycles

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

@[simp] theorem edgeOf_reverse (g : Germ M) : edgeOf (reverseGerm g)=edgeOf g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf,reverseGerm,neighbor]

@[simp] theorem dartSign_reverse (g : Germ M) : dartSign (reverseGerm g) = -dartSign g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [dartSign,reverseGerm,neighbor]

@[simp] theorem orientedFlow_reverse (q : Edge M →₀ ℤ) (g : Germ M) :
    orientedFlow q (reverseGerm g) = -orientedFlow q g := by
  simp [orientedFlow_eq]

 

def LocalIce (q : Edge M →₀ ℤ) (v : Vertex M) : Prop :=
  (∀ k,orientedFlow q (v,k)=0) ∨
  ∃ i o : Fin 3,i≠o ∧ ∀ k,orientedFlow q (v,k)=
    (if k=o then 1 else 0)-(if k=i then 1 else 0)

noncomputable def activeSites (q : Edge M →₀ ℤ) : Finset (Vertex M) :=
  (orientedFlow q).support.image Prod.fst

theorem mem_activeSites (q : Edge M →₀ ℤ) (v : Vertex M) :
    v∈activeSites q ↔ ∃ k,orientedFlow q (v,k)≠0 := by
  simp only [activeSites,Finset.mem_image,Finsupp.mem_support_iff]
  constructor
  · rintro ⟨⟨u,k⟩,hk,rfl⟩; exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩; exact ⟨(v,k),hk,rfl⟩

namespace IceNetwork
variable (q : Edge M →₀ ℤ) (hq : ∀ v,LocalIce q v)
include hq

theorem occupied (v : activeSites q) : ∃ i o : Fin 3,i≠o ∧ ∀ k,
    orientedFlow q (v.val,k)=(if k=o then 1 else 0)-(if k=i then 1 else 0) := by
  rcases hq v.val with hzero | h
  · obtain ⟨k,hk⟩:=(mem_activeSites q v.val).mp v.property
    exact (hk (hzero k)).elim
  · exact h

noncomputable def enter (v : activeSites q) : Fin 3 := (occupied q hq v).choose
noncomputable def exit (v : activeSites q) : Fin 3 := (occupied q hq v).choose_spec.choose

theorem distinct (v : activeSites q) : enter q hq v≠exit q hq v :=
  (occupied q hq v).choose_spec.choose_spec.1

theorem at_slot (v : activeSites q) (k : Fin 3) :
    orientedFlow q (v.val,k)=(if k=exit q hq v then 1 else 0)-(if k=enter q hq v then 1 else 0) :=
  (occupied q hq v).choose_spec.choose_spec.2 k

theorem at_enter (v : activeSites q) : orientedFlow q (v.val,enter q hq v)= -1 := by
  rw [at_slot q hq]; simp [distinct q hq v]
theorem at_exit (v : activeSites q) : orientedFlow q (v.val,exit q hq v)=1 := by
  rw [at_slot q hq]; simp [Ne.symm (distinct q hq v)]

theorem enter_of_neg (v : activeSites q) (k : Fin 3) (h : orientedFlow q (v.val,k)= -1) :
    enter q hq v=k := by
  rw [at_slot q hq] at h
  split_ifs at h <;> omega

theorem exit_of_pos (v : activeSites q) (k : Fin 3) (h : orientedFlow q (v.val,k)=1) :
    exit q hq v=k := by
  rw [at_slot q hq] at h
  split_ifs at h <;> omega

noncomputable def next (v : activeSites q) : activeSites q :=
  ⟨neighbor v.val (exit q hq v),(mem_activeSites q _).mpr ⟨exit q hq v,by
    have h:=orientedFlow_reverse q (v.val,exit q hq v)
    rw [at_exit] at h
    exact h ▸ (by norm_num)⟩⟩

noncomputable def prev (v : activeSites q) : activeSites q :=
  ⟨neighbor v.val (enter q hq v),(mem_activeSites q _).mpr ⟨enter q hq v,by
    have h:=orientedFlow_reverse q (v.val,enter q hq v)
    rw [at_enter] at h
    exact h ▸ (by norm_num)⟩⟩

theorem enter_next (v : activeSites q) : enter q hq (next q hq v)=exit q hq v := by
  apply enter_of_neg
  change orientedFlow q (reverseGerm (v.val,exit q hq v))= -1
  rw [orientedFlow_reverse,at_exit]

theorem exit_prev (v : activeSites q) : exit q hq (prev q hq v)=enter q hq v := by
  apply exit_of_pos
  change orientedFlow q (reverseGerm (v.val,enter q hq v))=1
  rw [orientedFlow_reverse,at_enter]; norm_num

@[simp] theorem prev_next (v : activeSites q) : prev q hq (next q hq v)=v := by
  apply Subtype.ext
  change neighbor (neighbor v.val (exit q hq v)) (enter q hq (next q hq v))=v.val
  rw [enter_next,neighbor_neighbor]

@[simp] theorem next_prev (v : activeSites q) : next q hq (prev q hq v)=v := by
  apply Subtype.ext
  change neighbor (neighbor v.val (enter q hq v)) (exit q hq (prev q hq v))=v.val
  rw [exit_prev,neighbor_neighbor]

noncomputable def permutation : Equiv.Perm (activeSites q) :=
  ⟨next q hq,prev q hq,prev_next q hq,next_prev q hq⟩

noncomputable def network : ClosedNetwork M where
  sites := activeSites q
  enter := enter q hq
  exit := exit q hq
  distinct := distinct q hq
  next := permutation q hq
  incident := fun _ => rfl
  matching := enter_next q hq

end IceNetwork
end PolynomialVacuumCylinder

end OAI
