import Mathlib.GroupTheory.IsPerfect

namespace OAI

/-! Normal subgroup intersections retaining a perfect image, and their least preimage. -/

namespace FiniteLattice

variable {M H : Type*} [Group M] [Group H]

/-- Two normal subgroups whose images contain a perfect subgroup retain it in their intersection. -/
theorem perfect_le_map_inf (f : M →* H) (P : Subgroup H) [Group.IsPerfect P]
    (B C : Subgroup M) [B.Normal] [C.Normal]
    (hB : P ≤ B.map f) (hC : P ≤ C.map f) : P ≤ (B ⊓ C).map f := by
  calc
    P = ⁅P, P⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅B.map f, C.map f⁆ := Subgroup.commutator_mono hB hC
    _ = (⁅B, C⁆).map f := (Subgroup.map_commutator B C f).symm
    _ ≤ (B ⊓ C).map f := Subgroup.map_mono (Subgroup.commutator_le_inf B C)

/-- A finite nonempty intersection of normal subgroups retains a prescribed perfect image. -/
theorem perfect_le_map_iInf {ι : Type*} [Finite ι] [Nonempty ι]
    (f : M →* H) (P : Subgroup H) [Group.IsPerfect P]
    (B : ι → Subgroup M) (hN : ∀ i, (B i).Normal)
    (hP : ∀ i, P ≤ (B i).map f) : P ≤ (⨅ i, B i).map f := by
  classical
  let := Fintype.ofFinite ι
  have hrange : P ≤ (⊤ : Subgroup M).map f := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (hP i).trans (Subgroup.map_mono le_top)
  have hs (s : Finset ι) : P ≤ (⨅ i ∈ s, B i).map f := by
    induction s using Finset.induction_on with
    | empty => simpa using hrange
    | @insert i s his ih =>
      rw [Finset.iInf_insert]
      let : (B i).Normal := hN i
      let : (⨅ j ∈ s, B j).Normal :=
        Subgroup.normal_iInf_normal (fun j => Subgroup.normal_iInf_normal (fun _ => hN j))
      exact perfect_le_map_inf f P (B i) (⨅ j ∈ s, B j) (hP i) ih
  simpa using hs Finset.univ

/-- In a finite group, there is a least normal subgroup mapping onto a prescribed perfect normal subgroup. -/
theorem exists_least_normal_perfect_preimage [Finite M]
    (f : M →* H) (P : Subgroup H) [Group.IsPerfect P] [P.Normal]
    (hP : P ≤ f.range) :
    ∃ Q : Subgroup M, Q.Normal ∧ Q.map f = P ∧
      ∀ B : Subgroup M, B.Normal → P ≤ B.map f → Q ≤ B := by
  let S := {B : Subgroup M // B.Normal ∧ P ≤ B.map f}
  have hpre : P ≤ (P.comap f).map f := (Subgroup.map_comap_eq_self hP).ge
  let : Nonempty S := ⟨⟨P.comap f, inferInstance, hpre⟩⟩
  let Q : Subgroup M := ⨅ B : S, B.val
  have hQN : Q.Normal := Subgroup.normal_iInf_normal (fun B : S => B.property.1)
  have hQI : P ≤ Q.map f :=
    perfect_le_map_iInf f P (fun B : S => B.val)
      (fun B => B.property.1) (fun B => B.property.2)
  have hleast (B : Subgroup M) (hBN : B.Normal) (hBP : P ≤ B.map f) : Q ≤ B :=
    iInf_le (fun A : S => A.val) ⟨B, hBN, hBP⟩
  refine ⟨Q, hQN, le_antisymm ?_ hQI, hleast⟩
  exact Subgroup.map_le_iff_le_comap.mpr (hleast (P.comap f) inferInstance hpre)

end FiniteLattice

end OAI
