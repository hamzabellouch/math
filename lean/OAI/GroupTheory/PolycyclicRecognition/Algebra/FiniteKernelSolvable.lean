import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OAI

/-! # Removing a finite normal kernel from virtual solvability

This is the elementary centralizer step used in §2 of
Kropholler–Martínez-Pérez–Nucinkis (2009). It does not assume any finiteness
theorem for elementary amenable groups.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

theorem conjugation_ker_eq_centralizer :
    (MulAut.conjNormal : G →* MulAut N).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  constructor
  · intro hg n hn
    have he := congrArg (fun a : MulAut N => (a ⟨n, hn⟩ : G)) hg
    change g * n * g⁻¹ = n at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = (n : G)
    rw [← hg n n.property, mul_inv_cancel_right]

theorem finiteIndex_centralizer_of_finite_normal [Finite N] :
    (Subgroup.centralizer (N : Set G)).FiniteIndex := by
  rw [← conjugation_ker_eq_centralizer N]
  infer_instance

/-- If the quotient by a finite normal subgroup is virtually solvable, the
ambient group is virtually solvable. Intersect the lifted solvable subgroup
with the centralizer of the finite kernel; its new kernel is abelian. -/
theorem exists_finiteIndex_solvable_of_finite_kernel [Finite N]
    (hQ : ∃ V : Subgroup (G ⧸ N), V.FiniteIndex ∧ Group.IsSolvable V) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  obtain ⟨V, hV, hVs⟩ := hQ
  let :=  hV
  let :=  hVs
  let π := QuotientGroup.mk' N
  let P := V.comap π
  let C := Subgroup.centralizer (N : Set G)
  let : C.FiniteIndex := finiteIndex_centralizer_of_finite_normal N
  let H := P ⊓ C
  let q : H →* V := (π.comp H.subtype).codRestrict V (fun x => x.property.1)
  have hkN (a : q.ker) : (((a : H) : G)) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    have ha := congrArg (fun v : V => (v : G ⧸ N)) a.property
    exact ha
  let : Group.IsSolvable q.ker := Group.isSolvable_of_comm (fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    exact ((a : H).property.2 _ (hkN b)).symm)
  have hs : Group.IsSolvable H :=
    Group.isSolvable_of_ker_le_range q.ker.subtype q (by simp)
  exact ⟨H, inferInstance, hs⟩

end PolycyclicRecognition

end

end OAI
