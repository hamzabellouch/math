import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableFiniteExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeAbelianRank

namespace OAI

/-! # A finite-kernel abelian quotient has a finite-index integral lattice -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {H Q : Type} [Group H] [Group Q] [Group.FG Q] [IsMulCommutative Q]
  [Group.IsSolvable H]

theorem finite_kernel_abelian_quotient_lattice (f : H →* Q)
    (hf : Function.Surjective f) [Finite f.ker] :
    ∃ U : Subgroup H, U.FiniteIndex ∧ ∃ r : ℕ, Nonempty (IntegralLatticeGroup r ≃* U) := by
  have hQ : IsPolycyclic (H ⧸ f.ker) :=
    (isPolycyclic_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf)).mpr
      (isPolycyclic_of_finitelyGenerated_nilpotent Q)
  have hH : IsPolycyclic H :=
    isPolycyclic_of_normal_subgroup f.ker isPolycyclic_of_finite_solvable hQ
  obtain ⟨U, hUi, htf⟩ := hH.exists_torsionFree_finiteIndex
  let g := f.comp U.subtype
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 1
    let k : f.ker := ⟨(u : H), hu⟩
    have hp : u ^ Nat.card f.ker = 1 := by
      apply Subtype.ext
      exact congrArg (fun x : f.ker => (x : H)) (pow_card_eq_one' (x := k))
    exact htf u (Nat.card f.ker) (Nat.ne_of_gt Nat.card_pos) hp
  let : IsMulCommutative U := ⟨⟨fun a b => hg (by simp only [map_mul, mul_comm])⟩⟩
  let : Group.FG U := hH.finitelyGenerated |> fun h => by
    let := h
    let := hUi
    infer_instance
  obtain ⟨r, e⟩ := exists_integralLattice_equiv (A := U) htf
  exact ⟨U, hUi, r, e⟩

end PolycyclicRecognition

end

end OAI
