import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAbelianizedDimension

namespace OAI

/-! # Finite virtual dimension above an abelian quotient

Only the kernel's actual integral cohomological dimension is used. The
kernel may be infinitely generated.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G Q : Type} [Group G] [Group Q] [Group.FG Q]
  [IsMulCommutative Q] [Group.IsSolvable G]

theorem abelian_quotient_virtual_finite_dimension (f : G →* Q)
    (hf : Function.Surjective f) (hker : HasFiniteIntegralCohomologicalDimension f.ker) :
    ∃ P : Subgroup G, P.FiniteIndex ∧ Group.IsSolvable P ∧
      HasFiniteIntegralCohomologicalDimension P := by
  obtain ⟨d, hd⟩ := hker
  let := hd
  obtain ⟨U, hU, htfU⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent Q).exists_torsionFree_finiteIndex
  let := hU
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htfU
  let P := U.comap f
  let : P.FiniteIndex := inferInstance
  let p : P →* U := (f.comp P.subtype).codRestrict U (fun x => x.property)
  have hp : Function.Surjective p := by
    intro u
    obtain ⟨g, hg⟩ := hf (u : Q)
    have hgP : g ∈ P := by change f g ∈ U; rw [hg]; exact u.property
    exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩
  let q := e.symm.toMonoidHom.comp p
  have hq : Function.Surjective q := e.symm.surjective.comp hp
  have hk (a : q.ker) : ((a : P) : G) ∈ f.ker := by
    have ha : q (a : P) = 1 := a.property
    have hpa : p (a : P) = 1 := e.symm.injective (ha.trans e.symm.map_one.symm)
    exact congrArg (fun u : U => (u : Q)) hpa
  let k : q.ker →* f.ker := (P.subtype.comp q.ker.subtype).codRestrict f.ker hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : f.ker => (x : G)) hab
  let := cohomologicalDimension_le_of_injective k hki d
  let := cohomologicalDimension_le_of_lattice_quotient r q hq d
  exact ⟨P, inferInstance, inferInstance, d + r, inferInstance⟩

end PolycyclicRecognition

end

end OAI
