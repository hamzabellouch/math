import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianRankDimension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeQuotientDimension

namespace OAI

/-! # Finite-rank torsion-free abelian quotients preserve finite dimension

Exhaust the quotient by finitely generated free abelian subgroups and apply
the explicit cyclic-extension bound to each preimage.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative

variable {G : Type} [Group G] [Countable G]

theorem cohomologicalDimension_le_of_abelian_quotient
    (N : Subgroup G) [N.Normal] [IsMulCommutative (G ⧸ N)] (d r : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral N) d]
    (htf : HasNoNontrivialTorsion (G ⧸ N))
    (hrank : Module.rank ℤ (Additive (G ⧸ N)) ≤ r) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + r + 1) := by
  let : CommGroup (G ⧸ N) := inferInstance
  let : Countable (G ⧸ N) := (QuotientGroup.mk'_surjective N).countable
  obtain ⟨S, hS, hfg, hcover⟩ := exists_fg_subgroup_exhaustion (G := G ⧸ N)
  let π := QuotientGroup.mk' N
  let P (n : ℕ) := (S n).comap π
  have hP : Monotone P := fun _ _ h => Subgroup.comap_mono (hS h)
  have hcoverP (g : G) : ∃ n, g ∈ P n := hcover (π g)
  apply cohomologicalDimension_le_of_exhaustion P hP hcoverP (d + r)
  intro n
  obtain ⟨s, hsr, ⟨e⟩⟩ := abelian_fg_subgroup_lattice_of_rank r hrank htf (S n) (hfg n)
  let f : P n →* S n := (π.comp (P n).subtype).codRestrict (S n) (fun x => x.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change π g ∈ S n
      rw [hg]
      exact x.property
    · apply Subtype.ext
      exact hg
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (x : q.ker) : (((x : P n) : G)) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    have hx : f (x : P n) = 1 := e.symm.injective
      (x.property.trans (map_one e.symm.toMonoidHom).symm)
    exact congrArg (fun y : S n => (y : G ⧸ N)) hx
  let k : q.ker →* N := ((P n).subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let := cohomologicalDimension_le_of_injective k hki d
  let := cohomologicalDimension_le_of_lattice_quotient s q hq d
  exact hasProjectiveDimensionLT_of_ge (trivialIntegral (P n)) (d + s + 1)
    (d + r + 1) (by omega)

end PolycyclicRecognition

end

end OAI
