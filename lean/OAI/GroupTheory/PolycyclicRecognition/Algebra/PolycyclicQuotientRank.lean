import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolyZDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FreeAbelianDuality

namespace OAI

/-! # Lattice quotients of polycyclic groups

The already proved finite-index duality transfer gives duality for a
polycyclic group of finite integral cohomological dimension. Splitting off
the coordinates of a lattice quotient then bounds its rank by that dimension.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem IsPolycyclic.exists_poincareDuality_of_finiteDimension
    (hG : IsPolycyclic G) (hcd : HasFiniteIntegralCohomologicalDimension G) :
    ∃ n, IsIntegralPoincareDualityGroup G n := by
  let : Group.FG G := hG.finitelyGenerated
  obtain ⟨H, hH, n, hn⟩ := hG.exists_poincareDuality_finiteIndex
  let := hH
  let : Group.FG H := hn.1.fg
  exact ⟨n, liDualityInput H G (finiteIndexCoarseEquivalence H)
    (hn.finiteCohomologicalDimension H) hcd n hn⟩

theorem IsPolycyclic.poincareDuality_dimension_ge_lattice_quotient
    (hG : IsPolycyclic G) (hcd : HasFiniteIntegralCohomologicalDimension G)
    (n : ℕ) (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q) :
    ∃ m, IsIntegralPoincareDualityGroup G (m + n) := by
  induction n generalizing G with
  | zero =>
    obtain ⟨m, hm⟩ := hG.exists_poincareDuality_of_finiteDimension hcd
    exact ⟨m, by simpa using hm⟩
  | succ n ih =>
    let q₁ : G →* Multiplicative ℤ := (latticeCoordinate n).comp q
    let qK : q₁.ker →* (latticeCoordinate n).ker :=
      { toFun := fun x => ⟨q x, x.property⟩
        map_one' := Subtype.ext q.map_one
        map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
    have hqK : Function.Surjective qK := by
      intro y
      obtain ⟨x, hx⟩ := hq y
      have hxK : x ∈ q₁.ker := by
        change latticeCoordinate n (q x) = 1
        rw [hx]
        exact y.property
      exact ⟨⟨x, hxK⟩, Subtype.ext hx⟩
    obtain ⟨m, hm⟩ := ih
      (hG.of_injective q₁.ker.subtype Subtype.val_injective)
      (hcd.subgroup q₁.ker)
      ((latticeCoordinateKernel n).toMonoidHom.comp qK)
      ((latticeCoordinateKernel n).surjective.comp hqK)
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection n)
    have ht₁ : q₁ t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate n (q t) = _
      rw [ht, latticeCoordinate_section]
    exact ⟨m, by simpa only [Nat.add_assoc] using
      poincareDuality_of_integerQuotient q₁ t ht₁ hm⟩

theorem IsPolycyclic.lattice_quotient_rank_le
    (hG : IsPolycyclic G) (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (n : ℕ) (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q) : n ≤ d := by
  obtain ⟨m, hm⟩ := hG.poincareDuality_dimension_ge_lattice_quotient ⟨d, inferInstance⟩ n q hq
  have hmd : m + n ≤ d := hm.dimension_le
  omega

end PolycyclicRecognition

end

end OAI
