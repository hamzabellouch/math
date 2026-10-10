import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyBoundTransport
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeKernelTail
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareHomologyDimension

namespace OAI

/-! # Homology dimension through a free abelian quotient

The explicit cyclic mapping cone is iterated over the quotient coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

theorem homology_bound_of_lattice_quotient (r : ℕ) {G : Type} [Group G]
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hN : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i)) :
    ∀ A : Rep ℤ G, ∀ i, d + r < i → IsZero (groupHomology A i) := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    have e : q.ker ≃* G := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    simpa only [Nat.add_zero] using homology_bound_of_equiv e d hN
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    have htail : ∀ B : Rep ℤ (latticeKernelTail q).ker, ∀ i,
        d < i → IsZero (groupHomology B i) :=
      homology_bound_of_equiv (latticeKernelTailEquiv q) d hN
    have hK := ih (latticeKernelTail q) (latticeKernelTail_surjective q hq) htail
    simpa only [Nat.add_assoc, Nat.add_comm r 1] using
      homology_bound_of_integer_quotient p t hpt (d + r) hK

theorem IsIntegralPoincareDualityGroup.dimension_le_of_lattice_quotient
    {G : Type} [Group G] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n)
    (r : ℕ) (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hN : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i)) : n ≤ d + r :=
  hG.homologicalDimension_le (d + r) (homology_bound_of_lattice_quotient r q hq d hN)

end PolycyclicRecognition

end

end OAI
