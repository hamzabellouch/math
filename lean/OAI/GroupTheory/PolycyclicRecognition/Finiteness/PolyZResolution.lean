import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolyZComparison
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.GroupIsoFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicDuality

namespace OAI

/-! # Finite projective resolutions along a torsion-free cyclic series -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

theorem finiteProjectiveResolution_of_torsionFreeCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]
    (hN : HasFiniteProjectiveResolution N)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) : HasFiniteProjectiveResolution G := by
  cases finite_or_infinite (G ⧸ N) with
  | inr h =>
    let := h
    exact finiteProjectiveResolution_of_infiniteCyclicQuotient N hN
  | inl h =>
    let := h
    let := subsingleton_of_finite_torsionFree (G ⧸ N) hQ
    have htop : N = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    subst N
    exact hN.of_equiv Subgroup.topEquiv

theorem IsPolyZ.finiteProjectiveResolution (hG : IsPolyZ G) :
    HasFiniteProjectiveResolution G := by
  obtain ⟨n, c, hc⟩ := hG
  have hm : ∀ i, i ≤ n → HasFiniteProjectiveResolution (c.group i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact finiteProjectiveResolution_of_subsingleton _
    | succ i ih =>
      intro hi
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      exact finiteProjectiveResolution_of_torsionFreeCyclicQuotient
        ((c.group i).subgroupOf (c.group (i + 1)))
        ((ih (by omega)).of_equiv e) (hc i (by omega))
  have htop := hm n le_rfl
  rw [c.last] at htop
  exact htop.of_equiv Subgroup.topEquiv

theorem IsPolycyclic.exists_finiteProjectiveResolution_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ HasFiniteProjectiveResolution H := by
  obtain ⟨H, hi, hz⟩ := hG.exists_polyZ_finiteIndex
  exact ⟨H, hi, hz.finiteProjectiveResolution⟩

end PolycyclicRecognition

end

end OAI
