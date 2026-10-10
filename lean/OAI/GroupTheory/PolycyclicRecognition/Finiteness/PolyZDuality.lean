import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolyZResolution
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.GroupIsoDuality

namespace OAI

/-! # Integral duality along a torsion-free cyclic series

The comparison group needed in recognition can be chosen poly-Z.  The
cohomology shift for an infinite cyclic extension proves duality for this
subgroup directly, without assuming the general polycyclic duality theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

theorem poincareDuality_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    {n : ℕ} (hN : IsIntegralPoincareDualityGroup N n) :
    IsIntegralPoincareDualityGroup G (n + 1) := by
  let e : Multiplicative ℤ ≃* G ⧸ N := intCyclicMulEquiv
  let q : G →* Multiplicative ℤ := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hker : q.ker = N := by
    ext g
    change e.symm (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
    rw [← e.symm.map_one, e.symm.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective N (e (Multiplicative.ofAdd 1))
  have hqt : q t = Multiplicative.ofAdd 1 := by
    change e.symm (QuotientGroup.mk' N t) = _
    rw [ht, e.symm_apply_apply]
  exact poincareDuality_of_integerQuotient q t hqt
    (hN.of_equiv (MulEquiv.subgroupCongr hker.symm))

theorem exists_poincareDuality_of_torsionFreeCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]
    {n : ℕ} (hN : IsIntegralPoincareDualityGroup N n)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) :
    ∃ d, IsIntegralPoincareDualityGroup G d := by
  cases finite_or_infinite (G ⧸ N) with
  | inr h =>
    let := h
    exact ⟨n + 1, poincareDuality_of_infiniteCyclicQuotient N hN⟩
  | inl h =>
    let := h
    let := subsingleton_of_finite_torsionFree (G ⧸ N) hQ
    have htop : N = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    subst N
    exact ⟨n, hN.of_equiv Subgroup.topEquiv⟩

theorem IsPolyZ.exists_poincareDuality (hG : IsPolyZ G) :
    ∃ n, IsIntegralPoincareDualityGroup G n := by
  obtain ⟨n, c, hc⟩ := hG
  have hm : ∀ i, i ≤ n → ∃ d, IsIntegralPoincareDualityGroup (c.group i) d := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨0, poincareDuality_zero_of_subsingleton _⟩
    | succ i ih =>
      intro hi
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      obtain ⟨d, hd⟩ := ih (by omega)
      exact exists_poincareDuality_of_torsionFreeCyclicQuotient
        ((c.group i).subgroupOf (c.group (i + 1)))
        (hd.of_equiv e) (hc i (by omega))
  obtain ⟨d, hd⟩ := hm n le_rfl
  rw [c.last] at hd
  exact ⟨d, hd.of_equiv Subgroup.topEquiv⟩

theorem IsPolycyclic.exists_poincareDuality_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ n, IsIntegralPoincareDualityGroup H n := by
  obtain ⟨H, hi, hz⟩ := hG.exists_polyZ_finiteIndex
  exact ⟨H, hi, hz.exists_poincareDuality⟩

end PolycyclicRecognition

end

end OAI
