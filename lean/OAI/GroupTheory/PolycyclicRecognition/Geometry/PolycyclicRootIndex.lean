import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexNormalExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Polycyclic

namespace OAI

/-! # Full root subgroups have finite index in a polycyclic group -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type*} [Group G]

theorem finiteIndex_of_cyclic_roots [IsCyclic G] (H : Subgroup G)
    (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) : H.FiniteIndex := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  obtain ⟨n, hn, hgn⟩ := hH g
  have hZ : (Subgroup.zpowers (g ^ (n : ℤ))).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_zpowers_zpow hg]
    exact ne_of_gt (Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast ne_of_gt hn))
  let := hZ
  apply Subgroup.finiteIndex_of_le (H := Subgroup.zpowers (g ^ (n : ℤ)))
  exact Subgroup.zpowers_le.mpr (by simpa only [zpow_natCast] using hgn)

theorem finiteIndex_roots_cyclic_extension (N H : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)]
    (hN : ∀ L : Subgroup N, (∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ L) → L.FiniteIndex)
    (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) : H.FiniteIndex := by
  let q := QuotientGroup.mk' N
  have hn : (H.comap N.subtype).FiniteIndex := hN _ (by
    intro g
    obtain ⟨n, hn, hg⟩ := hH g
    exact ⟨n, hn, hg⟩)
  have hq : (H.map q).FiniteIndex := finiteIndex_of_cyclic_roots _ (by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨n, hn, hg⟩ := hH g
    exact ⟨n, hn, ⟨g ^ n, hg, by rw [map_pow]⟩⟩)
  let := hn
  let := hq
  exact finiteIndex_of_normal_extension N H

theorem IsPolycyclic.finiteIndex_of_roots (hG : IsPolycyclic G) (H : Subgroup G)
    (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) : H.FiniteIndex := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have hi (i : ℕ) (hi : i ≤ n) : ∀ L : Subgroup (c.group i),
      (∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ L) → L.FiniteIndex := by
    induction i with
    | zero =>
      rw [c.first]
      intro L _
      infer_instance
    | succ i ih =>
      let s := c.step i (by omega)
      let N := (c.group i).subgroupOf (c.group (i + 1))
      let := s.normal
      let := s.cyclic
      intro L hL
      apply finiteIndex_roots_cyclic_extension N L _ hL
      intro A hA
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      have hAi : (A.comap e.toMonoidHom).FiniteIndex := ih (by omega) _ (by
        intro g
        obtain ⟨k, hk, hg⟩ := hA (e g)
        refine ⟨k, hk, ?_⟩
        change e (g ^ k) ∈ A
        rw [map_pow]
        exact hg)
      refine ⟨?_⟩
      rw [← A.index_comap_of_surjective (f := e.toMonoidHom) e.surjective]
      exact hAi.index_ne_zero
  have ht := hi n le_rfl
  rw [c.last] at ht
  let e := Subgroup.topEquiv (G := G)
  have htop : (H.comap e.toMonoidHom).FiniteIndex := ht _ (by
    intro g
    obtain ⟨k, hk, hg⟩ := hH (e g)
    exact ⟨k, hk, hg⟩)
  refine ⟨?_⟩
  rw [← H.index_comap_of_surjective (f := e.toMonoidHom) e.surjective]
  exact htop.index_ne_zero

end PolycyclicRecognition

end

end OAI
