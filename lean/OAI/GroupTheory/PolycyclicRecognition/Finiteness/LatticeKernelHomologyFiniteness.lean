import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicKernelHomologyFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LatticeExtensionHomologyBound

namespace OAI

/-! # Descending top-homology finiteness through a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem lattice_topHomology_finiteness (r : ℕ) {G : Type} [Group G]
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i))
    (A : Rep ℤ G)
    (htorsion : ∀ (z : ℤ) (x : groupHomology (Rep.res q.ker.subtype A) d),
      z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : groupHomology (Rep.res q.ker.subtype A) d,
      x ≠ 0 → y ≠ 0 → ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) :
    (∀ (z : ℤ) (x : groupHomology A (d + r)), z • x = 0 → z = 0 ∨ x = 0) ∧
    (∀ x y : groupHomology A (d + r), x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) ∧
    (∀ x : groupHomology A (d + r), x ≠ 0 → Module.Finite ℤ (groupHomology A (d + r)) →
      Module.Finite ℤ (groupHomology (Rep.res q.ker.subtype A) d)) := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    let f : q.ker ≃* G := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    let E := groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := A)
      f (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    have hi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    obtain ⟨ht, hc⟩ := integralRankOne_properties_of_injective E.inv hi htorsion hcomm
    refine ⟨ht, hc, ?_⟩
    intro x hx hfinite
    let := hfinite
    exact Module.Finite.equiv E.symm.toLinearEquiv
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    let q' := latticeKernelTail q
    let A' := Rep.res p.ker.subtype A
    let B := Rep.res q'.ker.subtype A'
    let E : groupHomology (Rep.res q.ker.subtype A) d ≅ groupHomology B d :=
      groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := B)
        (latticeKernelTailEquiv q) (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    have hi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    obtain ⟨htB, hcB⟩ := integralRankOne_properties_of_injective E.inv hi htorsion hcomm
    have hbB : ∀ B : Rep ℤ q'.ker, ∀ i, d < i → IsZero (groupHomology B i) :=
      homology_bound_of_equiv (latticeKernelTailEquiv q) d hbound
    obtain ⟨htK, hcK, hfiniteK⟩ := ih q' (latticeKernelTail_surjective q hq) hbB A' htB hcB
    have hvanish : IsZero (groupHomology A' (d + r + 1)) :=
      homology_bound_of_lattice_quotient r q' (latticeKernelTail_surjective q hq) d hbB
        A' (d + r + 1) (by omega)
    let P := Rep.standardResolution ℤ p.ker
    let j := cyclicTopHomologyInjection p t hpt P A (d + r) hvanish
    have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
    obtain ⟨htG, hcG⟩ := integralRankOne_properties_of_injective j hj htK hcK
    have hdeg : d + (r + 1) = d + r + 1 := by omega
    rw [hdeg]
    refine ⟨htG, hcG, ?_⟩
    intro x hx hfinite
    let := hfinite
    have hKfinite := cyclic_topHomology_finiteness p t hpt P A (d + r) hvanish htK hcK x hx
    have hy : j x ≠ 0 := fun h => hx (hj (h.trans (map_zero j.hom).symm))
    have hBfinite : Module.Finite ℤ (groupHomology B d) := hfiniteK (j x) hy hKfinite
    let := hBfinite
    exact Module.Finite.equiv E.symm.toLinearEquiv

end PolycyclicRecognition

end

end OAI
