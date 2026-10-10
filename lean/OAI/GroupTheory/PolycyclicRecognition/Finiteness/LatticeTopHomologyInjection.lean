import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicTopHomologyInjection
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LatticeExtensionHomologyBound

namespace OAI

/-! # Injecting top homology into the kernel of a lattice quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem exists_latticeTopHomologyInjection (r : ℕ) {G : Type} [Group G]
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q) (d : ℕ)
    (hbound : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i))
    (A : Rep ℤ G) :
    ∃ f : groupHomology A (d + r) ⟶ groupHomology (Rep.res q.ker.subtype A) d,
      Function.Injective f := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    let e : q.ker ≃* G := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    let E := groupHomology.mapIso (A := Rep.res q.ker.subtype A) (B := A)
      e (LinearEquiv.refl ℤ A.V) (by intro g; rfl) d
    exact ⟨E.inv, (ModuleCat.mono_iff_injective _).mp inferInstance⟩
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
    have hbB : ∀ B : Rep ℤ q'.ker, ∀ i, d < i → IsZero (groupHomology B i) :=
      homology_bound_of_equiv (latticeKernelTailEquiv q) d hbound
    obtain ⟨f, hf⟩ := ih q' (latticeKernelTail_surjective q hq) hbB A'
    have hv : IsZero (groupHomology A' (d + r + 1)) :=
      homology_bound_of_lattice_quotient r q' (latticeKernelTail_surjective q hq) d hbB
        A' (d + r + 1) (by omega)
    let j := cyclicTopHomologyInjection p t hpt (Rep.standardResolution ℤ p.ker) A (d + r) hv
    have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hE : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
    have hdeg : d + (r + 1) = d + r + 1 := by omega
    rw [hdeg]
    exact ⟨j ≫ f ≫ E.inv, hE.comp (hf.comp hj)⟩

end PolycyclicRecognition

end

end OAI
