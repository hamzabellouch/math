import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeCyclicExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Extensions

namespace OAI

/-! # Cyclic series with torsion-free factors

Trivial factors are allowed. Removing them gives the usual poly-Z series.
The predicate records an actual series and is stable under subgroups.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic

variable {G J : Type} [Group G] [Group J]

def TorsionFreeCyclicFactors {H K : Subgroup G} {n : ℕ} (c : CyclicSeries H K n) : Prop :=
  ∀ i (hi : i < n), letI := (c.step i hi).normal
    HasNoNontrivialTorsion (c.group (i + 1) ⧸ (c.group i).subgroupOf (c.group (i + 1)))

def IsPolyZ (G : Type) [Group G] : Prop :=
  ∃ n, ∃ c : CyclicSeries (⊥ : Subgroup G) ⊤ n, TorsionFreeCyclicFactors c

theorem IsPolyZ.isPolycyclic (h : IsPolyZ G) : IsPolycyclic G := by
  obtain ⟨n, c, _⟩ := h
  exact ⟨n, ⟨c⟩⟩

theorem TorsionFreeCyclicFactors.comap {H K : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K n} (hc : TorsionFreeCyclicFactors c) (f : J →* G) :
    TorsionFreeCyclicFactors (c.comap f) := by
  dsimp only [TorsionFreeCyclicFactors, CyclicSeries.comap]
  intro i hi
  let := (c.step i hi).normal
  let := (c.step i hi).normal_comap f
  exact (hc i hi).of_injective ((c.step i hi).factorComap f)
    ((c.step i hi).factorComap_injective f)

theorem IsPolyZ.of_injective (h : IsPolyZ G) (f : J →* G)
    (hf : Function.Injective f) : IsPolyZ J := by
  obtain ⟨n, c, hc⟩ := h
  let d := c.comap f
  let d' : CyclicSeries (⊥ : Subgroup J) ⊤ n :=
    { d with
      first := by
        simpa only [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff f).mpr hf] using d.first
      last := by simpa only [Subgroup.comap_top] using d.last }
  exact ⟨n, d', hc.comap f⟩

theorem IsPolyZ.of_equiv (h : IsPolyZ G) (e : G ≃* J) : IsPolyZ J :=
  h.of_injective e.symm.toMonoidHom e.symm.injective

theorem isPolyZ_of_subsingleton [Subsingleton G] : IsPolyZ G := by
  let c : CyclicSeries (⊥ : Subgroup G) ⊤ 0 :=
    { CyclicSeries.refl (⊥ : Subgroup G) with last := Subsingleton.elim _ _ }
  exact ⟨0, c, by intro i hi; omega⟩

end PolycyclicRecognition

end

end OAI
