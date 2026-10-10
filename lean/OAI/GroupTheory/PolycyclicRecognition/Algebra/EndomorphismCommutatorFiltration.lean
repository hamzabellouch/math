import OAI.GroupTheory.PolycyclicRecognition.Algebra.EquivariantCommutatorFiltration

namespace OAI

/-! # The commutator-filtration bridge for linear endomorphism representations -/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℝ V]

theorem linearActionFiltration_comp_le {I J : Type*} (D : I → Module.End ℝ V)
    (f : J → I) (n : ℕ) : linearActionFiltration (D ∘ f) n ≤ linearActionFiltration D n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change (⨆ j, (linearActionFiltration (D ∘ f) n).map (D (f j))) ≤ _
    apply iSup_le
    intro j
    exact (Submodule.map_mono ih).trans (le_iSup
      (fun i => (linearActionFiltration D n).map (D i)) (f j))

theorem relativeCommutatorSeries_le_endFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* Module.End ℝ V)
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd) (n : ℕ) :
    relativeCommutatorSeries K N n ≤
      (linearPreimageSubgroup π (linearActionFiltration
        (fun g : K => ρ g - 1) n)).map N.subtype := by
  let D := fun g : K => ρ g - 1
  induction n with
  | zero =>
    intro a ha
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    change (π ⟨a, ha⟩).toAdd ∈ (⊤ : Submodule ℝ V)
    trivial
  | succ n ih =>
    apply Subgroup.commutator_le.mpr
    intro g hg a ha
    obtain ⟨a, hav, rfl⟩ := ih ha
    let b : N := MulAut.conjNormal (H := N) g a * a⁻¹
    have hb : (π b).toAdd = D ⟨g, hg⟩ (π a).toAdd := by
      simp only [b, map_mul, map_inv, toAdd_mul, toAdd_inv, heq]
      change ρ g (π a).toAdd + -(π a).toAdd = ρ g (π a).toAdd - (π a).toAdd
      exact (sub_eq_add_neg _ _).symm
    refine ⟨b, ?_, rfl⟩
    change (π b).toAdd ∈ linearActionFiltration D (n + 1)
    rw [hb]
    exact ActionDepth.generator (D := D) (⟨g, hg⟩ : K) n _ hav

theorem relativeCommutatorSeries_le_kernel_of_endFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* Module.End ℝ V)
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd)
    (c : ℕ) (hc : linearActionFiltration (fun g : K => ρ g - 1) c = ⊥) :
    relativeCommutatorSeries K N c ≤ π.ker.map N.subtype := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := relativeCommutatorSeries_le_endFiltration K N ρ π heq c hg
  refine ⟨a, ?_, rfl⟩
  change (π a).toAdd ∈ linearActionFiltration (fun g : K => ρ g - 1) c at ha
  rw [hc, Submodule.mem_bot] at ha
  change π a = 1
  exact Multiplicative.toAdd.injective ha

end PolycyclicRecognition

end

end OAI
