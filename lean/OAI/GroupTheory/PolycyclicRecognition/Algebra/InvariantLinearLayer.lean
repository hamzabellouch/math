import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Endomorphisms on an invariant subquotient

This is the concrete linear bridge used on successive lower-central factors.
Commutation modulo the smaller subspace becomes exact commutation, and
unipotence survives restriction and quotient.
-/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev InvariantLinearLayer (U W : Submodule ℝ V) := U ⧸ W.comap U.subtype

def invariantLayerEnd (U W : Submodule ℝ V) (f : Module.End ℝ V)
    (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) :
    Module.End ℝ (InvariantLinearLayer U W) :=
  (W.comap U.subtype).mapQ (W.comap U.subtype) (f.restrict hU) (fun x hx => hW x hx)

theorem invariantLayerEnd_commute (U W : Submodule ℝ V) (f g : Module.End ℝ V)
    (hfU : ∀ x ∈ U, f x ∈ U) (hgU : ∀ x ∈ U, g x ∈ U)
    (hfW : ∀ x ∈ W, f x ∈ W) (hgW : ∀ x ∈ W, g x ∈ W)
    (hcomm : ∀ x ∈ U, f (g x) - g (f x) ∈ W) :
    Commute (invariantLayerEnd U W f hfU hfW) (invariantLayerEnd U W g hgU hgW) := by
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro x
  change (Submodule.Quotient.mk ((f.restrict hfU) ((g.restrict hgU) x)) : InvariantLinearLayer U W) =
    Submodule.Quotient.mk ((g.restrict hgU) ((f.restrict hfU) x))
  apply (Submodule.Quotient.eq (W.comap U.subtype)).mpr
  exact hcomm x x.property

theorem invariantLayerEnd_unipotent (U W : Submodule ℝ V) (f : Module.End ℝ V)
    (hfU : ∀ x ∈ U, f x ∈ U) (hfW : ∀ x ∈ W, f x ∈ W)
    (hnil : IsNilpotent (f - 1)) :
    IsNilpotent (invariantLayerEnd U W f hfU hfW - 1) := by
  let R := W.comap U.subtype
  let d := f.restrict hfU - 1
  have hd : R ≤ R.comap d := fun x hx => W.sub_mem (hfW x hx) hx
  have hdU : ∀ x ∈ U, (f - 1) x ∈ U := fun x hx => U.sub_mem (hfU x hx) hx
  have he : d = (f - 1).restrict hdU := by
    apply LinearMap.ext
    intro x
    rfl
  have hdn : IsNilpotent d := he ▸ Module.End.isNilpotent.restrict hdU hnil
  have hq : invariantLayerEnd U W f hfU hfW - 1 = R.mapQ R d hd := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  rw [hq]
  obtain ⟨n, hn⟩ := hdn
  refine ⟨n, ?_⟩
  rw [← R.mapQ_pow hd n]
  simp only [hn, Submodule.mapQ_zero]

end PolycyclicRecognition

end

end OAI
