import Mathlib
import OAI.Computability.MinUncut.Games.TripleKernel

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

abbrev TripleIndex (J : Type*) := Option (Option (Option J))

def tripleTupleEquiv {J A : Type*} :
    (TripleIndex J → A) ≃ ((J → A) × (A × A × A)) where
  toFun L := (fun j => L (some (some (some j))), L none,L (some none),L (some (some none)))
  invFun z
    | none => z.2.1
    | some none => z.2.2.1
    | some (some none) => z.2.2.2
    | some (some (some j)) => z.1 j
  left_inv L := by funext j; cases j with
    | none => rfl
    | some j => cases j with
      | none => rfl
      | some j => cases j <;> rfl
  right_inv _ := rfl

lemma TripleIndex.card (J : Type*) [Fintype J] :
    Fintype.card (TripleIndex J)=Fintype.card J+3 := by simp [TripleIndex]

variable {J V W : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Module F₂ V] [Fintype V]
  [AddCommGroup W] [Module F₂ W] [Fintype W]

def adaptiveKernel (f : (J → V) → V → ℝ) (u : ℝ) (L : TripleIndex J → V) : ℝ :=
  tripleKernel (remainder (f (tripleTupleEquiv L).1) u) (tripleTupleEquiv L).2

omit [Fintype J] [DecidableEq J] in
lemma adaptiveKernel_abs (f : (J → V) → V → ℝ) {M u : ℝ}
    (hM : 0≤M) (hu : 0<u) (hf : ∀ D z, |f D z|≤M) (L : TripleIndex J → V) :
    |adaptiveKernel f u L|≤(M+M^2/u)^4 :=
  tripleKernel_abs _ (by positivity) (remainder_abs_bound _ hM hu (hf _)) _

lemma adaptiveKernel_uniform (f : (J → V) → V → ℝ) {M u : ℝ}
    (hM : 0≤M) (hu : 0<u) (hf : ∀ D z, |f D z|≤M) :
    (𝔼 L : TripleIndex J → V, adaptiveKernel f u L)≤u^2*M^2 := by
  have he : (𝔼 L : TripleIndex J → V, adaptiveKernel f u L) =
      𝔼 z : (J → V) × (V × V × V), tripleKernel (remainder (f z.1) u) z.2 :=
    Fintype.expect_equiv tripleTupleEquiv _ _ (fun _ => rfl)
  rw [he,expect_pair]
  simp_rw [tripleKernel_mean]
  exact (Finset.expect_le_expect (fun D _ => remainder_fourth_bound (f D) hM hu (hf D))).trans_eq
    (Fintype.expect_const _)

omit [Fintype J] [DecidableEq J] [Fintype W] in
lemma adaptiveKernel_pullback (π : W →ₗ[F₂] V) (f : (J → V) → V → ℝ) (u : ℝ)
    (L : TripleIndex J → W) :
    adaptiveKernel f u (fun j => π (L j)) =
      tripleKernel (fun z => remainder (f (fun j => π ((tripleTupleEquiv L).1 j))) u (π z))
        (tripleTupleEquiv L).2 := by
  simp only [adaptiveKernel,tripleKernel,tripleTupleEquiv,Equiv.coe_fn_mk,map_add]

lemma adaptiveKernel_pullback_mean (π : W →ₗ[F₂] V) (f : (J → V) → V → ℝ) (u : ℝ) :
    (𝔼 L : TripleIndex J → W, adaptiveKernel f u (fun j => π (L j))) =
      𝔼 D : J → W, ∑ β : Module.Dual F₂ W,
        coefficient (fun z => remainder (f (fun j => π (D j))) u (π z)) β ^4 := by
  simp_rw [adaptiveKernel_pullback]
  have he := Fintype.expect_equiv (tripleTupleEquiv (J := J) (A := W))
    (fun L => tripleKernel (fun z => remainder (f (fun j => π ((tripleTupleEquiv L).1 j))) u (π z))
      (tripleTupleEquiv L).2)
    (fun z => tripleKernel (fun w => remainder (f (fun j => π (z.1 j))) u (π w)) z.2)
    (fun _ => rfl)
  rw [he,expect_pair]
  simp_rw [tripleKernel_mean]

end MinUncut.Composition

end
end

end OAI
