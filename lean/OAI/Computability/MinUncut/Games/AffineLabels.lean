import Mathlib
import OAI.Computability.MinUncut.Estimates.F2

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open BinaryFourier
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

def labelFrequency (a : A) : Module.Dual F₂ (Forms A) where
  toFun b := b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma labelFrequency_apply (a : A) (b : Forms A) : labelFrequency a b = b a := rfl
@[simp] lemma labelFrequency_odd (a : A) :
    labelFrequency a (AffineMap.const F₂ A 1) = 1 := rfl

def basedForm (a₀ : A) : Module.Dual F₂ V →ₗ[F₂] Forms A where
  toFun l := l.toAffineMap.comp (AffineEquiv.vaddConst F₂ a₀).symm.toAffineMap
  map_add' l k := by ext a; rfl
  map_smul' t l := by ext a; rfl

@[simp] lemma basedForm_apply (a₀ a : A) (l : Module.Dual F₂ V) :
    basedForm a₀ l a = l (a -ᵥ a₀) := rfl

lemma form_decomposition (a₀ : A) (b : Forms A) :
    b = basedForm a₀ b.linear + b a₀ • AffineMap.const F₂ A 1 := by
  ext a
  have h := b.map_vadd a₀ (a -ᵥ a₀)
  simpa only [vsub_vadd, vadd_eq_add, AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply,
    AffineMap.const_apply, smul_eq_mul, mul_one, basedForm_apply] using h

lemma labelFrequency_injective : Function.Injective (labelFrequency (A := A)) := by
  intro a a' h
  have hlin : (Module.Dual.eval F₂ V) (a -ᵥ a') = 0 := by
    ext l
    have hh := congrArg (fun α : Module.Dual F₂ (Forms A) => α (basedForm a' l)) h
    simpa using hh
  have hz : a -ᵥ a' = 0 := (Module.eval_apply_eq_zero_iff F₂ _).mp hlin
  exact vsub_eq_zero_iff_eq.mp hz

variable [Fintype A]

lemma oddFrequency_exists_label (α : Module.Dual F₂ (Forms A))
    (hα : α (AffineMap.const F₂ A 1) = 1) : ∃ a : A, labelFrequency a = α := by
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let : Fintype V := Fintype.ofEquiv A (AffineEquiv.vaddConst F₂ a₀).toEquiv.symm
  obtain ⟨v,hv⟩ := (Module.bijective_dual_eval F₂ V).2 (α.comp (basedForm a₀))
  refine ⟨v +ᵥ a₀, ?_⟩
  apply LinearMap.ext
  intro b
  have hb : α b = b.linear v + b a₀ := by
    conv_lhs => rw [form_decomposition a₀ b]
    rw [map_add, map_smul, hα]
    have hh := congrArg (fun β : Module.Dual F₂ (Module.Dual F₂ V) => β b.linear) hv
    change b.linear v = α (basedForm a₀ b.linear) at hh
    rw [← hh]
    simp
  simpa only [labelFrequency_apply, AffineMap.map_vadd, vadd_eq_add] using hb.symm

def oddFrequencyEquiv : A ≃ {α : Module.Dual F₂ (Forms A) //
    α (AffineMap.const F₂ A 1) = 1} :=
  Equiv.ofBijective (fun a => ⟨labelFrequency a, labelFrequency_odd a⟩)
    ⟨fun _ _ h => labelFrequency_injective (congrArg Subtype.val h),
      fun α => by
        obtain ⟨a,ha⟩ := oddFrequency_exists_label α.val α.property
        exact ⟨a, Subtype.ext ha⟩⟩

variable {V' A' : Type*} [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A']

def formPullback (π : A →ᵃ[F₂] A') : Forms A' →ₗ[F₂] Forms A where
  toFun b := b.comp π
  map_add' _ _ := by ext a; rfl
  map_smul' _ _ := by ext a; rfl

omit [Fintype A] in
@[simp] lemma formPullback_one (π : A →ᵃ[F₂] A') :
    formPullback π (AffineMap.const F₂ A' 1) = AffineMap.const F₂ A 1 := by ext a; rfl

omit [Fintype A] in
@[simp] lemma labelFrequency_pullback (π : A →ᵃ[F₂] A') (a : A) :
    (labelFrequency a).comp (formPullback π) = labelFrequency (π a) := rfl
end MinUncut.Inner

end
end

end OAI
