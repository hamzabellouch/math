import Mathlib
import OAI.Analysis.Commutator.FinitePairings3
import OAI.Analysis.Commutator.Pairings

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

namespace Pairing

def Crosses {k l : ℕ} (τ : Pairing (TailSlots k l)) : Prop :=
  (∀ a : Fin k, ∃ b : Fin l, τ (.inl a) = .inr b) ∧
  (∀ b : Fin l, ∃ a : Fin k, τ (.inr b) = .inl a)

def crossPairing {k l : ℕ} (e : Fin k ≃ Fin l) : Pairing (TailSlots k l) :=
  ⟨{ toFun := Sum.elim (fun a => .inr (e a)) (fun b => .inl (e.symm b))
     invFun := Sum.elim (fun a => .inr (e a)) (fun b => .inl (e.symm b))
     left_inv := by
       intro j
       cases j with
       | inl a => exact congrArg Sum.inl (e.symm_apply_apply a)
       | inr b => exact congrArg Sum.inr (e.apply_symm_apply b)
     right_inv := by
       intro j
       cases j with
       | inl a => exact congrArg Sum.inl (e.symm_apply_apply a)
       | inr b => exact congrArg Sum.inr (e.apply_symm_apply b) },
   by
     intro j
     cases j with
     | inl a => exact congrArg Sum.inl (e.symm_apply_apply a)
     | inr b => exact congrArg Sum.inr (e.apply_symm_apply b),
   by intro j; cases j <;> intro h <;> cases h⟩

@[simp] theorem crossPairing_inl {k l : ℕ} (e : Fin k ≃ Fin l) (a : Fin k) :
    crossPairing e (.inl a) = .inr (e a) := rfl

@[simp] theorem crossPairing_inr {k l : ℕ} (e : Fin k ≃ Fin l) (b : Fin l) :
    crossPairing e (.inr b) = .inl (e.symm b) := rfl

theorem crossPairing_crosses {k l : ℕ} (e : Fin k ≃ Fin l) :
    Crosses (crossPairing e) :=
  ⟨fun a => ⟨e a, rfl⟩, fun b => ⟨e.symm b, rfl⟩⟩

theorem crossPairing_injective {k l : ℕ} :
    Function.Injective (@crossPairing k l) := by
  intro e f h
  apply Equiv.ext
  intro a
  exact Sum.inr_injective (congrArg (fun τ : Pairing (TailSlots k l) => τ (.inl a)) h)

theorem exists_crossPairing {k l : ℕ} (τ : Pairing (TailSlots k l)) (hτ : Crosses τ) :
    ∃ e : Fin k ≃ Fin l, crossPairing e = τ := by
  let f : Fin k → Fin l := fun a => (hτ.1 a).choose
  have hf (a : Fin k) : τ (.inl a) = .inr (f a) := (hτ.1 a).choose_spec
  have hinj : Function.Injective f := by
    intro a b hab
    apply Sum.inl_injective
    apply τ.injective
    rw [hf, hf, hab]
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := hτ.2 b
    refine ⟨a, ?_⟩
    have hh := τ.apply_apply (.inr b)
    rw [ha, hf] at hh
    exact Sum.inr_injective hh
  let e : Fin k ≃ Fin l := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  apply ext
  intro j
  cases j with
  | inl a => exact (hf a).symm
  | inr b =>
    apply τ.injective
    erw [τ.apply_apply, crossPairing_inr, hf]
    change Sum.inr (e (e.symm b)) = .inr b
    rw [e.apply_symm_apply]

def crossingEquiv (k l : ℕ) : (Fin k ≃ Fin l) ≃ {τ : Pairing (TailSlots k l) // Crosses τ} :=
  Equiv.ofBijective (fun e => ⟨crossPairing e, crossPairing_crosses e⟩)
    ⟨fun _ _ h => crossPairing_injective (congrArg Subtype.val h), by
      rintro ⟨τ, hτ⟩
      obtain ⟨e, he⟩ := exists_crossPairing τ hτ
      exact ⟨e, Subtype.ext he⟩⟩

@[simp] theorem crossingEquiv_val (k l : ℕ) (e : Fin k ≃ Fin l) :
    (crossingEquiv k l e).val = crossPairing e := rfl

theorem contraction_crossPairing {k l : ℕ} {E : Type*} (e : Fin k ≃ Fin l)
    (B : E → E → ℂ) (v : TailSlots k l → E) :
    contraction (crossPairing e) B v = ∏ a, B (v (.inl a)) (v (.inr (e a))) := by
  classical
  rw [contraction, Finset.prod_filter]
  erw [Fintype.prod_sum_type]
  simp only [crossPairing_inl, crossPairing_inr]
  change (∏ a : Fin k, if (toLex (.inl a) : TailSlots k l) < toLex (.inr (e a))
      then B (v (toLex (.inl a))) (v (toLex (.inr (e a)))) else 1) *
    (∏ b : Fin l, if (toLex (.inr b) : TailSlots k l) < toLex (.inl (e.symm b))
      then B (v (toLex (.inr b))) (v (toLex (.inl (e.symm b)))) else 1) = _
  simp
  rfl

theorem sum_contraction_crossing {k l : ℕ} {E : Type*}
    (B : E → E → ℂ) (v : TailSlots k l → E) (c : Pairing (TailSlots k l) → ℂ)
    (hz : ∀ τ, ¬ Crosses τ → c τ = 0) :
    (∑ τ, c τ * contraction τ B v) =
      ∑ e : Fin k ≃ Fin l, c (crossPairing e) * ∏ a, B (v (.inl a)) (v (.inr (e a))) := by
  classical
  calc
    _ = ∑ τ ∈ Finset.univ.filter Crosses, c τ * contraction τ B v := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro τ _ hτ
      rw [hz τ (by simpa using hτ), zero_mul]
    _ = ∑ τ : {τ : Pairing (TailSlots k l) // Crosses τ},
        c τ.val * contraction τ.val B v := by
      exact Finset.sum_subtype (F := inferInstance) _ (by intro τ; simp) _
    _ = ∑ e : Fin k ≃ Fin l, c (crossPairing e) * contraction (crossPairing e) B v := by
      exact (Equiv.sum_comp (crossingEquiv k l) _).symm
    _ = _ := by simp_rw [contraction_crossPairing]

end Pairing

end Kadison
end

end OAI
