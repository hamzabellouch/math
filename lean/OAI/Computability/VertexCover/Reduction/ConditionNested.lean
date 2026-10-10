import Mathlib
import OAI.Computability.VertexCover.Analysis.Restriction

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace EnergyForm

noncomputable def finite {S : Type*} [Fintype S] (B : EnergyForm E) : EnergyForm (S → E) where
  form :=
    { toFun := fun f =>
        { toFun := fun g => (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (g s)
          map_add' := fun g h => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun a g => by simp [mul_left_comm, Finset.mul_sum] }
      map_add' := fun f g => by
        ext h
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        ext g
        simp [mul_left_comm, Finset.mul_sum] }
  symm f g := by
    change (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (g s) =
      (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (g s) (f s)
    simp only [B.symm]
  nonneg f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun s _ => B.nonneg (f s)))

@[simp] theorem finite_form {S : Type*} [Fintype S] (B : EnergyForm E) (f g : S → E) :
    B.finite.form f g = (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (g s) := rfl

@[simp] theorem finite_energy {S : Type*} [Fintype S] (B : EnergyForm E) (f : S → E) :
    B.finite.energy f = (Fintype.card S : ℝ)⁻¹ * ∑ s, B.energy (f s) := rfl

namespace Projection
variable {B : EnergyForm E}

def lift {S : Type*} [Fintype S] (P : B.Projection) : (B.finite (S := S)).Projection where
  toLinearMap :=
    { toFun := fun f s => P (f s)
      map_add' := fun f g => funext (fun s => P.map_add (f s) (g s))
      map_smul' := fun a f => funext (fun s => P.map_smul a (f s)) }
  idem f := funext (fun s => P.apply_idem (f s))
  selfAdjoint f g := by
    change (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (P (f s)) (g s) =
      (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (P (g s))
    simp only [P.selfAdjoint]

@[simp] theorem lift_apply {S : Type*} [Fintype S] (P : B.Projection) (f : S → E) (s : S) :
    P.lift f s = P (f s) := rfl

theorem productMap_lift {S ι : Type*} [Fintype S] (P : ι → B.Projection)
    (is : List ι) (f : S → E) (s : S) :
    productMap (fun i => (P i).lift) is f s = productMap P is (f s) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [productMap_cons, lift_apply, ih]

section Conditional
variable {S T : Type*} [Fintype S]

noncomputable def fiberSize (q : S → T) (t : T) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s => q s = t)).card

noncomputable def fiberKernel (q : S → T) (s t : S) : ℝ := by
  classical
  exact if q t = q s then (fiberSize q (q s) : ℝ)⁻¹ else 0

theorem fiberSize_pos (q : S → T) (s : S) : 0 < fiberSize q (q s) := by
  classical
  exact Finset.card_pos.mpr ⟨s, by simp⟩

theorem fiberKernel_symm (q : S → T) (s t : S) : fiberKernel q s t = fiberKernel q t s := by
  classical
  by_cases h : q t = q s
  · simp [fiberKernel, h]
  · simp [fiberKernel, h, Ne.symm h]

theorem fiberKernel_sum (q : S → T) (s : S) : ∑ t, fiberKernel q s t = 1 := by
  classical
  simp only [fiberKernel, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (fiberSize q (q s) : ℝ) * (fiberSize q (q s) : ℝ)⁻¹ = 1
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (fiberSize_pos q s).ne')

noncomputable def conditionMap (q : S → T) : (S → E) →ₗ[ℝ] (S → E) where
  toFun f s := ∑ t, fiberKernel q s t • f t
  map_add' f g := by
    ext s
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext s
    simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem conditionMap_apply (q : S → T) (f : S → E) (s : S) :
    conditionMap q f s = ∑ t, fiberKernel q s t • f t := rfl

theorem conditionMap_congr {R : Type*} (q : S → T) (r : S → R)
    (h : ∀ s t, q s = q t ↔ r s = r t) :
    (conditionMap q : (S → E) →ₗ[ℝ] (S → E)) = conditionMap r := by
  classical
  have hs : ∀ s, fiberSize q (q s) = fiberSize r (r s) := by
    intro s
    unfold fiberSize
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
  apply LinearMap.ext
  intro f
  funext s
  simp only [conditionMap_apply, fiberKernel, h, hs]

theorem conditionMap_eq_of_key_eq (q : S → T) (f : S → E) {s t : S}
    (h : q s = q t) : conditionMap q f s = conditionMap q f t := by
  classical
  change (∑ x, (if q x = q s then (fiberSize q (q s) : ℝ)⁻¹ else 0) • f x) =
    ∑ x, (if q x = q t then (fiberSize q (q t) : ℝ)⁻¹ else 0) • f x
  rw [h]

theorem conditionMap_of_invariant (q : S → T) (f : S → E)
    (hf : ∀ s t, q s = q t → f s = f t) (s : S) : conditionMap q f s = f s := by
  classical
  calc
    conditionMap q f s = ∑ t, fiberKernel q s t • f s := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : q t = q s
      · rw [hf t s ht]
      · simp [fiberKernel, ht]
    _ = f s := by rw [← Finset.sum_smul, fiberKernel_sum, one_smul]

noncomputable def condition (q : S → T) : (B.finite (S := S)).Projection where
  toLinearMap := conditionMap q
  idem f := funext (conditionMap_of_invariant q (conditionMap q f)
    (fun _ _ h => conditionMap_eq_of_key_eq q f h))
  selfAdjoint f g := by
    simp only [finite_form, conditionMap_apply, _root_.map_sum, _root_.map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [fiberKernel_symm]

@[simp] theorem condition_apply (q : S → T) (f : S → E) (s : S) :
    condition (B := B) q f s = conditionMap q f s := rfl

theorem condition_lift_commute (q : S → T) (P : B.Projection) (f : S → E) :
    condition (B := B) q (P.lift f) = P.lift (condition (B := B) q f) := by
  ext s
  simp only [condition_apply, conditionMap_apply, lift_apply, _root_.map_sum,
    _root_.map_smul]

theorem condition_nested {R : Type*} (q : S → T) (r : S → R)
    (h : ∀ s t, q s = q t → r s = r t) (f : S → E) :
    condition (B := B) q (condition (B := B) r f) = condition (B := B) r f := by
  ext s
  apply conditionMap_of_invariant
  intro s t he
  exact conditionMap_eq_of_key_eq r f (h s t he)

end Conditional
end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
