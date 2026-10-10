import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # Invertibility of a triangular scalar extension -/

noncomputable section

namespace BoltzmannNonuniqueness

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem triangular_bijective (L : P × ℝ →L[ℝ] P × ℝ)
    (hf : ∀ x, (L x).1 = x.1) (hd : (L (0,1)).2 ≠ 0) :
    Function.Bijective L := by
  have he (p : P) (u : ℝ) : (L (p,u)).2 = (L (p,0)).2 + u*(L (0,1)).2 := by
    have h : (p,u) = (p,0) + u • (0,1) := by ext <;> simp
    rw [h,map_add,map_smul]
    rfl
  constructor
  · rintro ⟨p,u⟩ ⟨q,v⟩ h
    have hp : p = q := by simpa only [hf] using congrArg Prod.fst h
    subst q
    refine Prod.ext rfl ?_
    have hu := congrArg Prod.snd h
    rw [he p u,he p v] at hu
    exact mul_right_cancel₀ hd (add_left_cancel hu)
  · rintro ⟨p,u⟩
    refine ⟨(p,(u-(L (p,0)).2)/(L (0,1)).2),?_⟩
    refine Prod.ext (hf _) ?_
    rw [he,div_mul_cancel₀ _ hd]
    ring

def triangularEquiv [FiniteDimensional ℝ P] (L : P × ℝ →L[ℝ] P × ℝ)
    (hf : ∀ x, (L x).1 = x.1) (hd : (L (0,1)).2 ≠ 0) :
    (P × ℝ) ≃L[ℝ] (P × ℝ) :=
  (LinearEquiv.ofBijective L.toLinearMap (triangular_bijective L hf hd)).toContinuousLinearEquiv

@[simp] theorem triangularEquiv_coe [FiniteDimensional ℝ P]
    (L : P × ℝ →L[ℝ] P × ℝ) (hf : ∀ x, (L x).1 = x.1)
    (hd : (L (0,1)).2 ≠ 0) : (triangularEquiv L hf hd).toContinuousLinearMap = L := rfl

end BoltzmannNonuniqueness

end

end OAI
