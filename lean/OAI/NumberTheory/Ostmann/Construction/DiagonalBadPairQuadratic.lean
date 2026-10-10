import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairInverse

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem paired_weight_quadratic_bound {α : Type*} [Fintype α] (E : α≃α)
    (W : α→ℝ) (A : α→ℂ) (hW : ∀z,0≤W z) (hWE : ∀z,W (E z)=W z) :
    (∑z,W z*(A z*star (A (E z))).re)≤∑z,W z*‖A z‖^2 := by
  have hp (z : α) : 2*(A z*star (A (E z))).re≤‖A z‖^2+‖A (E z)‖^2 := by
    have hr := Complex.re_le_norm (A z*star (A (E z)))
    rw [norm_mul,norm_star] at hr
    nlinarith [sq_nonneg (‖A z‖-‖A (E z)‖)]
  have he : (∑z,W z*‖A (E z)‖^2)=∑z,W z*‖A z‖^2 := by
    apply Fintype.sum_equiv E
    intro z
    rw [hWE]
  have hsum : 2*(∑z,W z*(A z*star (A (E z))).re)≤
      (∑z,W z*‖A z‖^2)+(∑z,W z*‖A (E z)‖^2) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z hz
    nlinarith [mul_le_mul_of_nonneg_left (hp z) (hW z)]
  rw [he] at hsum
  linarith

theorem badCounterpartPair_quadratic_bound (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (B : Equiv.Perm (RemainingIndex T)→Prop)
    (hB : ∀e,B e→B e.symm) (G : RemainingSample sources T giant→ℝ)
    (A : RemainingSample sources T giant→ℂ) (hG : ∀x,0≤G x)
    (hGE : ∀(x : RemainingSample sources T giant)(e : Equiv.Perm (RemainingIndex T))
      (he : CounterpartCompatible sources T giant x e),B e →
      (remainingPrior sources T giant).mass x≠0 →
      (remainingPrior sources T giant).mass (reconstructCounterpart sources T giant x e he)≠0 →
      G (reconstructCounterpart sources T giant x e he)=G x) :
    (∑z : BadCounterpartPair sources T giant B,
      ((remainingPrior sources T giant).mass z.val.1*
        (remainingPrior sources T giant).mass
          (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*G z.val.1)*
      (A z.val.1*star (A (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1))).re)≤
    ∑z : BadCounterpartPair sources T giant B,
      ((remainingPrior sources T giant).mass z.val.1*
        (remainingPrior sources T giant).mass
          (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*G z.val.1)*‖A z.val.1‖^2 := by
  let W : BadCounterpartPair sources T giant B→ℝ := fun z =>
    (remainingPrior sources T giant).mass z.val.1*
      (remainingPrior sources T giant).mass
        (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*G z.val.1
  apply paired_weight_quadratic_bound (badCounterpartSwapEquiv sources T giant B hB) W
    (fun z => A z.val.1)
  · intro z
    exact mul_nonneg (mul_nonneg ((remainingPrior sources T giant).mass_nonneg _)
      ((remainingPrior sources T giant).mass_nonneg _)) (hG _)
  · intro z
    change (remainingPrior sources T giant).mass
        (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*
      (remainingPrior sources T giant).mass
        (reconstructCounterpart sources T giant
          (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)
          z.val.2.symm _)*
      G (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)=W z
    rw [reconstructCounterpart_inverse]
    unfold W
    by_cases hx : (remainingPrior sources T giant).mass z.val.1=0
    · simp only [hx,mul_zero,zero_mul]
    by_cases hy : (remainingPrior sources T giant).mass
        (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)=0
    · simp only [hy,mul_zero,zero_mul]
    rw [hGE _ _ _ z.property.2 hx hy]
    ring

end Ostmann.Construction

end

end OAI
