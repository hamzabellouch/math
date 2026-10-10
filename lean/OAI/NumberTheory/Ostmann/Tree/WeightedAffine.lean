import OAI.NumberTheory.Ostmann.Tree.AffineUnitEnergy
import OAI.NumberTheory.Ostmann.Tree.MeanInner

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def affineSubstitutionEquiv (r : (ZMod p)ˣ) : ZMod p ≃ ZMod p where
  toFun := affineUnitSubstitution r
  invFun := inverseAffineUnitSubstitution r
  left_inv := inverseAffineUnitSubstitution_affine r
  right_inv := affineUnitSubstitution_inverse r

def weightedAffine (w : (ZMod p)ˣ → ℂ) (f : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  (p:ℂ)⁻¹ * ∑ r, w r * f (affineUnitSubstitution r t)

def weightedAffineAdjoint (w : (ZMod p)ˣ → ℂ) (f : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  (p:ℂ)⁻¹ * ∑ r, conj (w r) * f (inverseAffineUnitSubstitution r t)

theorem affineSubstitution_sum (r : (ZMod p)ˣ) (f : ZMod p → ℂ) :
    ∑ t, f (affineUnitSubstitution r t) = ∑ t, f t :=
  (affineSubstitutionEquiv r).bijective.sum_comp f

theorem affineSubstitution_pairing (r : (ZMod p)ˣ) (f h : ZMod p → ℂ) :
    ∑ t, conj (f (affineUnitSubstitution r t))*h t =
      ∑ t, conj (f t)*h (inverseAffineUnitSubstitution r t) := by
  have hh := (affineSubstitutionEquiv r).bijective.sum_comp
    (fun t => conj (f t)*h (inverseAffineUnitSubstitution r t))
  simpa only [affineSubstitutionEquiv, Equiv.coe_fn_mk,
    inverseAffineUnitSubstitution_affine] using hh

theorem weightedAffine_adjoint (w : (ZMod p)ˣ → ℂ) (f h : ZMod p → ℂ) :
    meanInner (weightedAffine w f) h = meanInner f (weightedAffineAdjoint w h) := by
  have hl : meanInner (weightedAffine w f) h =
      (p:ℂ)⁻¹ * (p:ℂ)⁻¹ * ∑ r, conj (w r) *
        ∑ t, conj (f (affineUnitSubstitution r t))*h t := by
    simp only [meanInner, mean, weightedAffine, map_mul, map_inv₀, map_natCast,
      map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hr : meanInner f (weightedAffineAdjoint w h) =
      (p:ℂ)⁻¹ * (p:ℂ)⁻¹ * ∑ r, conj (w r) *
        ∑ t, conj (f t)*h (inverseAffineUnitSubstitution r t) := by
    simp only [meanInner, mean, weightedAffineAdjoint, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hl, hr]
  simp_rw [affineSubstitution_pairing]

theorem weightedAffine_adjoint_comp (w : (ZMod p)ˣ → ℂ) (f : ZMod p → ℂ) :
    weightedAffineAdjoint w (weightedAffine w f) =
      fun t => (p:ℂ)⁻¹*(p:ℂ)⁻¹ * affineAction (affineUnitCoefficient w) f t := by
  funext t
  unfold affineAction
  rw [affineUnitCoefficient_action w f t]
  simp only [weightedAffineAdjoint, weightedAffine, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem weightedAffine_mean (w : (ZMod p)ˣ → ℂ) (f : ZMod p → ℂ) :
    mean (weightedAffine w f) = ((p:ℂ)⁻¹ * ∑ r, w r) * mean f := by
  simp only [mean, weightedAffine, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r, (p:ℂ)⁻¹*(p:ℂ)⁻¹*w r * ∑ t, f (affineUnitSubstitution r t) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      simp only [affineSubstitution_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro t _
      ring

end
end Ostmann.FiniteField

end OAI
