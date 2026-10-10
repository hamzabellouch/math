import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePoleCoefficient

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff ComplexConjugate
attribute [local instance] Classical.propDecidable

lemma sphereLND_support {n : ℕ} (j : ℕ) {b : SphereAmbientND n → ℂ}
    (hb : ContDiff ℝ ∞ b) : tsupport (sphereLND n j b) ⊆ tsupport b := by
  rw [sphereLND_eq_polynomial j ⟨b,hb⟩]
  exact differentialPolynomialND_support _ _ _

lemma sphere_conj_tsupportND {V : Type*} [TopologicalSpace V] (b : V → ℂ) :
    tsupport (fun w => conj (b w))=tsupport b := by
  unfold tsupport
  congr 1
  ext w
  simp only [Function.mem_support,map_ne_zero]

lemma spherePoleCoefficientND_zero {n J : ℕ} {b : SphereAmbientND n → ℂ}
    (hb : ContDiff ℝ ∞ b) {S : Set (SphereAmbientND n)}
    (hS : ∀ w∈S, -w∈S) (hbS : tsupport b ⊆ S)
    {e : SphereAmbientND n} (he : e∉S) (Λ : ℝ) (i : PoleIndexND J) :
    spherePoleCoefficientND J Λ b e i = 0 := by
  have hp : sphereLND n i.2 b e = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => he (hbS (sphereLND_support i.2 hb hh)))
  have hne : -e∉S := by
    intro hh
    have hh' := hS (-e) hh
    simp only [neg_neg] at hh'
    exact he hh'
  have hc : ContDiff ℝ ∞ (fun w => conj (b w)) :=
    Complex.conjCLE.contDiff.comp hb
  have hm : sphereLND n i.2 (fun w => conj (b w)) (-e)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    have hh' := sphereLND_support i.2 hc hh
    rw [sphere_conj_tsupportND] at hh'
    exact hne (hbS hh')
  simp [spherePoleCoefficientND,sphereLMinusND,hp,hm]

lemma radialPoleSumND_zero (n J : ℕ) (Λ : ℝ) (c : PoleIndexND J → ℂ)
    (hc : ∀ i, c i=0) (u : ℝ) : radialPoleSumND n J Λ c u=0 := by
  simp [radialPoleSumND,hc]

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
