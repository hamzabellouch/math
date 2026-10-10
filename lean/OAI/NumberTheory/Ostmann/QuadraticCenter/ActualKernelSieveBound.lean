import OAI.NumberTheory.Ostmann.QuadraticCenter.AffineKernelNumeratorActual
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelSieveBound

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem actual_affine_kernel_image_card_eventually (c δ ε : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z J : ℕ) (P : Finset ℕ),
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      c*(Z:ℝ)/Real.log Z ≤ J → J ≤ 2*Z →
      commonCenterCutoff Z ≤ P.card →
      commonCenterMomentScale J Z (evenMomentParameter (parameterX T) Z)/4 ≤
        2*(J:ℝ)*(P.card:ℝ)^(evenMomentParameter (parameterX T) Z-1) →
      (∀p∈P,Nat.Prime p) → (∀p∈P,Odd p) →
      (∀p∈P,Z ≤ p) → (∀p∈P,p ≤ 2*Z) →
      ∀ e : ℕ → ℤ,(∀p∈P,e p = -1 ∨ e p = 1) →
      ∀ (A B : Set ℕ) (S : Finset ℤ),
      S ⊆ positiveIntegerWindow A (parameterX T) ∪ negativeIntegerWindow B (parameterX T) →
      ∀ (m : ℕ) (h : ℤ),0 < m → m ≤ quadraticLiftMultiplierBound Z →
      h.natAbs ≤ quadraticLiftHeight (parameterX T) Z →
      (∀x∈S,δ ≤ |affineKernelAverage P e m h x|) →
      ((canonicalKernelImage S m h).card:ℝ) ≤ (parameterX T:ℝ)^ε := by
  filter_upwards [actual_kernel_image_card_eventually c (δ/2) ε hc (half_pos hδ) hε,
    actual_affine_kernel_inputs_eventually δ hδ] with T hcount hactual
  intro Z J P hZl hZu hJ hJu hPJ hcenter hP ho hlow hhigh e he A B S hS m h hm hmcap hhcap hbias
  have ha := hactual Z P hZl hPJ hP hlow e he A B S hS m h hm hmcap hhcap hbias
  exact hcount Z J P hZl hZu hJ hJu hPJ hcenter hP ho hhigh e he S m
    (m*parameterX T+h.natAbs) h ha.1 ha.2.2.2.1
    (fun x hx => (ha.2.2.2.2 x hx).1)
    (fun x hx => (ha.2.2.2.2 x hx).2.1)
    (fun x hx => (ha.2.2.2.2 x hx).2.2.2)

end Ostmann.QuadraticCenter

end

end OAI
