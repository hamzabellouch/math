import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphRetainedDirect
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

noncomputable def nearRetainedND {d : ℕ} (h : ℕ)
    (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ) (r : ℝ) (z : V × V) : ℂ :=
  graphRetainedDirectND A B ({()}:Finset Unit) (fun _ => nearGridPairND h)
    (fun _ _ => 1) U W r z

omit [MeasurableSpace V] in
lemma nearRetainedND_eq {d : ℕ} (h : ℕ) (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ) (r : ℝ) (z : V × V) :
    nearRetainedND h A B U W r z =
      ∑ a ∈ A.product B, ∑ b ∈ A.product B, if nearGridPairND h a b then
        (U a.1 (r,z.1)*W a.2 (r,z.2))*
          conj (U b.1 (r,z.1)*W b.2 (r,z.2)) else 0 := by
  simp only [nearRetainedND,graphRetainedDirectND,Finset.sum_singleton,
    Complex.ofReal_one,one_mul]

theorem nearRetainedND_integral_bound {d : ℕ} (h : ℕ)
    (μ : Measure V) [IsFiniteMeasure μ] (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) (hΨpos : ∀ r, 0≤Ψ r) :
    ‖∫ r, (Ψ r:ℂ)*∫ z, nearRetainedND h A B U W r z ∂μ.prod μ‖ ≤
      (20*(d+1:ℝ)+5)^(2*d)*∑ i∈A, ∑ j∈B,
        ∫ r, Ψ r*sourceAngularMomentND μ (U i) r*sourceAngularMomentND μ (W j) r := by
  exact graphRetainedDirectND_integral_bound μ A B ({()}:Finset Unit)
    (fun _ => nearGridPairND h) (fun _ _ => 1) (by filter_upwards with z; simp)
    U W hU hW C E hbU hbW ((20*(d+1:ℝ)+5)^(2*d))
    (fun _ _ a _ => nearGridPairND_row_card h A B a)
    (fun _ _ b _ => nearGridPairND_col_card h A B b) hΨ hΨpos

noncomputable def nearAngularEnergyND (d : ℕ) (μ : Measure V) (a : ℝ) (h : ℕ)
    (v lam₁ lam₂ : ℝ) (Ψ : ℝ → ℝ) (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ) : ℝ :=
  lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ‖∫ r, (Ψ (r/(2:ℝ)^v):ℂ)*∫ z, nearRetainedND h A B U W r z ∂μ.prod μ‖

theorem nearAngularEnergyND_le_sum (d : ℕ) (μ : Measure V) [IsFiniteMeasure μ]
    (a : ℝ) (h : ℕ) (v lam₁ lam₂ : ℝ) (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (hΨpos : ∀ r, 0≤Ψ r) :
    nearAngularEnergyND d μ a h v lam₁ lam₂ Ψ A B U W ≤
      lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*((h:ℝ)-a))*(20*(d+1:ℝ)+5)^(2*d)*
        (∑ i∈A, ∑ j∈B, sourceAngularHND d μ h v Ψ (U i) (W j)) := by
  have hh := nearRetainedND_integral_bound h μ A B U W hU hW C E hbU hbW hΨ
    (fun r => hΨpos (r/(2:ℝ)^v))
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0≤lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹ by positivity)
  have hf : (2:ℝ)^((d:ℝ)*((h:ℝ)-a))*(2:ℝ)^((d:ℝ)*(v-(h:ℝ))) =
      (2:ℝ)^((d:ℝ)*(v-a)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  apply hm.trans_eq
  simp only [sourceAngularHND,← Finset.mul_sum]
  rw [← hf]
  ring

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
