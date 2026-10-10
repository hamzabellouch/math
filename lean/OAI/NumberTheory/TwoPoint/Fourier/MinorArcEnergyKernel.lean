import OAI.NumberTheory.TwoPoint.Fourier.MinorArcShiftedFiber
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcKernelSymmetry
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPrimeFourth

namespace OAI

/-! Regrouping the prime fourth moment by its integer additive difference. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_fiber_sum {α β : Type*} (S : Finset α) (T : Finset β)
    (f : α → β) (w : β → ℝ) (B : ℝ)
    (hmap : ∀ a ∈ S, f a ∈ T) (hw : ∀ b ∈ T, 0 ≤ w b)
    (hcard : ∀ b ∈ T, ((S.filter (fun a => f a = b)).card : ℝ) ≤ B) :
    (∑ a ∈ S, w (f a)) ≤ B * (∑ b ∈ T, w b) := by
  rw [← sum_fiberwise_of_maps_to hmap (fun a => w (f a)), mul_sum]
  apply sum_le_sum
  intro b hb
  calc
    _ = ((S.filter (fun a => f a = b)).card : ℝ) * w b := by
      rw [sum_congr rfl (fun a ha => congrArg w (mem_filter.mp ha).2)]
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard b hb) (hw b hb)

theorem minor_arc_prime_fourth_energy (P : Finset ℕ) (c : ℕ → ℂ)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ 1) (α : ℝ) (a b N : ℕ)
    (hP : ∀ p ∈ P, p ≤ N) :
    (∑ m ∈ Ico a b, ‖∑ p ∈ P, c p * additiveCharacter (α * p) m‖ ^ 4) ≤
      (Finset.addEnergy P P : ℝ) *
        ∑ n ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
          minorArcGeometricBound ((b - a : ℕ) : ℝ) (α * (n : ℝ)) := by
  let S := (P ×ˢ P) ×ˢ (P ×ˢ P)
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun v =>
    ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2)
  have hmap : ∀ v ∈ S, f v ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) := by
    rintro ⟨⟨p, q⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hpq, hrs⟩ := mem_product.mp hv
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hr, hs⟩ := mem_product.mp hrs
    have := hP p hp
    have := hP q hq
    have := hP r hr
    have := hP s hs
    apply mem_Icc.mpr
    dsimp [f]
    omega
  have he := minor_arc_fiber_sum S (Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) f
    (fun n => minorArcGeometricBound ((b - a : ℕ) : ℝ) (α * (n : ℝ)))
    (Finset.addEnergy P P : ℝ) hmap
    (fun n _ => minor_arc_geometric_nonneg (Nat.cast_nonneg _) _)
    (fun n _ => by
      have hh := (Nat.cast_le (α := ℝ)).mpr (minor_arc_prime_shifted_fiber P n)
      simpa only [S, f] using hh)
  apply (minor_arc_prime_fourth P c hc α a b).trans
  convert he using 1
  dsimp [S, f]
  simp only [sum_product]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  congr 1
  push_cast
  ring

end TwoPointCorrelations

end OAI
