import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.LowProjection

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

noncomputable def firstFiber {A : Type*} {n : ℕ} (f : (Fin (n+1) → A) → ℂ)
    (z : (Fin n → A) × A) : ℂ := f (Fin.cons z.2 z.1)

lemma firstFiber_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ} (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    MemLp (firstFiber f) 2 ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  change MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2 _
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)

lemma lowProjection_density_pauli {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (s : Finset ι) (x : A) :
    ((n+1:ℕ):ℝ) * (∫ y : Fin n → A, ‖lowProjection (μ := μ) v s (firstFiber f) (y,x)‖^2
      ∂(Measure.pi fun _ => μ)) ≤
      (∑ i ∈ s, ‖v i x‖^2) * (∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) := by
  have H := contraction_pauli f hf ha (lowOrbital v s x) (lowOrbital_memLp v hv s x)
  rw [lowOrbital_sq v hv ho] at H
  have he := lowProjection_eq_contract v hv s (firstFiber_memLp hf) x
  have he' : (∫ y : Fin n → A, ‖lowProjection (μ := μ) v s (firstFiber f) (y,x)‖^2
      ∂(Measure.pi fun _ => μ)) =
      ∫ y : Fin n → A, ‖fiberContract (μ := μ) (lowOrbital v s x) (firstFiber f) y‖^2
        ∂(Measure.pi fun _ => μ) := integral_congr_ae (he.fun_comp fun z => ‖z‖^2)
  rw [he']
  exact H

lemma norm_sq_le_two_norm_sq_add_sub (a b : ℂ) :
    ‖a‖^2 ≤ 2*‖b‖^2 + 2*‖a-b‖^2 := by
  have h : ‖a‖ ≤ ‖b‖ + ‖a-b‖ := by
    simpa only [add_sub_cancel] using norm_add_le b (a-b)
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a-b), sq_nonneg (‖b‖-‖a-b‖)]

lemma fiber_norm_sq_split {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x‖^2 ∂μ) ≤ 2*(∫ x, ‖g x‖^2 ∂μ) + 2*(∫ x, ‖f x-g x‖^2 ∂μ) := by
  have hi : Integrable (fun x => ‖f x-g x‖^2) μ := (hf.sub hg).norm.integrable_sq
  calc
    _ ≤ ∫ x, 2*‖g x‖^2 + 2*‖f x-g x‖^2 ∂μ :=
      integral_mono hf.norm.integrable_sq
        ((hg.norm.integrable_sq.const_mul 2).add (hi.const_mul 2))
        (fun x => norm_sq_le_two_norm_sq_add_sub (f x) (g x))
    _ = _ := by rw [integral_add (hg.norm.integrable_sq.const_mul 2)
        (hi.const_mul 2), integral_const_mul, integral_const_mul]

end Coulomb

end
end

end OAI
