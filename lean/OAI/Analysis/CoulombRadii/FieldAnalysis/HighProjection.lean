import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.FirstFiber

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

section
variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

omit [MeasurableSpace B] [SigmaFinite μ] in
include hv ho in
lemma fiberContract_lowProjection (s : Finset ι) (f : B × A → ℂ) (a : ι) (y : B) :
    fiberContract (μ := μ) (v a) (lowProjection (μ := μ) v s f) y =
      if a ∈ s then fiberContract (μ := μ) (v a) f y else 0 := by
  classical
  dsimp only [lowProjection, fiberContract]
  rw [show (fun x => star (v a x) * ∑ i ∈ s,
        (∫ z, star (v i z) * f (y,z) ∂μ) * v i x) =
      (fun x => ∑ i ∈ s, (∫ z, star (v i z) * f (y,z) ∂μ) * (star (v a x) * v i x)) from by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [integral_finsetSum s (fun i _ => (integrable_star_mul (hv a) (hv i)).const_mul _)]
  simp only [integral_const_mul, ho, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

noncomputable def highProjection (s : Finset ι) (f : B × A → ℂ) : B × A → ℂ :=
  f - lowProjection (μ := μ) v s f

include hv in
lemma highProjection_memLp (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (highProjection (μ := μ) v s f) 2 (ν.prod μ) := by
  have hp : MemLp (lowProjection (μ := μ) v s f) 2 (ν.prod μ) :=
    lowProjection_memLp v hv s hf
  change MemLp (f - lowProjection (μ := μ) v s f) 2 (ν.prod μ)
  exact hf.sub hp

include hv ho in
lemma fiberContract_highProjection (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) (a : ι) :
    fiberContract (μ := μ) (v a) (highProjection (μ := μ) v s f) =ᵐ[ν]
      fun y => if a ∈ s then 0 else fiberContract (μ := μ) (v a) f y := by
  classical
  filter_upwards [memLp_fiber_ae hf] with y hy
  have hp : MemLp (fun x => lowProjection (μ := μ) v s f (y,x)) 2 μ :=
    orbital_sum_memLp v hv s (fun i => fiberContract (μ := μ) (v i) f y)
  change (∫ x, star (v a x) * (f (y,x) - lowProjection (μ := μ) v s f (y,x)) ∂μ) = _
  simp only [mul_sub]
  rw [integral_sub (integrable_star_mul (hv a) hy) (integrable_star_mul (hv a) hp)]
  change fiberContract (μ := μ) (v a) f y -
    fiberContract (μ := μ) (v a) (lowProjection (μ := μ) v s f) y = _
  rw [fiberContract_lowProjection v hv ho]
  split_ifs <;> simp only [sub_self, sub_zero]

include hv ho in
lemma fiberContract_finite_bessel (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) :
    ∑ i ∈ s, (∫ y, ‖fiberContract (μ := μ) (v i) f y‖^2 ∂ν) ≤
      ∫ z, ‖f z‖^2 ∂(ν.prod μ) := by
  rw [← integral_finsetSum s (fun i _ => (fiberContract_memLp (hv i) hf).norm.integrable_sq)]
  rw [integral_prod _ hf.norm.integrable_sq]
  apply integral_mono_ae
    (integrable_finsetSum s (fun i _ => (fiberContract_memLp (hv i) hf).norm.integrable_sq))
    hf.norm.integrable_sq.integral_prod_left
  filter_upwards [memLp_fiber_ae hf] with y hy
  have H := (orbital_orthonormal v hv ho).sum_inner_products_le (s := s) (hy.toLp _)
  simpa only [inner_toLp_complex, norm_toLp_sq_complex, fiberContract] using H

include hv ho in
lemma fiberContract_norm_summable {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    Summable (fun i => ∫ y, ‖fiberContract (μ := μ) (v i) f y‖^2 ∂ν) :=
  summable_of_sum_le (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun s => fiberContract_finite_bessel v hv ho s hf)

end

noncomputable def firstUnfiber {A : Type*} {n : ℕ} (f : (Fin n → A) × A → ℂ)
    (x : Fin (n+1) → A) : ℂ := f (Fin.tail x, x 0)

lemma firstFiber_firstUnfiber {A : Type*} {n : ℕ} (f : (Fin n → A) × A → ℂ) :
    firstFiber (firstUnfiber f) = f := by
  funext z
  simp only [firstFiber, firstUnfiber, Fin.tail_cons, Fin.cons_zero]

lemma firstUnfiber_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} {f : (Fin n → A) × A → ℂ}
    (hf : MemLp f 2 ((Measure.pi fun _ : Fin n => μ).prod μ)) :
    MemLp (firstUnfiber f) 2 (Measure.pi fun _ => μ) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have heq : ∀ x : Fin (n+1) → A, e x = (Fin.tail x, x 0) := by
    intro x
    rfl
  change MemLp (fun x : Fin (n+1) → A => f (Fin.tail x, x 0)) 2 (Measure.pi fun _ => μ)
  simpa only [Function.comp_def, heq] using hf.comp_measurePreserving he

lemma firstUnfiber_norm_sq {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} (f : (Fin n → A) × A → ℂ) :
    (∫ x, ‖firstUnfiber f x‖^2 ∂(Measure.pi fun _ => μ)) =
      ∫ z, ‖f z‖^2 ∂((Measure.pi fun _ : Fin n => μ).prod μ) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  exact he.integral_comp' (fun z => ‖f z‖^2)

lemma scalarCoefficient_congr {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    {n : ℕ} {f g : (Fin n → A) → ℂ} (he : f =ᵐ[Measure.pi fun _ => μ] g)
    (v : ι → A → ℂ) (b : Fin n → ι) :
    scalarCoefficient (μ := μ) f v b = scalarCoefficient (μ := μ) g v b := by
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include hv ho in
lemma scalarCoefficient_highFirst {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (s : Finset ι) (b : Fin (n+1) → ι) :
    scalarCoefficient (μ := μ) (firstUnfiber (highProjection (μ := μ) v s (firstFiber f))) v b =
      if b 0 ∈ s then 0 else scalarCoefficient (μ := μ) f v b := by
  classical
  have hff := firstFiber_memLp hf
  have hh := highProjection_memLp v hv s hff
  have hu := firstUnfiber_memLp hh
  have hb : Fin.cons (b 0) (Fin.tail b) = b := by
    ext i
    exact Fin.cases rfl (fun j => rfl) i
  rw [← hb, scalarCoefficient_contract _ hu v hv, scalarCoefficient_contract f hf v hv]
  change scalarCoefficient (μ := μ)
    (fiberContract (μ := μ) (v (b 0)) (firstFiber (firstUnfiber
      (highProjection (μ := μ) v s (firstFiber f))))) v (Fin.tail b) = _
  rw [firstFiber_firstUnfiber]
  rw [scalarCoefficient_congr (fiberContract_highProjection v hv ho s hff (b 0))]
  by_cases hs : b 0 ∈ s
  · simp only [Fin.cons_zero, hs, ite_true, scalarCoefficient, mul_zero, integral_zero]
  · simp only [Fin.cons_zero, hs, ite_false]
    rfl

include hv ho in
lemma highProjection_norm_spectrum [Countable ι] (hc : CompleteOrbitals μ v)
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (s : Finset ι) :
    (∫ z, ‖highProjection (μ := μ) v s (firstFiber f) z‖^2
      ∂((Measure.pi fun _ : Fin n => μ).prod μ)) =
      ∑' b, if b 0 ∈ s then 0 else ‖scalarCoefficient (μ := μ) f v b‖^2 := by
  rw [← firstUnfiber_norm_sq]
  have hh := highProjection_memLp v hv s (firstFiber_memLp hf)
  rw [← scalarCoefficient_parseval _ (firstUnfiber_memLp hh) v hv ho hc]
  apply tsum_congr
  intro b
  rw [scalarCoefficient_highFirst v hv ho hf s b]
  split_ifs <;> norm_num

end Coulomb
open MeasureTheory Set Filter
open scoped ENNReal NNReal

end OAI
