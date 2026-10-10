import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.HilbertBasisContaining

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma tsum_fixed_zero {ι : Type*} {n : ℕ} (f : (Fin (n+1) → ι) → ℝ) (a : ι) :
    (∑' b : Fin (n+1) → ι, if b 0 = a then f b else 0) =
      ∑' c : Fin n → ι, f (Fin.cons a c) := by
  have hinj : Function.Injective (fun c : Fin n → ι => (Fin.cons a c : Fin (n+1) → ι)) := by
    intro c d h
    funext i
    exact congrFun h i.succ
  have hs : Function.support (fun b : Fin (n+1) → ι => if b 0 = a then f b else 0) ⊆
      Set.range (fun c : Fin n → ι => (Fin.cons a c : Fin (n+1) → ι)) := by
    intro b hb
    have ha : b 0 = a := by
      by_contra hh
      exact hb (ite_eq_right hh)
    exact ⟨Fin.tail b, by simpa only [← ha] using Fin.cons_self_tail b⟩
  simpa only [Fin.cons_zero, ite_true] using (hinj.tsum_eq hs).symm

lemma basis_contraction_pauli {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (a : ι) :
    ((n+1 : ℕ) : ℝ) * (∫ y : Fin n → A,
      ‖fiberContract (μ := μ) (v a) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2
        ∂(Measure.pi fun _ => μ)) ≤ ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have hp := (scalarCoefficient_antisymmetric ha v).pauli_bound
    (scalarCoefficient_summable f hf v hv ho) a 0
  rw [scalarCoefficient_parseval f hf v hv ho hc, tsum_fixed_zero] at hp
  simp only [scalarCoefficient_contract f hf v hv] at hp
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  have hf' : MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2
      ((Measure.pi fun _ : Fin n => μ).prod μ) := by
    simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)
  rw [scalarCoefficient_parseval _ (fiberContract_memLp (hv a) hf') v hv ho hc] at hp
  exact hp

lemma unit_contraction_pauli {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : A → ℂ) (hv : MemLp v 2 μ) (hv1 : ∫ x, ‖v x‖^2 ∂μ = 1) :
    ((n+1 : ℕ) : ℝ) * (∫ y : Fin n → A,
      ‖fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2
        ∂(Measure.pi fun _ => μ)) ≤ ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have hn : ‖hv.toLp v‖ = 1 := by
    have hs := norm_toLp_sq_complex hv
    rw [hv1] at hs
    nlinarith [norm_nonneg (hv.toLp v)]
  obtain ⟨w, b, i, hbi, hb⟩ := exists_hilbertBasis_containing (hv.toLp v) hn
  have : Countable w := orthonormal_subtype_countable (by
    simpa only [hb] using b.orthonormal)
  have ho (j k : w) : (∫ a, star (b j a) * b k a ∂μ) = if j = k then (1:ℂ) else 0 := by
    rw [← inner_toLp_complex (Lp.memLp (b j)) (Lp.memLp (b k))]
    simp only [Lp.toLp_coeFn]
    exact (orthonormal_iff_ite.mp b.orthonormal) j k
  have H := basis_contraction_pauli f hf ha (fun j => b j) (fun j => Lp.memLp (b j))
    (by intro j k; by_cases h : j = k <;>
      simpa only [h, ite_true, ite_false] using ho j k) (HilbertBasis_completeOrbitals b) i
  have he : (fun a => b i a) =ᵐ[μ] v := by
    simpa only [hbi] using hv.coeFn_toLp
  have hc (y : Fin n → A) :
      fiberContract (μ := μ) (b i) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y =
      fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y := by
    unfold fiberContract
    apply integral_congr_ae
    filter_upwards [he] with a ha
    rw [ha]
  simpa only [hc] using H

lemma fiberContract_const_mul {A B : Type*} [MeasurableSpace A] {μ : Measure A}
    (c : ℂ) (v : A → ℂ) (f : B × A → ℂ) (y : B) :
    fiberContract (μ := μ) (fun x => c * v x) f y = star c * fiberContract (μ := μ) v f y := by
  unfold fiberContract
  rw [show (fun a => star (c * v a) * f (y,a)) =
    (fun a => star c * (star (v a) * f (y,a))) from by
      funext a; simp only [star_mul]; ring, integral_const_mul]

lemma contraction_pauli {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f) (v : A → ℂ) (hv : MemLp v 2 μ) :
    ((n+1 : ℕ) : ℝ) * (∫ y : Fin n → A,
      ‖fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2
        ∂(Measure.pi fun _ => μ)) ≤
      (∫ x, ‖v x‖^2 ∂μ) * (∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ)) := by
  let t : ℝ := ‖hv.toLp v‖
  have ht : 0 ≤ t := norm_nonneg _
  have ht2 : t^2 = ∫ x, ‖v x‖^2 ∂μ := norm_toLp_sq_complex hv
  by_cases hz : t = 0
  · have hv0 : hv.toLp v = 0 := norm_eq_zero.mp hz
    have hev : v =ᵐ[μ] 0 := hv.coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).mp hv0)
    have hc (y : Fin n → A) :
        fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y = 0 := by
      unfold fiberContract
      apply integral_eq_zero_of_ae
      filter_upwards [hev] with x hx
      simp [hx]
    simp only [← ht2, hz, zero_pow (by decide : 2 ≠ 0), zero_mul, hc, norm_zero, integral_zero,
      mul_zero, le_refl]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    let u : A → ℂ := fun x => (t⁻¹ : ℂ) * v x
    have hu : MemLp u 2 μ := hv.const_mul _
    have hu1 : (∫ x, ‖u x‖^2 ∂μ) = 1 := by
      simp only [u, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
        mul_pow, integral_const_mul, ← ht2]
      field_simp
    have H := unit_contraction_pauli f hf ha u hu hu1
    simp only [u, fiberContract_const_mul, norm_mul, norm_star, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, mul_pow, integral_const_mul] at H
    rw [← ht2]
    have H' := mul_le_mul_of_nonneg_left H (sq_nonneg t)
    have he : t^2 * (((n+1:ℕ):ℝ) * ((t⁻¹)^2 *
        (∫ y : Fin n → A, ‖fiberContract (μ := μ) v
          (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2 ∂(Measure.pi fun _ => μ)))) =
        ((n+1:ℕ):ℝ) * (∫ y : Fin n → A, ‖fiberContract (μ := μ) v
          (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2 ∂(Measure.pi fun _ => μ)) := by
      field_simp
    rwa [he] at H'

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include ho in
lemma orbital_orthonormal : Orthonormal ℂ (fun i => (hv i).toLp (v i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_toLp_complex]
  exact ho i j

include hv in
lemma orbital_sum_memLp (s : Finset ι) (c : ι → ℂ) :
    MemLp (fun x => ∑ i ∈ s, c i * v i x) 2 μ :=
  memLp_finsetSum s (fun i _ => (hv i).const_mul (c i))

lemma orbital_sum_toLp (s : Finset ι) (c : ι → ℂ) :
    (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) =
      ∑ i ∈ s, c i • (hv i).toLp (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert a s ha ih =>
    have he : (fun x => ∑ i ∈ insert a s, c i * v i x) =
        (fun x => c a * v a x) + (fun x => ∑ i ∈ s, c i * v i x) := by
      funext x
      simp [Finset.sum_insert ha]
    rw [show (orbital_sum_memLp v hv (insert a s) c).toLp _ =
      ((hv a).const_mul (c a)).toLp (fun x => c a * v a x) +
      (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) from by
        simpa only [he] using ((hv a).const_mul (c a)).toLp_add
          (orbital_sum_memLp v hv s c)]
    rw [ih, Finset.sum_insert ha]
    congr 1

include hv ho in
lemma orbital_sum_sq (s : Finset ι) (c : ι → ℂ) :
    (∫ x, ‖∑ i ∈ s, c i * v i x‖^2 ∂μ) = ∑ i ∈ s, ‖c i‖^2 := by
  rw [← norm_toLp_sq_complex (orbital_sum_memLp v hv s c), orbital_sum_toLp v hv s c]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (↑(‖∑ i ∈ s, c i • (hv i).toLp (v i)‖^2) : ℂ) =
        inner ℂ (∑ i ∈ s, c i • (hv i).toLp (v i))
          (∑ i ∈ s, c i • (hv i).toLp (v i)) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∑ i ∈ s, star (c i) * c i := (orbital_orthonormal v hv ho).inner_sum c c s
    _ = ∑ i ∈ s, (↑(‖c i‖^2) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [starRingEnd_apply, Complex.ofReal_pow] using Complex.conj_mul' (c i)

noncomputable def lowOrbital (s : Finset ι) (x : A) (y : A) : ℂ :=
  ∑ i ∈ s, star (v i x) * v i y

include hv in
lemma lowOrbital_memLp (s : Finset ι) (x : A) :
    MemLp (lowOrbital v s x) 2 μ := orbital_sum_memLp v hv s _

include hv ho in
lemma lowOrbital_sq (s : Finset ι) (x : A) :
    (∫ y, ‖lowOrbital v s x y‖^2 ∂μ) = ∑ i ∈ s, ‖v i x‖^2 := by
  simpa only [lowOrbital, norm_star] using orbital_sum_sq v hv ho s (fun i => star (v i x))

end Coulomb

end OAI
