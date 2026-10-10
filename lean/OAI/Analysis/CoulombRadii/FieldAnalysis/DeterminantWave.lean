import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.OrbitalHilbertBasis

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def determinantWave {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : ℂ := Matrix.det (fun i j => v i (x j))

lemma determinantWave_expansion {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : determinantWave v x =
    ∑ p : Equiv.Perm (Fin n), ((p.sign : ℤ) : ℂ) * ∏ i, v (p i) (x i) :=
  Matrix.det_apply' _

lemma determinantWave_permute {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (x : Fin n → A) :
    determinantWave v (x ∘ p) = ((p.sign : ℤ) : ℂ) * determinantWave v x := by
  exact Matrix.det_permute' p (fun i j => v i (x j))

lemma determinantWave_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) :
    MemLp (determinantWave v) 2 (Measure.pi fun _ : Fin n => μ) := by
  change MemLp (fun x => determinantWave v x) 2 _
  simp_rw [determinantWave_expansion]
  exact memLp_finsetSum _ (fun p _ => (scalarTensor_memLp v hv p).const_mul _)

lemma sign_star_mul {n : ℕ} (p : Equiv.Perm (Fin n)) :
    star (((p.sign : ℤ) : ℂ)) * (((p.sign : ℤ) : ℂ)) = 1 := by
  rcases Int.units_eq_one_or p.sign with h | h <;> simp [h]

lemma determinantWave_norm_sq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    (∫ x, ‖determinantWave v x‖^2 ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial := by
  let T (p : Equiv.Perm (Fin n)) : Lp ℂ 2 (Measure.pi fun _ : Fin n => μ) :=
    (scalarTensor_memLp v hv p).toLp (fun x : Fin n → A => ∏ i, v (p i) (x i))
  have hT : Orthonormal ℂ T := by
    rw [orthonormal_iff_ite]
    intro p q
    change inner ℂ ((scalarTensor_memLp v hv p).toLp _)
      ((scalarTensor_memLp v hv q).toLp _) = _
    rw [inner_toLp_complex]
    rw [scalarTensor_orthonormal v (fun i j => by
      by_cases h : i = j
      · simpa only [ite_eq_left h] using ho i j
      · simpa only [ite_eq_right h] using ho i j)]
    by_cases h : p = q
    · subst q; simp
    · have hfun : (p : Fin n → Fin n) ≠ q := fun he => h (Equiv.ext (congrFun he))
      simp only [ite_eq_right h, ite_eq_right hfun]
  let hD := determinantWave_memLp v hv
  have hsum : hD.toLp (determinantWave v) =
      ∑ p, (((p.sign : ℤ) : ℂ)) • T p := by
    apply Lp.ext
    filter_upwards [hD.coeFn_toLp, Lp.coeFn_fun_finsetSum
      (s := Finset.univ) (f := fun p : Equiv.Perm (Fin n) => (((p.sign : ℤ) : ℂ)) • T p),
      ae_all_iff.mpr (fun p : Equiv.Perm (Fin n) =>
        (scalarTensor_memLp v hv p).coeFn_toLp),
      ae_all_iff.mpr (fun p : Equiv.Perm (Fin n) =>
        Lp.coeFn_smul (((p.sign : ℤ) : ℂ)) (T p))] with x hx hsum ht hsmul
    rw [hx, hsum, determinantWave_expansion]
    apply Finset.sum_congr rfl
    intro p _
    rw [hsmul p]
    simp only [Pi.smul_apply, smul_eq_mul, T, ht p]
  apply Complex.ofReal_injective
  rw [← norm_toLp_sq_complex hD]
  calc
    (↑(‖hD.toLp (determinantWave v)‖^2) : ℂ) =
        inner ℂ (hD.toLp (determinantWave v)) (hD.toLp (determinantWave v)) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∑ p : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((p.sign : ℤ) : ℂ)) := by
      rw [hsum]
      exact hT.inner_sum _ _ Finset.univ
    _ = ↑(n.factorial : ℝ) := by
      simp only [sign_star_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      norm_cast
      simpa only [Fintype.card_fin] using (Fintype.card_perm (α := Fin n))

noncomputable def slaterWave {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : ℂ := (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * determinantWave v x

lemma slaterWave_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) :
    MemLp (slaterWave v) 2 (Measure.pi fun _ : Fin n => μ) :=
  (determinantWave_memLp v hv).const_mul _

lemma slaterWave_antisymmetric {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {n : ℕ} (v : Fin n → A → ℂ) : ProductAntisymmetric (μ := μ) (slaterWave v) := by
  intro p
  filter_upwards [] with x
  simp only [slaterWave, determinantWave_permute]
  ring

lemma slaterWave_normalized {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    (∫ x, ‖slaterWave v x‖^2 ∂(Measure.pi fun _ : Fin n => μ)) = 1 := by
  have hn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), integral_const_mul,
    determinantWave_norm_sq v hv ho, inv_pow, Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ hn.ne'

lemma perm_eq_of_eq_off {α : Type*} (p q : Equiv.Perm α) (i : α)
    (h : ∀ j, j ≠ i → p j = q j) : p = q := by
  apply Equiv.ext
  intro j
  by_cases hj : j = i
  · subst j
    by_cases hk : q.symm (p i) = i
    · simpa only [hk] using (q.apply_symm_apply (p i)).symm
    · have he : p (q.symm (p i)) = p i := (h _ hk).trans (q.apply_symm_apply _)
      exact False.elim (hk (p.injective he))
  · exact h j hj

lemma permutation_minor_orthogonality {α : Type*} [Fintype α] [DecidableEq α]
    (p q : Equiv.Perm α) (i : α) :
    (∏ j ∈ Finset.univ.erase i, if p j = q j then (1 : ℂ) else 0) =
      if p = q then 1 else 0 := by
  classical
  by_cases h : p = q
  · subst q; simp
  · rw [ite_eq_right h]
    obtain ⟨j,hji,hj⟩ : ∃ j, j ≠ i ∧ p j ≠ q j := by
      by_contra he
      apply h
      apply perm_eq_of_eq_off p q i
      intro j hji
      by_contra hj
      exact he ⟨j,hji,hj⟩
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩) (ite_eq_right hj)

lemma slater_one_body_trace_algebra {n : ℕ} (K : Fin n → Fin n → ℂ) :
    (∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
      star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, K (p i) (q i) *
          ∏ j ∈ Finset.univ.erase i, if p j = q j then (1 : ℂ) else 0) =
      (n.factorial : ℂ) * ∑ i, K i i := by
  classical
  simp_rw [permutation_minor_orthogonality]
  have hp (p : Equiv.Perm (Fin n)) :
      (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, K (p i) (q i) * (if p = q then 1 else 0)) = ∑ i, K i i := by
    rw [Finset.sum_eq_single p]
    · simp only [sign_star_mul, one_mul]
      simpa only [ite_true, mul_one] using Equiv.sum_comp p (fun i => K i i)
    · intro q _ hq
      simp only [ite_eq_right hq.symm, mul_zero, Finset.sum_const_zero]
    · simp
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

lemma tensor_weight_factor {A : Type*} {n : ℕ} (f : Fin n → A → ℂ)
    (w : A → ℂ) (i : Fin n) (x : Fin n → A) :
    w (x i) * ∏ j, f j (x j) =
      ∏ j, (if j = i then w (x j) * f j (x j) else f j (x j)) := by
  calc
    w (x i) * ∏ j, f j (x j) =
        (w (x i) * f i (x i)) * ∏ j ∈ Finset.univ.erase i, f j (x j) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)]
      ring
    _ = (if i = i then w (x i) * f i (x i) else f i (x i)) *
        ∏ j ∈ Finset.univ.erase i, if j = i then w (x j) * f j (x j) else f j (x j) := by
      simp only [ite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact (ite_eq_right (Finset.mem_erase.mp hj).1).symm
    _ = _ := Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then w (x j) * f j (x j) else f j (x j)) (Finset.mem_univ i)

lemma weighted_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (f : Fin n → A → ℂ) (w : A → ℂ) (i : Fin n)
    (hf : ∀ j, Integrable (f j) μ) (hwi : Integrable (fun a => w a * f i a) μ) :
    Integrable (fun x : Fin n → A => w (x i) * ∏ j, f j (x j))
      (Measure.pi fun _ => μ) := by
  simp_rw [tensor_weight_factor]
  apply Integrable.fintype_prod (f := fun j a => if j = i then w a * f j a else f j a)
  intro j
  by_cases h : j = i
  · subst j; simpa only [ite_true] using hwi
  · simpa only [ite_eq_right h] using hf j

lemma weighted_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (f : Fin n → A → ℂ) (w : A → ℂ) (i : Fin n) :
    (∫ x : Fin n → A, w (x i) * ∏ j, f j (x j) ∂(Measure.pi fun _ => μ)) =
      (∫ a, w a * f i a ∂μ) * ∏ j ∈ Finset.univ.erase i, ∫ a, f j a ∂μ := by
  simp_rw [tensor_weight_factor]
  rw [integral_fintype_prod_eq_prod (f := fun j a => if j = i then w a * f j a else f j a) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

lemma one_body_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (∫ x : Fin n → A, w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j))
      ∂(Measure.pi fun _ => μ)) =
      (∫ a, w a * (star (v (p i) a) * v (q i) a) ∂μ) *
        ∏ j ∈ Finset.univ.erase i, if p j = q j then (1 : ℂ) else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [weighted_tensor_integral (fun j a => star (v (p j) a) * v (q j) a) w i]
  simp_rw [ho]

lemma one_body_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * v j a)) μ)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    Integrable (fun x : Fin n → A =>
      w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j)))
      (Measure.pi fun _ => μ) := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact weighted_tensor_integrable (μ := μ) (fun j a => star (v (p j) a) * v (q j) a) w i
    (fun j => (hv (p j)).star.integrable_mul (hv (q j))) (hw _ _)

lemma determinant_bilinear_expansion {A : Type*} {n : ℕ}
    (v u : Fin n → A → ℂ) (x y : Fin n → A) :
    star (determinantWave v x) * determinantWave u y =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          (star (∏ i, v (p i) (x i)) * ∏ i, u (q i) (y i)) := by
  simp only [determinantWave_expansion, star_sum, star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma determinant_one_body_expansion {A : Type*} {n : ℕ}
    (v : Fin n → A → ℂ) (w : A → ℂ) (x : Fin n → A) :
    (∑ i, w (x i)) * (star (determinantWave v x) * determinantWave v x) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j)) := by
  rw [determinant_bilinear_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma determinant_one_body_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * v j a)) μ) :
    Integrable (fun x : Fin n → A =>
      (∑ i, w (x i)) * (star (determinantWave v x) * determinantWave v x))
      (Measure.pi fun _ => μ) := by
  simp_rw [determinant_one_body_expansion]
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro q _
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun i _ => one_body_tensor_integrable v w hv hw p q i)

lemma determinant_one_body_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * v j a)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i)) *
      (star (determinantWave v x) * determinantWave v x) ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℂ) * ∑ i, ∫ a, w a * (star (v i a) * v i a) ∂μ := by
  let F (p q : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) : ℂ :=
    w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j))
  let c (p q : Equiv.Perm (Fin n)) : ℂ :=
    star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ))
  have hi (p q : Equiv.Perm (Fin n)) : Integrable (fun x => ∑ i, F p q i x)
      (Measure.pi fun _ => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => one_body_tensor_integrable v w hv hw p q i)
  have hj (p : Equiv.Perm (Fin n)) : Integrable (fun x => ∑ q, c p q * ∑ i, F p q i x)
      (Measure.pi fun _ => μ) :=
    integrable_finsetSum Finset.univ (fun q _ => (hi p q).const_mul (c p q))
  calc
    _ = ∫ x : Fin n → A, ∑ p, ∑ q, c p q * ∑ i, F p q i x
        ∂(Measure.pi fun _ => μ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact determinant_one_body_expansion v w x
    _ = ∑ p, ∑ q, c p q * ∑ i, ∫ x : Fin n → A, F p q i x
        ∂(Measure.pi fun _ => μ) := by
      rw [integral_finsetSum _ (fun p _ => hj p)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_finsetSum _ (fun q _ => (hi p q).const_mul (c p q))]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_const_mul, integral_finsetSum _
        (fun i _ => one_body_tensor_integrable v w hv hw p q i)]
    _ = _ := by
      simp only [F, one_body_tensor_integral v w ho]
      exact slater_one_body_trace_algebra (fun i j => ∫ a, w a * (star (v i a) * v j a) ∂μ)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
