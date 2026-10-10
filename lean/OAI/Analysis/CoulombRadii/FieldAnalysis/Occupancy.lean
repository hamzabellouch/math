import Mathlib
import OAI.Analysis.CoulombRadii.Packets.OrbitalKernel

namespace OAI

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable def occupancy (b : Bool) : ℝ := if b then 1 else 0
noncomputable def bernoulliWeight {ι : Type*} [Fintype ι] (lam : ι → ℝ) (w : ι → Bool) : ℝ :=
  ∏ i, if w i then lam i else 1-lam i
lemma bernoulliWeight_nonneg {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (hl : ∀ i, 0 ≤ lam i) (hu : ∀ i, lam i ≤ 1) (w : ι → Bool) :
    0 ≤ bernoulliWeight lam w := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact hl i
  · exact sub_nonneg.mpr (hu i)
lemma bernoulli_product_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (f : ι → Bool → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * ∏ i, f i (w i)) =
      ∏ i, ((1-lam i)*f i false+lam i*f i true) := by
  simp only [bernoulliWeight,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i b => (if b then lam i else 1-lam i)*f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]
lemma bernoulliWeight_sum {ι : Type*} [Fintype ι] (lam : ι → ℝ) :
    ∑ w : ι → Bool, bernoulliWeight lam w = 1 := by
  simpa using bernoulli_product_mean lam (fun _ _ => 1)
lemma bernoulli_forced_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (s : Finset ι) :
    (∑ w : ι → Bool, bernoulliWeight lam w * ∏ i ∈ s,occupancy (w i)) = ∏ i ∈ s,lam i := by
  have he (w : ι → Bool) : (∏ i ∈ s,occupancy (w i)) = ∏ i,if i ∈ s then occupancy (w i) else 1 := by
    rw [Finset.prod_ite]
    simp
  simp_rw [he]
  rw [bernoulli_product_mean lam (fun i b => if i ∈ s then occupancy b else 1)]
  have hp (i : ι) : (1-lam i)*(if i ∈ s then occupancy false else 1)+
      lam i*(if i ∈ s then occupancy true else 1) = if i ∈ s then lam i else 1 := by
    by_cases hs : i ∈ s <;> simp [hs,occupancy]
  simp_rw [hp]
  rw [Finset.prod_ite]
  simp
lemma bernoulli_one_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (i : ι) :
    (∑ w : ι → Bool,bernoulliWeight lam w*occupancy (w i)) = lam i := by
  simpa using bernoulli_forced_mean lam {i}
lemma bernoulli_two_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∑ w : ι → Bool,bernoulliWeight lam w*(occupancy (w i)*occupancy (w j))) = lam i*lam j := by
  simpa [hij] using bernoulli_forced_mean lam {i,j}
lemma bernoulli_linear_mean {ι : Type*} [Fintype ι] (lam a : ι → ℝ) :
    (∑ w : ι → Bool,bernoulliWeight lam w*(∑ i,occupancy (w i)*a i)) = ∑ i,lam i*a i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [←mul_assoc,←Finset.sum_mul,bernoulli_one_mean]
lemma bernoulli_pair_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (d : ι → ι → ℝ)
    (hd : ∀ i, d i i = 0) :
    (∑ w : ι → Bool,bernoulliWeight lam w*(∑ i,∑ j,occupancy (w i)*occupancy (w j)*d i j)) =
      ∑ i,∑ j,lam i*lam j*d i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [hd]
  · calc
      _ = (∑ w : ι → Bool,bernoulliWeight lam w*(occupancy (w i)*occupancy (w j)))*d i j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [bernoulli_two_mean lam hij]

noncomputable def occupiedIndex {ι : Type*} [Fintype ι] (w : ι → Bool) :
    Fin (Fintype.card {i // w i = true}) ↪ ι :=
  (Fintype.equivFin {i // w i = true}).symm.toEmbedding.trans (Function.Embedding.subtype _)

lemma sum_occupiedIndex {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (w : ι → Bool) (f : ι → R) :
    (∑ a, f (occupiedIndex w a)) = ∑ i, if w i then f i else 0 := by
  classical
  rw [show (∑ a, f (occupiedIndex w a)) = ∑ a : {i // w i = true}, f a by
    exact Equiv.sum_comp (Fintype.equivFin {i // w i = true}).symm (fun a => f a)]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => w i = true)) (by simp) f,
    Finset.sum_filter]

lemma sum_occupiedIndex_real {ι : Type*} [Fintype ι] (w : ι → Bool) (f : ι → ℝ) :
    (∑ a, f (occupiedIndex w a)) = ∑ i, occupancy (w i) * f i := by
  rw [sum_occupiedIndex]
  apply Finset.sum_congr rfl
  intro i _
  cases w i <;> simp [occupancy]

noncomputable def slaterPairEntry {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) (W : A → A → ℝ) (i j : ι) : ℝ :=
  (∫ xy : A × A, (W xy.1 xy.2 : ℂ) *
      ((star (v i xy.1)*v i xy.1)*(star (v j xy.2)*v j xy.2)) ∂(μ.prod μ)).re -
  (∫ xy : A × A, (W xy.1 xy.2 : ℂ) *
      ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2)) ∂(μ.prod μ)).re

lemma slaterPairEntry_self {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) (W : A → A → ℝ) (i : ι) : slaterPairEntry μ v W i i = 0 := by
  simp [slaterPairEntry]

lemma slaterWave_two_body_exact {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (W : A → A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ) *
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ)) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
      ‖slaterWave v x‖^2 ∂(Measure.pi fun _ => μ)) = ∑ i, ∑ j, slaterPairEntry μ v W i j := by
  have H := determinant_two_body_integral v (fun x y => (W x y : ℂ)) hv ho hW
  simp only [complex_star_mul_self, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    integral_complex_ofReal] at H
  have HR := congrArg Complex.re H
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum, Complex.sub_re] at HR
  have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have he (x : Fin n → A) : (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
      ‖slaterWave v x‖^2 = (n.factorial : ℝ)⁻¹ *
        ((∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) * ‖determinantWave v x‖^2) := by
    simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le]
    ring
  simp_rw [he]
  rw [integral_const_mul, HR, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  simp only [slaterPairEntry, complex_star_mul_self, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re]

lemma bernoulli_slater_pair_mean {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] (v : ι → A → ℂ) (W : A → A → ℝ)
    (lam : ι → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ) *
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ)) :
    (∑ w : ι → Bool, bernoulliWeight lam w *
      (∫ x : Fin (Fintype.card {i // w i = true}) → A,
        (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
        ‖slaterWave (fun a => v (occupiedIndex w a)) x‖^2 ∂(Measure.pi fun _ => μ))) =
      ∑ i, ∑ j, lam i * lam j * slaterPairEntry μ v W i j := by
  classical
  have he (w : ι → Bool) := slaterWave_two_body_exact
    (fun a => v (occupiedIndex w a)) W (fun a => hv _) (fun a b => by
      simp only [ho, (occupiedIndex w).injective.eq_iff])
    (fun a b c d => hW _ _ _ _)
  simp_rw [he]
  have hs (w : ι → Bool) :
      (∑ a, ∑ b, slaterPairEntry μ (fun a => v (occupiedIndex w a)) W a b) =
      ∑ i, ∑ j, occupancy (w i)*occupancy (w j)*slaterPairEntry μ v W i j := by
    change (∑ a, ∑ b, slaterPairEntry μ v W (occupiedIndex w a) (occupiedIndex w b)) = _
    rw [sum_occupiedIndex_real w (fun i => ∑ b, slaterPairEntry μ v W i (occupiedIndex w b))]
    simp_rw [sum_occupiedIndex_real, Finset.mul_sum, mul_assoc]
  simp_rw [hs]
  exact bernoulli_pair_mean lam _ (slaterPairEntry_self μ v W)
end Coulomb

end OAI
