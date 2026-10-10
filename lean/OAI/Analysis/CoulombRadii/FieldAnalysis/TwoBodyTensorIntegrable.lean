import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PermOrCompSwapOffTwo

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

lemma two_body_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ))
    (p q : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j) *
      (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k))) (Measure.pi fun _ => μ) := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact pair_weight_tensor_integrable i j hij (fun k a => star (v (p k) a) * v (q k) a) w
    (fun k => (hv (p k)).star.integrable_mul (hv (q k))) (hw _ _ _ _)

lemma two_body_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (p q : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    (∫ x : Fin n → A, w (x i) (x j) *
      (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k)) ∂(Measure.pi fun _ => μ)) =
      (∫ xy : A × A, w xy.1 xy.2 *
        ((star (v (p i) xy.1) * v (q i) xy.1) * (star (v (p j) xy.2) * v (q j) xy.2))
          ∂(μ.prod μ)) * ∏ k ∈ (Finset.univ.erase i).erase j,
            if p k = q k then (1:ℂ) else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [pair_weight_tensor_integral i j hij (fun k a => star (v (p k) a) * v (q k) a) w]
  simp_rw [ho]

lemma determinant_two_body_expansion {A : Type*} {n : ℕ}
    (v : Fin n → A → ℂ) (w : A → A → ℂ) (x : Fin n → A) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave v x) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j) *
            (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k)) := by
  rw [determinant_bilinear_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma determinant_two_body_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ)) :
    Integrable (fun x : Fin n → A => (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave v x)) (Measure.pi fun _ => μ) := by
  simp_rw [determinant_two_body_expansion]
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro q _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm

lemma determinant_two_body_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ)) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave v x) ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℂ) * ∑ i, ∑ j,
        ((∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v i xy.1) * (star (v j xy.2) * v j xy.2)) ∂(μ.prod μ)) -
        (∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v j xy.1) * (star (v j xy.2) * v i xy.2)) ∂(μ.prod μ))) := by
  let F (p q : Equiv.Perm (Fin n)) (i j : Fin n) (x : Fin n → A) : ℂ :=
    w (x i) (x j) * (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k))
  let c (p q : Equiv.Perm (Fin n)) : ℂ := star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ))
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x) (Measure.pi fun _ => μ) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j hj =>
      two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm))
  have hj (p : Equiv.Perm (Fin n)) : Integrable
      (fun x => ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x)
      (Measure.pi fun _ => μ) := integrable_finsetSum _ (fun q _ => (hi p q).const_mul _)
  calc
    _ = ∫ x : Fin n → A, ∑ p, ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x
        ∂(Measure.pi fun _ => μ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact determinant_two_body_expansion v w x
    _ = ∑ p, ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x : Fin n → A, F p q i j x ∂(Measure.pi fun _ => μ) := by
      rw [integral_finsetSum _ (fun p _ => hj p)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_finsetSum _ (fun q _ => (hi p q).const_mul _)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j hj => two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j hj =>
        two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm)
    _ = _ := by
      have H := slater_two_body_trace_algebra (fun a b c d =>
        ∫ xy : A × A, w xy.1 xy.2 * ((star (v a xy.1) * v c xy.1) *
          (star (v b xy.2) * v d xy.2)) ∂(μ.prod μ))
      rw [← H]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact two_body_tensor_integral v w ho p q i j (Finset.mem_erase.mp hj).1.symm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
