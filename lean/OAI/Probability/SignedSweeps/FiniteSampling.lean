import OAI.Probability.SignedSweeps.TupleNorm

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (𝕜 : Type*) [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {A B : Type*} [Fintype A] [Fintype B]

def finiteMean (f : A → E) : E := (Fintype.card A : 𝕜)⁻¹ • ∑ x, f x

lemma finiteMean_congr {f g : A → E} (h : ∀ x, f x = g x) :
    finiteMean 𝕜 f = finiteMean 𝕜 g := by unfold finiteMean; simp only [h]

lemma finiteMean_equiv (e : A ≃ B) (f : B → E) :
    finiteMean 𝕜 (fun x => f (e x)) = finiteMean 𝕜 f := by
  rw [finiteMean, finiteMean, Fintype.card_congr e, e.sum_comp]

lemma finiteMean_const [CharZero 𝕜] [Nonempty A] (x : E) : finiteMean 𝕜 (fun _ : A => x) = x := by
  rw [finiteMean, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

lemma finiteMean_prod (f : A × B → E) :
    finiteMean 𝕜 f = finiteMean 𝕜 (fun a => finiteMean 𝕜 (fun b => f (a,b))) := by
  simp only [finiteMean, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.smul_sum, smul_smul, mul_comm]

lemma linearMap_finiteMean {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (T : E →ₗ[𝕜] F) (f : A → E) :
    T (finiteMean 𝕜 f) = finiteMean 𝕜 (fun a => T (f a)) := by
  simp only [finiteMean, map_smul, map_sum]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {𝕜 R : Type*} [Field 𝕜] [CharZero 𝕜] [Ring R] [Algebra 𝕜 R]

lemma finiteMean_reverse_prod (t : ℕ) (A : Fin t → Type*) [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (f : ∀ i, A i → R) :
    finiteMean 𝕜 (fun a : ∀ i, A i => ((List.ofFn fun i => f i (a i)).reverse).prod) =
      ((List.ofFn fun i => finiteMean 𝕜 (f i)).reverse).prod := by
  induction t with
  | zero =>
    simp only [List.ofFn_zero, List.reverse_nil, List.prod_nil]
    exact finiteMean_const 𝕜 1
  | succ t ih =>
    rw [← finiteMean_equiv 𝕜 (Fin.consEquiv A), finiteMean_prod]
    have hc (a : A 0) (b : ∀ i : Fin t, A i.succ) :
        ((List.ofFn fun i => f i (Fin.consEquiv A (a,b) i)).reverse).prod =
          ((List.ofFn fun i : Fin t => f i.succ (b i)).reverse).prod * f 0 a := by
      rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    simp only [hc]
    have hr (a : A 0) :
        finiteMean 𝕜 (fun b : ∀ i : Fin t, A i.succ =>
          ((List.ofFn fun i : Fin t => f i.succ (b i)).reverse).prod * f 0 a) =
          ((List.ofFn fun i : Fin t => finiteMean 𝕜 (f i.succ)).reverse).prod * f 0 a := by
      change finiteMean 𝕜 (fun b : ∀ i : Fin t, A i.succ =>
        LinearMap.mulRight 𝕜 (f 0 a)
          (((List.ofFn fun i : Fin t => f i.succ (b i)).reverse).prod)) = _
      rw [← linearMap_finiteMean, ih]
      rfl
    simp only [hr]
    change finiteMean 𝕜 (fun a : A 0 =>
      LinearMap.mulLeft 𝕜
        (((List.ofFn fun i : Fin t => finiteMean 𝕜 (f i.succ)).reverse).prod)
        (f 0 a)) = _
    rw [← linearMap_finiteMean]
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton]
    rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SweepSettings (d : ℕ) := ∀ i : Fin d, coordinateSubgroup d i

def sampleSweep (d : ℕ) (a : SweepSettings d) : SymmetricGroup (2 ^ d) :=
  ((List.ofFn fun i => (a i).1).reverse).prod

lemma representation_sampleSweep_average {𝕜 E : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (d : ℕ) (ρ : Representation 𝕜 (SymmetricGroup (2 ^ d)) E) :
    finiteMean 𝕜 (fun a : SweepSettings d => ρ (sampleSweep d a)) =
      ((List.ofFn fun i : Fin d => (Fintype.card (coordinateSubgroup d i) : 𝕜)⁻¹ •
        ∑ g : coordinateSubgroup d i, ρ g.1).reverse).prod := by
  have he (a : SweepSettings d) : ρ (sampleSweep d a) =
      ((List.ofFn fun i : Fin d => ρ (a i).1).reverse).prod := by
    simp only [sampleSweep, map_list_prod, List.map_reverse, List.map_ofFn, Function.comp_def]
  simp only [he]
  exact finiteMean_reverse_prod d (fun i => coordinateSubgroup d i) (fun i g => ρ g.1)

lemma sweepOperator_eq_sampleMean {d : ℕ} (lam : Partition (2 ^ d)) :
    sweepOperator lam = finiteMean ℂ (fun a : SweepSettings d => spechtRepresentation lam (sampleSweep d a)) :=
  (representation_sampleSweep_average d (spechtRepresentation lam)).symm

lemma tupleSweep_eq_sampleMean (I : Type*) [Fintype I] (d : ℕ) :
    tupleSweep I d = finiteMean ℂ (fun a : SweepSettings d => tupleRepresentation I (2 ^ d) (sampleSweep d a)) :=
  (representation_sampleSweep_average d (tupleRepresentation I (2 ^ d))).symm

lemma subsetSweep_eq_sampleMean (d : ℕ) :
    subsetSweep d = finiteMean ℝ (fun a : SweepSettings d => subsetRepresentation (Fin (2 ^ d)) (sampleSweep d a)) :=
  (representation_sampleSweep_average d (subsetRepresentation (Fin (2 ^ d)))).symm

end SignedSweeps
end

end OAI
