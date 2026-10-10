import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalTensor

namespace OAI

/-! Actual L2 derivative-slot tensors and their exact kinetic matrix
compression to CAR one-body operators. Derivative families are concrete
functions with L2 hypotheses, so spatial partial derivatives can be used
directly without assuming a kinetic-energy matrix identity. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.OrbitalDerivative
open Laughlin FockSlaterTensor SlaterOccupation

private lemma basisTensor_substitution {Q n : ℕ} (S : Occupied Q n)
    (f : Laughlin.Configuration n Q → ℂ) :
    (∑ a, basisTensor S a * f a) =
      (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ *
        ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) * f (fun i => selection S (p i)) := by
  classical
  simp_rw [basisTensor_expansion, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def derivativeTensorValue {A : Type*} {Q n : ℕ} (v d : Fin (Q + 1) → A → ℂ)
    (ψ : State n Q) (slot : Fin n) (x : Fin n → A) : ℂ :=
  ∑ a : Laughlin.Configuration n Q, ψ a *
    Coulomb.slotTensor (fun j => v (a j)) (fun j => d (a j)) 1 slot x

def normalizedSlotWave {A : Type*} {Q n : ℕ} (v d : Fin (Q + 1) → A → ℂ)
    (S : Occupied Q n) (slot : Fin n) (x : Fin n → A) : ℂ :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ *
    Coulomb.slotDeterminant (selectedOrbitals v S) (selectedOrbitals d S) slot x

lemma derivativeTensorValue_basisTensor {A : Type*} {Q n : ℕ}
    (v d : Fin (Q + 1) → A → ℂ) (S : Occupied Q n) (slot : Fin n) (x : Fin n → A) :
    derivativeTensorValue v d (basisTensor S) slot x = normalizedSlotWave v d S slot x := by
  unfold derivativeTensorValue
  rw [basisTensor_substitution]
  rfl

lemma derivativeTensorValue_occupationTensor {A : Type*} {Q n : ℕ}
    (v d : Fin (Q + 1) → A → ℂ) (c : EuclideanSpace ℂ (Occupied Q n))
    (slot : Fin n) (x : Fin n → A) :
    derivativeTensorValue v d (occupationTensor c) slot x =
      ∑ S, c S * normalizedSlotWave v d S slot x := by
  unfold derivativeTensorValue occupationTensor
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← derivativeTensorValue_basisTensor v d S slot x]
  unfold derivativeTensorValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {Q n : ℕ}

lemma derivativeTensorValue_memLp (v d : Fin (Q + 1) → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ)
    (ψ : State n Q) (slot : Fin n) :
    MemLp (derivativeTensorValue v d ψ slot) 2 (Measure.pi fun _ => μ) := by
  exact memLp_finsetSum Finset.univ (fun a _ =>
    (Coulomb.slotTensor_memLp (fun j => v (a j)) (fun j => d (a j))
      (fun j => hv (a j)) (fun j => hd (a j)) 1 slot).const_mul (ψ a))

omit [MeasurableSpace A] in
lemma derivative_bilinear_expansion (v d e : Fin (Q + 1) → A → ℂ)
    (ψ φ : State n Q) (slot : Fin n) (x : Fin n → A) :
    star (derivativeTensorValue v d ψ slot x) * derivativeTensorValue v e φ slot x =
      ∑ a : Laughlin.Configuration n Q, ∑ b : Laughlin.Configuration n Q,
        (star (ψ a) * φ b) *
          (star (Coulomb.slotTensor (fun j => v (a j)) (fun j => d (a j)) 1 slot x) *
            Coulomb.slotTensor (fun j => v (b j)) (fun j => e (b j)) 1 slot x) := by
  simp only [derivativeTensorValue, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma head_derivative_integral (v d e : Fin (Q + 1) → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) (he : ∀ i, MemLp (e i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (ψ φ : State (n + 1) Q) :
    (∫ x : Fin (n + 1) → A, star (derivativeTensorValue v d ψ 0 x) *
      derivativeTensorValue v e φ 0 x ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ j, (∫ x, star (d i x) * e j x ∂μ) *
        ∑ a : Laughlin.Configuration n Q, star (ψ (Fin.cons i a)) * φ (Fin.cons j a) := by
  have ht (a b : Laughlin.Configuration (n + 1) Q) : Integrable
      (fun x : Fin (n + 1) → A => (star (ψ a) * φ b) *
        (star (Coulomb.slotTensor (fun j => v (a j)) (fun j => d (a j)) 1 0 x) *
          Coulomb.slotTensor (fun j => v (b j)) (fun j => e (b j)) 1 0 x))
      (Measure.pi fun _ => μ) :=
    ((Coulomb.slotTensor_memLp (fun j => v (a j)) (fun j => d (a j))
      (fun j => hv (a j)) (fun j => hd (a j)) 1 0).star.integrable_mul
        (Coulomb.slotTensor_memLp (fun j => v (b j)) (fun j => e (b j))
          (fun j => hv (b j)) (fun j => he (b j)) 1 0)).const_mul _
  simp_rw [derivative_bilinear_expansion]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ht a b))]
  simp_rw [integral_finsetSum _ (fun b _ => ht _ b), integral_const_mul]
  have hI (a b : Laughlin.Configuration (n + 1) Q) :
      (∫ x : Fin (n + 1) → A,
        star (Coulomb.slotTensor (fun j => v (a j)) (fun j => d (a j)) 1 0 x) *
          Coulomb.slotTensor (fun j => v (b j)) (fun j => e (b j)) 1 0 x
        ∂(Measure.pi fun _ => μ)) =
      (∫ x, star (d (a 0) x) * e (b 0) x ∂μ) *
        ∏ j ∈ Finset.univ.erase 0, ∫ x, star (v (a j) x) * v (b j) x ∂μ := by
    exact MixedSlater.slotTensor_integral (fun j => v (a j)) (fun j => d (a j))
      (fun j => v (b j)) (fun j => e (b j)) 1 1 0
  simp_rw [hI]
  simp only [ho, OrbitalTensor.prod_erase_zero]
  rw [OrbitalTensor.head_pair_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, OrbitalTensor.delta_product]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma derivative_CAR_compression (v d e : Fin (Q + 1) → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) (he : ∀ i, MemLp (e i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (ψ φ : State (n + 1) Q) (hψ : Laughlin.Antisymmetric ψ) (hφ : Laughlin.Antisymmetric φ) :
    (n + 1 : ℂ) * (∫ x : Fin (n + 1) → A, star (derivativeTensorValue v d ψ 0 x) *
      derivativeTensorValue v e φ 0 x ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ j, (∫ x, star (d i x) * e j x ∂μ) *
        Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n + 1) Q ψ)
          (Laughlin.Fock.create i (Laughlin.Fock.annihilate j
            (Laughlin.Fock.normalizedTensorExterior (n + 1) Q φ))) := by
  rw [head_derivative_integral v d e hv hd he ho ψ φ]
  simp only [FockTensorCompression.oneBody_inner n Q ψ φ hψ hφ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

lemma slater_derivative_CAR_compression (v d e : Fin (Q + 1) → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) (he : ∀ i, MemLp (e i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x ∂μ) = if i = j then (1 : ℂ) else 0)
    (c b : EuclideanSpace ℂ (Occupied Q (n + 1))) :
    (n + 1 : ℂ) * (∫ x : Fin (n + 1) → A,
      star (∑ S, c S * normalizedSlotWave v d S 0 x) *
        (∑ T, b T * normalizedSlotWave v e T 0 x) ∂(Measure.pi fun _ => μ)) =
      ∑ i, ∑ j, (∫ x, star (d i x) * e j x ∂μ) *
        Laughlin.Fock.occupationInner Q (∑ S, c S • Laughlin.Fock.occupationBasis Q S.val)
          (Laughlin.Fock.create i (Laughlin.Fock.annihilate j
            (∑ T, b T • Laughlin.Fock.occupationBasis Q T.val))) := by
  have h := derivative_CAR_compression v d e hv hd he ho (occupationTensor c) (occupationTensor b)
    (occupationTensor_antisymmetric c) (occupationTensor_antisymmetric b)
  simpa only [derivativeTensorValue_occupationTensor, normalizedTensorExterior_occupationTensor] using h

end ContinuumCoulomb.OrbitalDerivative

end

end OAI
