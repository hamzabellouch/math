import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockOneBodyIntegral
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorTotalReplacement

namespace OAI

/-! Exact CAR compression of differential orbital residuals. The residual
family is only assumed to lie in L2, so the result applies to the actual
manufactured orbitals and their finite-box error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockResidualIntegral
open Laughlin Laughlin.Fock FockSlaterTensor FockOneBodyIntegral

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {n Q : ℕ}

theorem tensor_pair_slot_integrable (v r : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (a b : Laughlin.Configuration n Q) (i : Fin n) :
    Integrable (fun x : Fin n → A => (star (∏ j, v (a j) (x j)))*
      (∏ j, if j=i then r (b j) (x j) else v (b j) (x j))) (Measure.pi fun _ => μ) := by
  have hm (j : Fin n) : MemLp (fun y => if j=i then r (b j) y else v (b j) y) 2 μ := by
    by_cases hj : j=i
    · simpa only [hj,ite_true] using hr (b i)
    · simpa only [hj,ite_false] using hv (b j)
  exact (Coulomb.scalarTensor_memLp v hv a).star.integrable_mul
    (Coulomb.scalarTensor_memLp (fun j y => if j=i then r (b j) y else v (b j) y) hm id)

theorem tensor_pair_slot_integral (v r : Fin (Q+1) → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (a b : Laughlin.Configuration n Q) (i : Fin n) :
    (∫ x : Fin n → A, (star (∏ j, v (a j) (x j)))*
      (∏ j, if j=i then r (b j) (x j) else v (b j) (x j)) ∂(Measure.pi fun _ => μ)) =
      (∫ x, star (v (a i) x)*r (b i) x ∂μ)*
        ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0 := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (f := fun j x => star (v (a j) x)*(if j=i then r (b j) x else v (b j) x)) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => ∫ x, star (v (a j) x)*(if j=i then r (b j) x else v (b j) x) ∂μ)
    (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [(Finset.mem_erase.mp hj).1,ite_false,ho]

omit [MeasurableSpace A] in
theorem tensorValue_slot_expansion (v r : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (i : Fin n) (x : Fin n → A) :
    star (tensorValue v ψ x)*tensorSlotReplacement v r φ i x =
      ∑ a, ∑ b, (star (ψ a)*φ b)*((star (∏ j, v (a j) (x j)))*
        (∏ j, if j=i then r (b j) (x j) else v (b j) (x j))) := by
  simp only [tensorValue,tensorSlotReplacement,star_sum,star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorValue_slot_integral (v r : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (ψ φ : State n Q) (i : Fin n) :
    (∫ x, star (tensorValue v ψ x)*tensorSlotReplacement v r φ i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*((∫ x, star (v (a i) x)*r (b i) x ∂μ)*
        ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0) := by
  simp_rw [tensorValue_slot_expansion]
  have hi (a b : Laughlin.Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a)*φ b)*((star (∏ j, v (a j) (x j)))*
        (∏ j, if j=i then r (b j) (x j) else v (b j) (x j)))) (Measure.pi fun _ => μ) :=
    (tensor_pair_slot_integrable v r hv hr a b i).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul,tensor_pair_slot_integral v r ho]

theorem tensorValue_residual_integral (v r : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (ψ φ : State (n+1) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) :
    (∫ x, star (tensorValue v ψ x)*tensorTotalReplacement v r φ x
      ∂(Measure.pi fun _ : Fin (n+1) => μ)) =
      occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
        (HubbardGlobal.oneBodyOperator (fun a b => ∫ x, star (v a x)*r b x ∂μ)
          (normalizedTensorExterior (n+1) Q φ)) := by
  have hp : MemLp (tensorValue v ψ) 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
    memLp_finsetSum _ (fun a _ => (Coulomb.scalarTensor_memLp v hv a).const_mul (ψ a))
  simp only [tensorTotalReplacement,Finset.mul_sum]
  have hslot (i : Fin (n+1)) : Integrable (fun x =>
      star (tensorValue v ψ x)*tensorSlotReplacement v r φ i x) (Measure.pi fun _ => μ) :=
    hp.star.integrable_mul (tensorSlotReplacement_memLp v r hv hr φ i)
  rw [integral_finsetSum _ (fun i _ => hslot i)]
  have hi (i : Fin (n+1)) := (tensorValue_slot_integral v r hv hr ho ψ φ i).trans
    (oneBody_contraction (fun a b => ∫ x, star (v a x)*r b x ∂μ) ψ φ hψ hφ i)
  simp_rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    HubbardGlobal.oneBodyOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hcar := FockTensorCompression.oneBody_inner n Q ψ φ hψ hφ a b
  change occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
    ((HubbardGlobal.transfer a b) (normalizedTensorExterior (n+1) Q φ)) = _ at hcar
  rw [hcar]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  push_cast
  ring

end ContinuumCoulomb.FockResidualIntegral

end

end OAI
