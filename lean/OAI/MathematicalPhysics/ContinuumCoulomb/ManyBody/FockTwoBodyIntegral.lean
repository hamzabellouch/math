import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockTwoBodyContraction

namespace OAI

/-! Singular two-particle integrals of the actual orbital tensor and their
CAR representation. Integrability is required only for the four-index entries. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockTwoBodyIntegral
open Laughlin Laughlin.Fock FockSlaterTensor FockOneBodyIntegral FockTwoBodyContraction

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {n Q : ℕ}

theorem tensor_pair_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (a b : Laughlin.Configuration n Q) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j)*
      (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k)))) (Measure.pi fun _ => μ) := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  exact Coulomb.pair_weight_tensor_integrable i j hij
    (fun k x => star (v (a k) x)*v (b k) x) w
    (fun k => (hv (a k)).star.integrable_mul (hv (b k))) (hw _ _ _ _)

theorem tensor_pair_integral (v : Fin (Q+1) → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ) (a b : Laughlin.Configuration n Q) (i j : Fin n) (hij : i ≠ j) :
    (∫ x : Fin n → A, w (x i) (x j)*
      (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k))) ∂(Measure.pi fun _ => μ)) =
      (∫ z : A × A, w z.1 z.2*((star (v (a i) z.1)*v (b i) z.1)*
        (star (v (a j) z.2)*v (b j) z.2)) ∂(μ.prod μ))*
        ∏ k ∈ (Finset.univ.erase i).erase j, if a k=b k then (1:ℂ) else 0 := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  rw [Coulomb.pair_weight_tensor_integral i j hij
    (fun k x => star (v (a k) x)*v (b k) x) w]
  simp_rw [ho]

omit [MeasurableSpace A] in
theorem tensorValue_pair_expansion (v : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (w : A → A → ℂ) (i j : Fin n) (x : Fin n → A) :
    w (x i) (x j)*(star (tensorValue v ψ x)*tensorValue v φ x) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*(w (x i) (x j)*
        (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k)))) := by
  rw [tensorValue_bilinear]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorValue_pair_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State n Q) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j)*
      (star (tensorValue v ψ x)*tensorValue v φ x)) (Measure.pi fun _ => μ) := by
  simp_rw [tensorValue_pair_expansion]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (tensor_pair_integrable v hv w hw a b i j hij).const_mul _))

theorem tensorValue_pair_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State n Q) (i j : Fin n) (hij : i ≠ j) :
    (∫ x, w (x i) (x j)*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        ((∫ z : A × A, w z.1 z.2*((star (v (a i) z.1)*v (b i) z.1)*
          (star (v (a j) z.2)*v (b j) z.2)) ∂(μ.prod μ))*
          ∏ k ∈ (Finset.univ.erase i).erase j, if a k=b k then (1:ℂ) else 0) := by
  simp_rw [tensorValue_pair_expansion]
  have hi (a b : Laughlin.Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a)*φ b)*(w (x i) (x j)*
        (star (∏ k, v (a k) (x k))*(∏ k, v (b k) (x k))))) (Measure.pi fun _ => μ) :=
    (tensor_pair_integrable v hv w hw a b i j hij).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul,tensor_pair_integral v ho w a b i j hij]

theorem tensorValue_pair_contraction (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State (n+2) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    (∫ x, w (x i) (x j)*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+2) => μ)) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        (∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
          (star (v b z.2)*v d z.2)) ∂(μ.prod μ))*
          ∑ e : Laughlin.Configuration n Q,
            star (ψ (Fin.cons a (Fin.cons b e)))*φ (Fin.cons c (Fin.cons d e)) := by
  obtain ⟨j',rfl⟩ := Fin.exists_succAbove_eq hij.symm
  have hp := tensorValue_pair_integral (μ := μ) (n := n+2) (Q := Q)
    v hv ho w hw ψ φ i (i.succAbove j') hij
  have hc := twoBody_contraction (n := n) (Q := Q)
    (fun a b c d => ∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
      (star (v b z.2)*v d z.2)) ∂(μ.prod μ)) ψ φ hψ hφ i j'
  exact hp.trans hc

theorem tensorValue_twoBody_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → A → ℂ)
    (hw : ∀ a b c d, Integrable (fun z : A × A => w z.1 z.2*
      ((star (v a z.1)*v c z.1)*(star (v b z.2)*v d z.2))) (μ.prod μ))
    (ψ φ : State (n+2) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) :
    (2:ℂ)⁻¹ * (∫ x, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j))*
      (star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+2) => μ)) =
      occupationInner Q (normalizedTensorExterior (n+2) Q ψ)
        (HubbardGlobal.twoBodyOperator (fun a b c d =>
          ∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
            (star (v b z.2)*v d z.2)) ∂(μ.prod μ))
          (normalizedTensorExterior (n+2) Q φ)) := by
  let C : ℂ := ∑ a, ∑ b, ∑ c, ∑ d,
    (∫ z : A × A, w z.1 z.2*((star (v a z.1)*v c z.1)*
      (star (v b z.2)*v d z.2)) ∂(μ.prod μ))*
        ∑ e : Laughlin.Configuration n Q,
          star (ψ (Fin.cons a (Fin.cons b e)))*φ (Fin.cons c (Fin.cons d e))
  have hi : (∫ x, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j))*
      (star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+2) => μ)) = ∑ i : Fin (n+2),
        ∑ _j ∈ Finset.univ.erase i, C := by
    simp only [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum _ (fun j hj => tensorValue_pair_integrable v hv w hw ψ φ i j
        (Finset.ne_of_mem_erase hj).symm))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j hj => tensorValue_pair_integrable v hv w hw ψ φ i j
      (Finset.ne_of_mem_erase hj).symm)]
    apply Finset.sum_congr rfl
    intro j hj
    exact tensorValue_pair_contraction v hv ho w hw ψ φ hψ hφ i j
      (Finset.ne_of_mem_erase hj).symm
  rw [hi]
  simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [HubbardGlobal.twoBodyOperator,LinearMap.smul_apply,LinearMap.sum_apply,
    occupationInner_sum_right,occupationInner_smul_right]
  congr 1
  dsimp only [C]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have hcar := FockTensorCompression.twoBody_inner n Q ψ φ hψ hφ a b c d
  change occupationInner Q (normalizedTensorExterior (n+2) Q ψ)
    ((create a * create b * annihilate d * annihilate c)
      (normalizedTensorExterior (n+2) Q φ)) = _ at hcar
  rw [hcar]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  push_cast
  ring

end ContinuumCoulomb.FockTwoBodyIntegral

end

end OAI
