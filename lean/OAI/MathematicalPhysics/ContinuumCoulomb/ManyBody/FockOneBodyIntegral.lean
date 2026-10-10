import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSlaterTensor
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockTensorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockCoefficientNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.MixedSlater

namespace OAI

/-! The one-body potential integral of an actual finite orbital tensor is
the corresponding CAR matrix element. Singular potentials need only the
integrability of the one-orbital matrix entries. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb.FockOneBodyIntegral
open Laughlin Laughlin.Fock FockSlaterTensor

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
variable {n Q : ℕ}

omit [MeasurableSpace A] in
theorem tensorValue_bilinear (v : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (x : Fin n → A) :
    star (tensorValue v ψ x)*tensorValue v φ x =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        (star (∏ i, v (a i) (x i))*(∏ i, v (b i) (x i))) := by
  simp only [tensorValue,star_sum,star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [MeasurableSpace A] in
theorem tensorValue_weighted_expansion (v : Fin (Q+1) → A → ℂ)
    (ψ φ : State n Q) (w : A → ℂ) (i : Fin n) (x : Fin n → A) :
    w (x i)*(star (tensorValue v ψ x)*tensorValue v φ x) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        (w (x i)*(star (∏ j, v (a j) (x j))*(∏ j, v (b j) (x j)))) := by
  rw [tensorValue_bilinear]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem weighted_tensor_pair_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → ℂ)
    (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (a b : Configuration n Q) (i : Fin n) :
    Integrable (fun x : Fin n → A => w (x i)*
      (star (∏ j, v (a j) (x j))*(∏ j, v (b j) (x j))))
        (Measure.pi fun _ => μ) := by
  simp only [star_prod,← Finset.prod_mul_distrib]
  exact Coulomb.weighted_tensor_integrable (fun j x => star (v (a j) x)*v (b j) x) w i
    (fun j => (hv (a j)).star.integrable_mul (hv (b j))) (hw _ _)

theorem tensorValue_weighted_integrable (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (w : A → ℂ)
    (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (ψ φ : State n Q) (i : Fin n) :
    Integrable (fun x : Fin n → A => w (x i)*
      (star (tensorValue v ψ x)*tensorValue v φ x)) (Measure.pi fun _ => μ) := by
  simp_rw [tensorValue_weighted_expansion]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (weighted_tensor_pair_integrable v hv w hw a b i).const_mul _))

theorem tensorValue_weighted_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → ℂ) (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (ψ φ : State n Q) (i : Fin n) :
    (∫ x, w (x i)*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ a, ∑ b, (star (ψ a)*φ b)*
        ((∫ x, w x*(star (v (a i) x)*v (b i) x) ∂μ)*
          ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0) := by
  simp_rw [tensorValue_weighted_expansion]
  have hi (a b : Configuration n Q) : Integrable (fun x : Fin n → A =>
      (star (ψ a)*φ b)*(w (x i)*(star (∏ j, v (a j) (x j))*(∏ j, v (b j) (x j)))))
        (Measure.pi fun _ => μ) := (weighted_tensor_pair_integrable v hv w hw a b i).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul]
  congr 1
  simp only [star_prod,← Finset.prod_mul_distrib]
  rw [Coulomb.weighted_tensor_integral (fun j x => star (v (a j) x)*v (b j) x) w i]
  simp_rw [ho]

private theorem delta_insert_product (i : Fin (n+1)) (a b : Fin (Q+1))
    (c d : Configuration n Q) :
    (∏ j ∈ Finset.univ.erase i, if (i.insertNth a c : Fin (n+1) → Fin (Q+1)) j=
      (i.insertNth b d : Fin (n+1) → Fin (Q+1)) j then (1:ℂ) else 0) =
      if c=d then 1 else 0 := by
  by_cases h : c=d
  · subst d
    rw [ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro j hj
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
    simp only [Fin.insertNth_apply_succAbove,ite_true]
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Fin.succAbove_ne i k,Finset.mem_univ _⟩)
    simpa only [Fin.insertNth_apply_succAbove] using (ite_eq_right hk : (if c k=d k then (1:ℂ) else 0)=0)

theorem oneBody_contraction (K : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ψ φ : State (n+1) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i : Fin (n+1)) :
    (∑ a, ∑ b, (star (ψ a)*φ b)*(K (a i) (b i)*
      ∏ j ∈ Finset.univ.erase i, if a j=b j then (1:ℂ) else 0)) =
      ∑ a, ∑ b, K a b*∑ c : Configuration n Q, star (ψ (Fin.cons a c))*φ (Fin.cons b c) := by
  have hc (a b : Fin (Q+1)) (c d : Configuration n Q) :
      star (ψ (i.insertNth a c))*φ (i.insertNth b d) =
        star (ψ (Fin.cons a c))*φ (Fin.cons b d) := by
    rw [antisymmetric_insertNth hψ,antisymmetric_insertNth hφ,star_mul,star_pow]
    simp only [star_neg,star_one]
    have he : (-1:ℂ)^i.val*(-1:ℂ)^i.val=1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((-1:ℂ)^i.val*(-1:ℂ)^i.val)*
        (star (ψ (Fin.cons a c))*φ (Fin.cons b d)) := by ring
      _ = _ := by rw [he,one_mul]
  rw [sum_config_insert i]
  simp_rw [sum_config_insert i,Fin.insertNth_apply_same,delta_insert_product,hc]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem tensorValue_oneBody_integral (v : Fin (Q+1) → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (w : A → ℂ) (hw : ∀ a b, Integrable (fun x => w x*(star (v a x)*v b x)) μ)
    (ψ φ : State (n+1) Q) (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) :
    (∫ x, (∑ i, w (x i))*(star (tensorValue v ψ x)*tensorValue v φ x)
      ∂(Measure.pi fun _ : Fin (n+1) => μ)) =
      occupationInner Q (normalizedTensorExterior (n+1) Q ψ)
        (HubbardGlobal.oneBodyOperator (fun a b => ∫ x, w x*(star (v a x)*v b x) ∂μ)
          (normalizedTensorExterior (n+1) Q φ)) := by
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => tensorValue_weighted_integrable v hv w hw ψ φ i)]
  have hi (i : Fin (n+1)) := (tensorValue_weighted_integral v hv ho w hw ψ φ i).trans
    (oneBody_contraction (fun a b => ∫ x, w x*(star (v a x)*v b x) ∂μ) ψ φ hψ hφ i)
  simp_rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    HubbardGlobal.oneBodyOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Finset.mul_sum]
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

end ContinuumCoulomb.FockOneBodyIntegral

end

end OAI
