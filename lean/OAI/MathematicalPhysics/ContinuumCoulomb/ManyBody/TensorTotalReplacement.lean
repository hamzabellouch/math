import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorSlotReplacement

namespace OAI

/-! Summing one-body residuals over electron coordinates costs only the square
of the electron count, even though the tensor coefficient space is exponential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorTotalReplacement {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin n → ι) → ℂ) (x : Fin n → A) : ℂ :=
  ∑ i, tensorSlotReplacement v r c i x

theorem finite_sum_norm_square_le {κ : Type*} [Fintype κ] (f : κ → ℂ) :
    ‖∑ i, f i‖^2 ≤ (Fintype.card κ:ℝ)*∑ i, ‖f i‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ)) (fun i => ‖f i‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ f) 2).trans h

theorem tensorTotalReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : (Fin (n+1) → ι) → ℂ) :
    MemLp (tensorTotalReplacement v r c) 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
  memLp_finsetSum Finset.univ (fun i _ => tensorSlotReplacement_memLp v r hv hr c i)

theorem tensorTotalReplacement_L2_bound {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : (Fin (n+1) → ι) → ℂ) :
    (∫ x, ‖tensorTotalReplacement v r c x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ b, ‖c b‖^2) := by
  have hi (i : Fin (n+1)) := (tensorSlotReplacement_memLp v r hv hr c i).norm.integrable_sq
  calc
    _ ≤ ∫ x, (n+1:ℝ)*∑ i, ‖tensorSlotReplacement v r c i x‖^2
        ∂(Measure.pi fun _ : Fin (n+1) => μ) := by
      apply integral_mono (tensorTotalReplacement_memLp v r hv hr c).norm.integrable_sq
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _)
      intro x
      simpa only [tensorTotalReplacement,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
        finite_sum_norm_square_le (fun i => tensorSlotReplacement v r c i x)
    _ = (n+1:ℝ)*∑ i, ∫ x, ‖tensorSlotReplacement v r c i x‖^2
        ∂(Measure.pi fun _ : Fin (n+1) => μ) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ (n+1:ℝ)*∑ _i : Fin (n+1),
        (∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ b, ‖c b‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        tensorSlotReplacement_L2_bound v r hv hr ho c i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      ring

end ContinuumCoulomb

end

end OAI
