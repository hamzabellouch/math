import OAI.NumberTheory.JointDickman.Probability.GroupedKernelFeatures

namespace OAI

/-! # Uniform bounds for the finite-feature approximation -/

namespace JointDickman
open Finset

theorem groupedKernelCoefficient_bound {D R : Type*} [Fintype D] [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) {C : ℝ} (hδ : 0 ≤ δ)
    (hrow : ∀ a, (∑ b, δ*|K a b|) ≤ C) (d e : D) :
    |groupedKernelCoefficient δ K d e| ≤ δ*(Fintype.card R : ℝ)*C := by
  have hpart (r : R) : (∑ s, δ*|K (d,r) (e,s)|) ≤ C := by
    have hh := single_le_sum (s := univ) (f := fun b : D => ∑ s, δ*|K (d,r) (b,s)|)
      (fun b _ => sum_nonneg (fun s _ => mul_nonneg hδ (abs_nonneg _))) (mem_univ e)
    exact hh.trans (by simpa only [Fintype.sum_prod_type] using hrow (d,r))
  calc
    _ = δ^2*|∑ r, ∑ s, K (d,r) (e,s)| := by
      rw [groupedKernelCoefficient,abs_mul,abs_of_nonneg (sq_nonneg δ)]
    _ ≤ δ^2*(∑ r, ∑ s, |K (d,r) (e,s)|) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun r _ => abs_sum_le_sum_abs _ _))
    _ = δ*(∑ r, ∑ s, δ*|K (d,r) (e,s)|) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      ring
    _ ≤ δ*(∑ _r : R, C) := mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hpart r)) hδ
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

theorem primeCoarseCoefficient_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    {C : ℝ} (hrow : ∀ i, (∑ j, channelMesh (channelFineCount m B)*|K i j|) ≤ C)
    (d e : Fin m) : |primeCoarseCoefficient m B K d e| ≤ channelMesh m*C := by
  have hr (a : Fin m × Fin (channelBlockCount m B)) :
      (∑ b, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ C := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun j => channelMesh (channelFineCount m B)*|K (channelIndexEquiv m B a) j|)]
    exact hrow _
  have hh := groupedKernelCoefficient_bound (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
    (channelMesh_pos (channelFineCount_pos hm hB)).le hr d e
  simpa only [primeCoarseCoefficient,Fintype.card_fin,channelMesh_block_normalization hm hB] using hh

theorem primeCoarseKernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, channelMesh (channelFineCount m B)*|K i j|) ≤ C)
    (x y : auxiliaryPrimes B → Bool) :
    |primeCoarseKernel m B K x y| ≤ (m : ℝ)^2*C/channelMesh m := by
  have hμ := channelMesh_pos hm
  have hterm (d e : Fin m) :
      |primeCoarseCoefficient m B K d e*primeCoarseFeature m B d x*primeCoarseFeature m B e y| ≤
        C/channelMesh m := by
    rw [abs_mul,abs_mul,
      abs_of_nonneg (primeCoarseFeature_bounds hm d x).1,
      abs_of_nonneg (primeCoarseFeature_bounds hm e y).1]
    have hh := mul_le_mul
      (mul_le_mul (primeCoarseCoefficient_bound hm hB K hrow d e)
        (primeCoarseFeature_bounds hm d x).2 (primeCoarseFeature_bounds hm d x).1
        (mul_nonneg hμ.le hC))
      (primeCoarseFeature_bounds hm e y).2 (primeCoarseFeature_bounds hm e y).1
      (by positivity : 0 ≤ channelMesh m*C*(1/channelMesh m))
    exact hh.trans_eq (by field_simp)
  unfold primeCoarseKernel
  calc
    _ ≤ ∑ d : Fin m, ∑ e : Fin m,
        |primeCoarseCoefficient m B K d e*primeCoarseFeature m B d x*primeCoarseFeature m B e y| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _d : Fin m, ∑ _e : Fin m, C/channelMesh m :=
      sum_le_sum (fun d _ => sum_le_sum (fun e _ => hterm d e))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end JointDickman

end OAI
