import OAI.Geometry.Convex.GeneralMahler.Linear.SpectralIBP

namespace OAI
/-! Squared norm averaging. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

lemma ihSq {f:Rn m→ℝ} (hf:regular f): Integrable (fun x=>f x^2) (normal m) := by
  simp_rw [pow_two]; exact (hf.mul hf).ig
lemma var_le1 {f:Rn m→ℝ} (hf:regular f):
    (∫ x,f x ∂normal m)^2 ≤ ∫ x,f x^2 ∂normal m := by
  let c:= ∫ x,f x ∂normal m
  have hi : 0 ≤ ∫ x,f x^2-(2*c)*f x+c^2 ∂normal m := by
    apply integral_nonneg; intro x; change (0:ℝ)≤ f x^2-_+_; nlinarith [sq_nonneg (f x-c)]
  rw [integral_add (show Integrable (fun x=>f x^2-(2*c)*f x) (normal m) from ((ihSq hf).sub (hf.ig.const_mul _))) (integrable_const _), integral_sub
    (ihSq hf) (hf.ig.const_mul _),integral_const_mul,integral_const,probReal_univ,one_smul] at hi
  change c^2 ≤ _
  change 0 ≤ _-(2*c)*c+_ at hi; linarith

lemma hs_entry (f:Rn m→Mat m) (hf:regular f):
    (∫ x,hsN (f x) ∂normal m)=
      mats (fun i=>∑ j,∫ x,(f x i j)^2 ∂normal m) := by
  have h (i j) : Integrable (fun x=>(f x i j)^2) (normal m) := ihSq (hf.lin (coeffMap i j))
  simp_rw [hsN_eq]; unfold mats
  rw [integral_div]; congr 1
  rw [integral_finsetSum]
  · congr; ext i; exact integral_finsetSum _ fun j _=>h i j
  exact fun i _=> integrable_finsetSum _ fun j _=>h i j

lemma hs_le_exp (f:Rn m→Mat m) (hf:regular f):
    hsN (∫ x,f x ∂normal m) ≤ ∫ x,hsN (f x) ∂normal m := by
  rw [hs_entry f hf,hsN_eq]
  apply mats_le; intro i; apply Finset.sum_le_sum; intro j _
  have hi : (∫ x,f x ∂normal m) i j=∫ x,f x i j ∂normal m := ((coeffMap i j).integral_comp_comm hf.ig).symm
  rw [hi]
  exact var_le1 (hf.lin (coeffMap i j))

lemma hsCm (A B:Mat m): hsN (cmu A B)=hsN (cmu B A) := by
  rw [show cmu A B= -(cmu B A) from by simp [cmu] ]
  simp [hsN]

namespace ProjField
lemma coord_reg (i:Fin m):
    regular (coord i) :=
  ⟨PolyBound.clm _,(coord i).continuous.aestronglyMeasurable⟩
lemma avg_sq_lin (f:Rn m→ℝ) (h:Fin m→ℝ) (he:∀ x:Rn m,f x=∑ i,x i*h i):
    (∫ x,f x^2 ∂normal m) = ∑ i,h i^2 := by
  have ha (i j:Fin m):
      Integrable (fun x:Rn m=> (x i*x j)*(h i*h j)) (normal m) :=
    ((coord_reg i).mul (coord_reg j)).ig.mul_const _
  have hx (x:Rn m): f x^2=
      ∑ i:Fin m,∑ j:Fin m,(x i*x j)*(h i*h j) := by
    rw [he x,pow_two,Finset.sum_mul]; congr 1; ext i
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hu (i j:Fin m):
    (∫ x:Rn m,x i*x j ∂normal m) = if i=j then (1:ℝ) else 0 := by
    simp_rw [← Mi1, M_inner]
    by_cases hi:i=j
    · subst j; simp
    have hv : inc (0:MI m) i ≠ inc 0 j := by
      intro h; have hk:=congrFun h i; simp [inc,hi] at hk
    simp [hv,hi]
  simp_rw [hx]
  rw [integral_finsetSum]
  · have hv (i:Fin m) :
        (∫ x:Rn m,(∑ j,(x i*x j)*(h i*h j)) ∂normal m)=h i^2 := by
      rw [integral_finsetSum]
      · simp_rw [integral_mul_const,hu]
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
        · simp [pow_two]
        intro j _ hj; simp [hj.symm]
      exact fun j _=>ha i j
    simp_rw [hv]
  exact fun i _=>integrable_finsetSum _ (fun j _=>ha i j)

lemma Comm_L (q:ProjField m) (T:Mat m):
    Hcomm q.Lmat T=∑ i,hsN (cmu (q.M i) T) := by
  obtain ⟨D,hD⟩:=cmCL T
  let f := fun x=>cmu (q.Lmat x) T
  let g := fun i=>cmu (q.M i) T
  have hf : regular f := by unfold f; simp_rw [← congrFun hD]; exact q.l_reg.lin D
  have hl (x:Rn m) : f x=∑ i,x i • g i := by
    unfold f g
    simp_rw [← congrFun hD,Lmat,_root_.map_sum,_root_.map_smul]
  have hh (i j:Fin m) :
      (∫ x,(f x i j)^2 ∂normal m)=∑ k:Fin m,(g k i j)^2 := by
    apply avg_sq_lin; intro x; rw [hl]
    simp_rw [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  unfold Hcomm
  change (∫ x, hsN (f x) ∂normal m)=∑ i,hsN (g i)
  rw [hs_entry f hf]
  simp_rw [hh,hsN_eq]; unfold mats
  rw [← Finset.sum_div]; congr 1
  have he (i:Fin m) : (∑ j:Fin m,∑ k:Fin m,(g k i j)^2)=∑ k,∑ j,(g k i j)^2 := by rw [Finset.sum_comm]
  simp_rw [he]
  rw [Finset.sum_comm]

variable [NeZero m]

lemma comm_expect (q:ProjField m) (M:Mat m) {f:ℝ→ℝ} (hf:TestF f) :
    hsN (cmu M (q.expL f)) ≤ ∫ x,hsN (cmu (q.FL.eval f x) M) ∂normal m := by
  obtain ⟨D,hD⟩:=cmCL M
  have he (A:Mat m) : cmu A M=D A := by rw [← congrFun hD]
  let F:=q.FL.eval f
  rw [hsCm]
  simp_rw [he]
  have h : q.expL f= ∫ x,F x ∂normal m := rfl
  rw [h,← D.integral_comp_comm (q.FL.eval_reg hf).ig]
  exact hs_le_exp _ ((q.FL.eval_reg hf).lin D)
end ProjField
end GeneralMahler

end

end OAI
