import OAI.Combinatorics.HoneycombChords.PositiveJets
import OAI.Combinatorics.HoneycombChords.HyperbolicTransform

namespace OAI

/-! Calculus, total positivity, and exponential bounds for the entire beta kernel. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Filter Topology
lemma cosineKernelJet_zero_zero_cos {b x : ℝ} (hb : 0 ≤ b) (hx : x ≤ 0) :
    cosineKernelJet 0 0 b x=Real.cos (Real.sqrt b*Real.sqrt (-x)) := by
  apply HasSum.tsum_eq
  convert Real.hasSum_cos (Real.sqrt b*Real.sqrt (-x)) using 1
  ext k
  dsimp [kernelJetTerm]
  rw [polynomialJet_X_pow,polynomialJet_X_pow]
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  rw [mul_pow,pow_mul,pow_mul,Real.sq_sqrt hb,Real.sq_sqrt (neg_nonneg.mpr hx)]
  simp_rw [←mul_pow]
  congr 2
  ring
lemma polynomialJet_at_zero_X_pow (k r : ℕ) :
    polynomialJet ((X:Polynomial ℝ)^k) 0 r=if k=r then 1 else 0 := by
  simp [polynomialJet,Polynomial.coeff_X_pow,eq_comm]
lemma cosineKernelJet_at_zero (r : ℕ) (x : ℝ) :
    cosineKernelJet r 0 0 x=x^r/(2*r).factorial := by
  unfold cosineKernelJet kernelJetTerm
  simp only [polynomialJet_at_zero_X_pow]
  rw [tsum_eq_single r]
  · simp [polynomialJet_X_pow]
  · intro k hk
    simp [hk]
lemma cosineKernelJet_contDiff_right (r s : ℕ) (b : ℝ) :
    ∀ k : ℕ,ContDiff ℝ k (fun x=>cosineKernelJet r s b x) := by
  intro k
  induction k generalizing s with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun x=>(cosineKernelJet_hasDerivAt_right r s b x).continuousAt))
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨fun x=>(cosineKernelJet_hasDerivAt_right r s b x).differentiableAt,?_,?_⟩
    · simp
    · have he : deriv (fun x=>cosineKernelJet r s b x)=fun x=>(s+1:ℝ)*cosineKernelJet r (s+1) b x :=
        funext (fun x=>(cosineKernelJet_hasDerivAt_right r s b x).deriv)
      rw [he]
      exact contDiff_const.mul (ih (s+1))
lemma cosineKernelJet_contDiff_left (r s : ℕ) (x : ℝ) (k : ℕ) :
    ContDiff ℝ k (fun b=>cosineKernelJet r s b x) := by
  simpa only [cosineKernelJet_symm r s] using cosineKernelJet_contDiff_right s r x k
/-- The complete jet determinant with literal iterated derivatives, not a series interface. -/
lemma complete_beta_jet_det_pos {n : ℕ} (b x : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hx : Monotone (fun i : Fin n=>x i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hx0 : ∀ i : Fin n,0 ≤ x i) :
    0 < Matrix.det (fun i j : Fin n=>iteratedDeriv (nodalOrder x j)
      (fun y=>iteratedDeriv (nodalOrder b i) (fun z=>cosineKernelJet 0 0 z y) (b i)) (x j)) := by
  simp_rw [cosineKernelJet_mixed]
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j=>cosineKernelJet (nodalOrder b i) (nodalOrder x j) (b i) (x j)
  have hm : Matrix.of (fun i j : Fin n=>( (nodalOrder b i).factorial:ℝ)*((nodalOrder x j).factorial:ℝ)*A i j)=
    Matrix.of (fun i j : Fin n=>((nodalOrder b i).factorial:ℝ)*
      (Matrix.of (fun i j : Fin n=>((nodalOrder x j).factorial:ℝ)*A i j)) i j) := by
    ext i j
    simp only [Matrix.of_apply]
    ring
  change 0 < (Matrix.of (fun i j : Fin n=>((nodalOrder b i).factorial:ℝ)*((nodalOrder x j).factorial:ℝ)*A i j)).det
  rw [hm,Matrix.det_mul_column,Matrix.det_mul_row]
  apply mul_pos (prod_pos (fun i _=>by positivity))
  exact mul_pos (prod_pos (fun i _=>by positivity)) (cosineKernelJet_det_pos b x hb hx hb0 hx0)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset MeasureTheory Filter Topology
lemma binomial_term_le_add_pow {b δ : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ δ) (k r : ℕ) :
    (k.choose r:ℝ)*b^(k-r)*δ^r ≤ (b+δ)^k := by
  by_cases hr : r ≤ k
  · rw [add_comm,add_pow]
    have h:=single_le_sum (f:=fun i=>δ^i*b^(k-i)*(k.choose i:ℝ))
      (s:=range (k+1)) (fun i _=>by positivity) (mem_range.mpr (by omega : r<k+1))
    nlinarith only [h]
  · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hr),add_nonneg hb hd]
lemma cosineKernelJet_nonneg {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (r s : ℕ) :
    0 ≤ cosineKernelJet r s b x := by
  apply tsum_nonneg
  intro k
  simp only [kernelJetTerm,polynomialJet_X_pow]
  positivity
lemma cosineKernelJet_label_bound {b x δ : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hd : 0 < δ) (r : ℕ) :
    cosineKernelJet r 0 b x ≤ δ^(- (r:ℤ))*cosineKernelJet 0 0 (b+δ) x := by
  have he : δ^(-(r:ℤ))=(δ^r)⁻¹ := by simp
  rw [he,cosineKernelJet,cosineKernelJet,←tsum_mul_left]
  apply (kernelJetTerm_summable r 0 b x).tsum_le_tsum _ ((kernelJetTerm_summable 0 0 (b+δ) x).mul_left _)
  intro k
  simp only [kernelJetTerm,polynomialJet_X_pow,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  have h:=binomial_term_le_add_pow hb hd.le k r
  have hh : (k.choose r:ℝ)*b^(k-r) ≤ (δ^r)⁻¹*(b+δ)^k := by
    rw [inv_mul_eq_div,le_div_iff₀ (pow_pos hd _)]
    exact h
  calc
    _ ≤ ((δ^r)⁻¹*(b+δ)^k)*x^k/((2*k).factorial:ℝ) := by gcongr
    _ = _ := by ring
lemma cosineKernelJet_exp_bound {b δ : ℝ} (hb : 0 ≤ b) (hd : 0 < δ)
    (r : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |cosineKernelJet r 0 b (z^2)| ≤ δ^(-(r:ℤ))*Real.exp (Real.sqrt (b+δ)*z) := by
  rw [abs_of_nonneg (cosineKernelJet_nonneg hb (sq_nonneg _) r 0)]
  apply (cosineKernelJet_label_bound hb (sq_nonneg _) hd r).trans
  rw [cosineKernelJet_zero_zero_cosh (by positivity) (sq_nonneg _),Real.sqrt_sq hz]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h:=Analytic.cosh_abs_le_exp_abs (Real.sqrt (b+δ)*z)
  simpa only [abs_of_pos (Real.cosh_pos _),abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hz)] using h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
