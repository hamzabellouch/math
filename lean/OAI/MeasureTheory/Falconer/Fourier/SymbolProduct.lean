import OAI.MeasureTheory.Falconer.Fourier.SmoothMaskDerivatives
import OAI.MeasureTheory.Falconer.Fourier.SymbolProductBounds

namespace OAI

/-!
# Finite derivative budgets for products of angular masks

Products of scalar angular masks are considered in arbitrary one-coordinate
charts and for arbitrary finite indexed descriptor lists, including repeated
descriptors.
-/

namespace Falconer
open scoped ContDiff

private theorem product_derivatives_at {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) (c : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (J : ℕ) (x : ℝ) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ k ≤ J, ‖iteratedDeriv k (f i) x‖ ≤ c i*D^k) :
    ∀ j ≤ J, ‖iteratedDeriv j (fun t => ∏ i ∈ S, f i t) x‖ ≤
      (∏ i ∈ S, c i)*((S.card : ℝ)*D)^j := by
  induction S using Finset.induction_on with
  | empty =>
    intro j _
    cases j with
    | zero => simp
    | succ j => simp [iteratedDeriv_const]
  | @insert a S ha ih =>
    have hcS : ∀ i ∈ S, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbS := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih := ih hcS hfS hbS
    intro j hj
    have hfa : ContDiffAt ℝ j (f a) x := ((hf a (Finset.mem_insert_self _ _)).of_le (by simp)).contDiffAt
    have hfp : ContDiffAt ℝ j (fun t => ∏ i ∈ S, f i t) x :=
      ((contDiff_prod hfS).of_le (by simp)).contDiffAt
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    rw [iteratedDeriv_fun_mul hfa hfp]
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1),
          (j.choose k : ℝ)*(c a*D^k)*((∏ i ∈ S, c i)*((S.card : ℝ)*D)^(j-k)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp only [norm_mul,Real.norm_natCast]
        have hca := hc a (Finset.mem_insert_self _ _)
        gcongr
        · exact hb a (Finset.mem_insert_self _ _) k (hkj.trans hj)
        · exact ih (j-k) ((Nat.sub_le _ _).trans hj)
      _ = (c a*∏ i ∈ S, c i)*(D+(S.card : ℝ)*D)^j := by
        rw [add_pow,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by congr 2; ring

private theorem iteratedDeriv_add_order (f : ℝ → ℝ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k f) = iteratedDeriv (j+k) f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ,ih,Nat.succ_add,iteratedDeriv_succ]

private theorem iteratedDeriv_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

noncomputable def normalizedChartFactor (f : ℝ → ℝ) (D : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (D⁻¹)^k*iteratedDeriv k f x

theorem normalizedChartFactor_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (D : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (normalizedChartFactor f D k) :=
  contDiff_const.mul (iteratedDeriv_contDiff hf k)

theorem normalizedChartFactor_derivative_bound {f : ℝ → ℝ} {A D : ℝ}
    (hD : 0 < D) (J k j : ℕ) (hkj : k+j ≤ J) (x : ℝ)
    (hb : ∀ l ≤ J, ‖iteratedDeriv l f x‖ ≤ A^l*D^l) :
    ‖iteratedDeriv j (normalizedChartFactor f D k) x‖ ≤ A^k*(A*D)^j := by
  unfold normalizedChartFactor
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_add_order,norm_mul,Real.norm_eq_abs,
    abs_pow,abs_of_pos (inv_pos.mpr hD)]
  calc
    _ ≤ (D⁻¹)^k*(A^(j+k)*D^(j+k)) := mul_le_mul_of_nonneg_left
      (hb (j+k) (by omega)) (by positivity)
    _ = _ := by
      rw [pow_add,pow_add,mul_pow]
      have he : (D⁻¹)^k*D^k = 1 := by rw [← mul_pow,inv_mul_cancel₀ hD.ne',one_pow]
      calc
        _ = ((D⁻¹)^k*D^k)*A^k*A^j*D^j := by ring
        _ = _ := by rw [he]; ring

theorem normalized_chart_product_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) (D : ι → ℝ) (k : ι → ℕ)
    {A L : ℝ} (hA : 1 ≤ A) (hL : 0 ≤ L) (K j : ℕ)
    (hbudget : ∑ i ∈ S, k i ≤ K)
    (hD : ∀ i ∈ S, 0 < D i) (hLbound : ∀ i ∈ S, D i ≤ L)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (x : ℝ)
    (hb : ∀ i ∈ S, ∀ l ≤ K+j, ‖iteratedDeriv l (f i) x‖ ≤ A^l*(D i)^l) :
    ‖iteratedDeriv j (fun t => ∏ i ∈ S, normalizedChartFactor (f i) (D i) (k i) t) x‖ ≤
      A^(K+j)*((S.card : ℝ)*L)^j := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hk (i : ι) (hi : i ∈ S) : k i ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans hbudget
  have hh := product_derivatives_at S
    (fun i => normalizedChartFactor (f i) (D i) (k i)) (fun i => A^(k i)) (A*L)
    (mul_nonneg hA0 hL) j x (fun _ _ => pow_nonneg hA0 _)
    (fun i hi => normalizedChartFactor_contDiff (hf i hi) _ _)
    (fun i hi l hl => (normalizedChartFactor_derivative_bound (hD i hi) (K+j)
      (k i) l (Nat.add_le_add (hk i hi) hl) x (hb i hi)).trans (by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA0 _)
        exact pow_le_pow_left₀ (mul_nonneg hA0 (hD i hi).le)
          (mul_le_mul_of_nonneg_left (hLbound i hi) hA0) l)) j le_rfl
  apply hh.trans
  rw [Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ A^K*((S.card : ℝ)*(A*L))^j := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hA hbudget) (by positivity)
    _ = _ := by rw [pow_add,mul_pow,mul_pow]; ring

end Falconer

end OAI
