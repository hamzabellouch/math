import OAI.NumberTheory.Jacobsthal.Estimates.MarginalGrowth
import OAI.NumberTheory.Jacobsthal.Estimates.MarginalProfiles
import OAI.NumberTheory.Jacobsthal.Primes.PrimeMarginalRecursion

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.MarginalTransport

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeGridGeometry PrimeGridKernel PrimeSideSupport
open PrimeMarginalRecursion MarginalProfiles ExponentialMesh DerivativeWeights

noncomputable def rowFactor (L κ w S : ℝ) : ℝ :=
  (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*Real.exp (L*(1+S)^3*mesh κ w)

theorem rowFactor_pos (L κ w S : ℝ) : 0 < rowFactor L κ w S := by unfold rowFactor; positivity

theorem factor_eq_row (L κ w S : ℝ) :
    MarginalGrowth.factor L κ w S = rowFactor L κ w S*(1+20*mesh κ w) := rfl

theorem row_le_factor (L κ w S : ℝ) : rowFactor L κ w S ≤ MarginalGrowth.factor L κ w S := by
  rw [factor_eq_row]
  have hm := mesh_pos κ w
  have hR := rowFactor_pos L κ w S
  nlinarith

theorem entry_nonneg (L κ w S : ℝ) (m j k : ℕ) {i : Side}
    (hj : Valid i.flip (point m j)) (hk : Valid i (point m k)) : 0 ≤ entry L κ w S m i j k := by
  have hm := width_nonneg m
  have hW := (WeightFutureIntegrals.W_pos (valid_pos hj)).le
  have hr := (div_pos (weight_pos hj) (weight_pos hk)).le
  unfold entry
  positivity

theorem entry_cancel (L κ w S C : ℝ) (m n j k : ℕ) (i : Side) (F : ℝ → ℝ)
    (hk : Valid i (point m k)) :
    entry L κ w S m i j k*(C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*F (point m k)) =
      (C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j))*
        W (point m j)*(width m*F (point m k)) := by
  have heq : (weight i.flip (point m j)/weight i (point m k))*weight i (point m k) = weight i.flip (point m j) :=
    div_mul_cancel₀ _ (weight_pos hk).ne'
  calc
    _ = (C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*W (point m j)*width m*F (point m k))*
        ((weight i.flip (point m j)/weight i (point m k))*weight i (point m k)) := by unfold entry rowFactor; ring
    _ = _ := by rw [heq]; ring

theorem transport_sum (L κ w S C : ℝ) (m n j : ℕ) (i : Side) (I : Finset ℕ)
    (F : ℝ → ℝ) (μ : ℕ → ℝ≥0∞) (hC : 0 ≤ C) (hj : Valid i.flip (point m j))
    (hI : ∀ k ∈ I,Valid i (point m k)) (hF : ∀ k ∈ I,0 ≤ F (point m k))
    (hμ : ∀ k ∈ I,μ k ≤ ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*F (point m k))) :
    (∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*μ k) ≤
      ENNReal.ofReal ((C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j))*
        (W (point m j)*(∑ k ∈ I,width m*F (point m k)))) := by
  let scale := C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j)
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hr := (rowFactor_pos L κ w S).le
  have hw := width_nonneg m
  have hp := (weight_pos hj).le
  have hWt := (WeightFutureIntegrals.W_pos (valid_pos hj)).le
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  calc
    _ ≤ ∑ k ∈ I,ENNReal.ofReal (scale*W (point m j)*(width m*F (point m k))) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ENNReal.ofReal (entry L κ w S m i j k)*
            ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*F (point m k)) :=
          mul_le_mul_of_nonneg_left (hμ k hk) zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (entry_nonneg L κ w S m j k hj (hI k hk))]
          exact congrArg ENNReal.ofReal (entry_cancel L κ w S C m n j k i F (hI k hk))
    _ = ENNReal.ofReal ((scale*W (point m j))*(∑ k ∈ I,width m*F (point m k))) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (s:=I)
        (f:=fun k => scale*W (point m j)*(width m*F (point m k)))
        (fun k hk => mul_nonneg (mul_nonneg hscale hWt) (mul_nonneg hw (hF k hk)))]
    _ = _ := by congr 1; ring

theorem profile_step (L κ w S C : ℝ) {m : ℕ} (hm : 1 ≤ m) (hmesh : width m = mesh κ w)
    (n j : ℕ) (i : Side) (μ : ℕ → ℝ≥0∞) (hC : 0 ≤ C) (hj : lowerIndex m i.flip ≤ j)
    (hμ : ∀ k,lowerIndex m i ≤ k → μ k ≤
      ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*profile m i (point m k))) :
    (∑ k ∈ Finset.Icc (lowerIndex m i) (j+m+1),ENNReal.ofReal (entry L κ w S m i j k)*μ k) ≤
      ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^(n+1)*width m*weight i.flip (point m j)*profile m i.flip (point m j)) := by
  have hjV := index_valid hm i.flip hj
  have ht := transport_sum L κ w S C m n j i (Finset.Icc (lowerIndex m i) (j+m+1)) (profile m i) μ hC hjV
    (fun k hk => index_valid hm i (Finset.mem_Icc.mp hk).1)
    (fun k hk => profile_nonneg m (index_regular hm i (Finset.mem_Icc.mp hk).1))
    (fun k hk => hμ k (Finset.mem_Icc.mp hk).1)
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hr := (rowFactor_pos L κ w S).le
  have hw := width_nonneg m
  have hp := (weight_pos hjV).le
  have hscale : 0 ≤ C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j) := by positivity
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j))*
        ((1+20*width m)*profile m i.flip (point m j)) := mul_le_mul_of_nonneg_left (stationary_profile hm i hj) hscale
    _ = _ := by rw [pow_succ,factor_eq_row,← hmesh]; ring

theorem first_to_second (L κ w S C : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (j : ℕ) (hj : 2*m ≤ j) (μ : ℕ → ℝ≥0∞) (hC : 0 ≤ C)
    (hμ : ∀ k,Valid .odd (point m k) → μ k ≤
      ENNReal.ofReal (C*MarginalGrowth.factor L κ w S*width m*W (point m k)*weight .odd (point m k))) :
    (∑ k ∈ weakIndices m j .odd,ENNReal.ofReal (entry L κ w S m .odd j k)*μ k) ≤
      ENNReal.ofReal ((24*C)*(MarginalGrowth.factor L κ w S)^2*width m*weight .even (point m j)) := by
  classical
  have hjV : Valid Side.even (point m j) := index_valid hm .even hj
  have hI : ∀ k ∈ weakIndices m j .odd,Valid .odd (point m k) := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hF : ∀ k ∈ weakIndices m j .odd,0 ≤ W (point m k) :=
    fun k hk => (WeightFutureIntegrals.W_pos (valid_pos (hI k hk))).le
  have ht := transport_sum L κ w S C m 1 j .odd (weakIndices m j .odd) W μ hC hjV hI hF
    (fun k hk => by simpa only [pow_one,mul_assoc,mul_comm,mul_left_comm] using hμ k (hI k hk))
  rw [pow_one] at ht
  have hfirst := first_row_sum hm hj (weakIndices m j .odd)
    (fun k hk => (Finset.mem_filter.mp hk).1)
    (fun k hk => by have h := hI k hk; change 95/100 ≤ point m k at h; linarith)
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hr := (rowFactor_pos L κ w S).le
  have hw := width_nonneg m
  have hp := (weight_pos hjV).le
  have hscale : 0 ≤ C*MarginalGrowth.factor L κ w S*rowFactor L κ w S*width m*weight .even (point m j) := by positivity
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (C*MarginalGrowth.factor L κ w S*rowFactor L κ w S*width m*weight .even (point m j))*24 :=
      mul_le_mul_of_nonneg_left hfirst hscale
    _ = (24*C*MarginalGrowth.factor L κ w S*width m*weight .even (point m j))*rowFactor L κ w S := by ring
    _ ≤ (24*C*MarginalGrowth.factor L κ w S*width m*weight .even (point m j))*MarginalGrowth.factor L κ w S :=
      mul_le_mul_of_nonneg_left (row_le_factor L κ w S) (by positivity)
    _ = _ := by ring

end NumberTheoryLean.MarginalTransport

end

end Erdos970

end OAI
