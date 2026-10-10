import OAI.Probability.BenjaminiSchramm.TiltedMoments

namespace OAI

noncomputable section
open scoped ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

def expAbsLayerKernel (a : ℝ) (i : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-a*|(i : ℝ)|))

theorem expAbsLayerKernel_tsum_lt_top {a : ℝ} (ha : 0 < a) :
    (∑' i : ℤ, expAbsLayerKernel a i) < ⊤ := by
  have hn : Summable (fun n : ℕ => Real.exp ((n : ℝ)*(-a))) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)
  have hs : Summable (fun i : ℤ => Real.exp (-a*|(i : ℝ)|)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · convert hn using 1
      funext n
      simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      congr 1
      ring
    · convert hn using 1
      funext n
      simp only [Int.cast_neg,Int.cast_natCast,abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      congr 1
      ring
  exact hs.tsum_ofReal_lt_top

lemma three_layer_abs_bound (k l : ℕ) (i : ℝ) :
    ((max k l : ℕ) : ℝ)+|i+(min k l : ℕ)| ≤ |i|+|-(k : ℝ)-i|+|-(l : ℝ)-i| := by
  have hneg (r : ℕ) : |-(r : ℝ)-i| = |i+r| := by
    rw [show -(r : ℝ)-i = -(i+r) by ring,abs_neg]
  rw [hneg k,hneg l]
  have htriangle (r : ℕ) : (r : ℝ) ≤ |i|+|i+r| := by
    have hh := abs_add_le (-i) (i+(r : ℝ))
    rw [show -i+(i+(r : ℝ)) = (r : ℝ) by ring,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hh
    exact hh
  by_cases hkl : k ≤ l
  · rw [max_eq_right hkl,min_eq_left hkl]
    linarith [htriangle l]
  · rw [max_eq_left (le_of_not_ge hkl),min_eq_right (le_of_not_ge hkl)]
    linarith [htriangle k]

theorem expAbsLayerKernel_triple_bound {a : ℝ} (ha : 0 ≤ a)
    (k l : ℕ) (i : ℤ) :
    expAbsLayerKernel a i * expAbsLayerKernel a (-(k : ℤ)-i) *
        expAbsLayerKernel a (-(l : ℤ)-i) ≤
      ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) *
        expAbsLayerKernel a (i+(min k l : ℕ)) := by
  unfold expAbsLayerKernel
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←ENNReal.ofReal_mul (mul_nonneg
    (Real.exp_nonneg _) (Real.exp_nonneg _)),←ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,Int.cast_add]
  have hh := mul_le_mul_of_nonneg_left (three_layer_abs_bound k l (i : ℝ)) ha
  linarith

theorem expAbsLayerKernel_triple_sum_bound {a : ℝ} (ha : 0 ≤ a) (k l : ℕ) :
    (∑' i : ℤ, expAbsLayerKernel a i * expAbsLayerKernel a (-(k : ℤ)-i) *
      expAbsLayerKernel a (-(l : ℤ)-i)) ≤
      ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) * ∑' i : ℤ, expAbsLayerKernel a i := by
  apply (ENNReal.tsum_le_tsum (expAbsLayerKernel_triple_bound ha k l)).trans_eq
  rw [ENNReal.tsum_mul_left]
  congr 1
  exact (Equiv.addRight ((min k l : ℕ) : ℤ)).tsum_eq (expAbsLayerKernel a)

theorem subcritical_three_profile_convolution {a : ℝ} (ha : 0 ≤ a)
    (C : ℝ≥0∞) (f g h : ℤ → ℝ≥0∞)
    (hf : ∀ i, f i ≤ C*expAbsLayerKernel a i)
    (hg : ∀ i, g i ≤ C*expAbsLayerKernel a i)
    (hh : ∀ i, h i ≤ C*expAbsLayerKernel a i) (k l : ℕ) :
    (∑' i : ℤ, f i*g (-(k : ℤ)-i)*h (-(l : ℤ)-i)) ≤
      C^3*ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) *
        ∑' i : ℤ, expAbsLayerKernel a i := by
  calc
    _ ≤ ∑' i : ℤ, C^3*(expAbsLayerKernel a i * expAbsLayerKernel a (-(k : ℤ)-i) *
        expAbsLayerKernel a (-(l : ℤ)-i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      calc
        _ ≤ (C*expAbsLayerKernel a i)*(C*expAbsLayerKernel a (-(k : ℤ)-i))*
            (C*expAbsLayerKernel a (-(l : ℤ)-i)) :=
          mul_le_mul' (mul_le_mul' (hf i) (hg _)) (hh _)
        _ = _ := by ring
    _ ≤ C^3*(ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ)))*
        ∑' i : ℤ, expAbsLayerKernel a i) := by
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul' le_rfl (expAbsLayerKernel_triple_sum_bound ha k l)
    _ = _ := (mul_assoc _ _ _).symm

theorem subcritical_three_profile_uniform_bound {a : ℝ} (ha : 0 < a)
    (C : ℝ≥0∞) (hC : C < ⊤) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (f g h : ℤ → ℝ≥0∞),
      (∀ i, f i ≤ C*expAbsLayerKernel a i) →
      (∀ i, g i ≤ C*expAbsLayerKernel a i) →
      (∀ i, h i ≤ C*expAbsLayerKernel a i) → ∀ k l : ℕ,
      (∑' i : ℤ, f i*g (-(k : ℤ)-i)*h (-(l : ℤ)-i)) ≤
        K*ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) := by
  refine ⟨C^3*(∑' i : ℤ, expAbsLayerKernel a i),?_,?_⟩
  · apply ENNReal.mul_lt_top _ (expAbsLayerKernel_tsum_lt_top ha)
    simpa only [pow_succ,pow_zero,one_mul] using
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hC hC) hC
  · intro f g h hf hg hh k l
    exact (subcritical_three_profile_convolution ha.le C f g h hf hg hh k l).trans_eq
      (by ring)

end Percolation.BenjaminiSchramm

end

end OAI
