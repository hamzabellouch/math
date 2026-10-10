import OAI.Analysis.Laughlin.Pair.CoupledParity

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev WedgePairIndex (Q : ℕ) := {i : SpinIndex Q Q // i.1 < i.2}

noncomputable def tensorToWedgePair (Q : ℕ) (f : SpinIndex Q Q → ℝ) :
    WedgePairIndex Q → ℝ := fun i => Real.sqrt 2 * f i.val

theorem antisymmetric_pairing (Q : ℕ) (f g : SpinIndex Q Q → ℝ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (hg : ∀ i j, g (j,i) = -g (i,j)) :
    (∑ i : WedgePairIndex Q, tensorToWedgePair Q f i * tensorToWedgePair Q g i) =
      ∑ i, f i * g i := by
  have hd (i : Fin (Q+1)) : f (i,i) = 0 := by have h := hf i i; linarith
  have he (i j : Fin (Q+1)) : f (i,j)*g (i,j) =
      (if i < j then f (i,j)*g (i,j) else 0) +
      (if j < i then f (j,i)*g (j,i) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h,not_lt_of_gt h,hf i j,hg i j]
  have hs : (∑ i, f i*g i) = 2 * ∑ i : SpinIndex Q Q, if i.1 < i.2 then f i*g i else 0 := by
    calc
      _ = ∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
          ((if i < j then f (i,j)*g (i,j) else 0) +
          (if j < i then f (j,i)*g (j,i) else 0)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        exact he i j
      _ = _ := by
        simp only [Finset.sum_add_distrib,Fintype.sum_prod_type]
        rw [Finset.sum_comm (f := fun i j : Fin (Q+1) => if j < i then f (j,i)*g (j,i) else 0)]
        ring
  rw [hs]
  simp only [tensorToWedgePair]
  have hm (i : WedgePairIndex Q) :
      Real.sqrt 2*f i.val*(Real.sqrt 2*g i.val) = 2*(f i.val*g i.val) := by
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * (f i.val * g i.val) := by ring
      _ = _ := by rw [h]
  simp_rw [hm]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp) (fun i => f i*g i)).symm

theorem tensorToWedgePair_norm (Q : ℕ) (f : SpinIndex Q Q → ℝ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) :
    vectorNormSq (tensorToWedgePair Q f) = vectorNormSq f := by
  simpa only [vectorNormSq,pow_two] using antisymmetric_pairing Q f f hf hf

noncomputable def pairCoupledWedge (Q r : ℕ) (hr : r ≤ Q) (n : ℕ) : WedgePairIndex Q → ℝ :=
  tensorToWedgePair Q (pairCoupledTensor Q r hr n)

theorem pairCoupledWedge_norm (Q r n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (hn : n ≤ genericCoupledWeight Q Q r) :
    vectorNormSq (pairCoupledWedge Q r hr n) = 1 := by
  rw [pairCoupledWedge,tensorToWedgePair_norm Q _ (pairCoupledTensor_antisymmetric Q r n hr ho)]
  exact pairCoupledTensor_norm Q r n hr hn

end Laughlin.Spin

end OAI
