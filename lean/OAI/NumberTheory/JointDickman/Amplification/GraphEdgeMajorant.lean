import OAI.NumberTheory.JointDickman.Probability.GraphResidueNormalization
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphBounds

namespace OAI

/-! # The three-root majorant for the actual arithmetic edge weights -/

namespace JointDickman
open Finset

noncomputable def graphGoodPrimes (B a b c : ℕ) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => ¬p ∣ a ∧ ¬p ∣ b ∧ ¬p ∣ c)

noncomputable def graphResidueEnvelope (B a b c : ℕ) (j : ℤ) (n : ℕ) : ℝ :=
  (auxiliaryRatio B^(1/2 : ℝ))^3 * ∏ p ∈ graphGoodPrimes B a b c,
    residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
    residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
    residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p)

theorem divisorEdge_residue_majorant {a b c N : ℕ} {j : ℤ}
    (B : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    baseArithmeticResidueWeight B (divisorEdgeInverse a b c n) *
      baseArithmeticResidueWeight B (n/b) *
      baseArithmeticResidueWeight B (((n : ℤ)+j).toNat/a) ≤
      graphResidueEnvelope B a b c j n := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  obtain ⟨hqa,hqb⟩ := divisorEdge_new_quotients ha hb hc he hcop hn
  have hnb : n = b*(n/b) := (Nat.mul_div_cancel' (mem_filter.mp hn).2.1).symm
  have hend : (n : ℤ)+j = ((a*((b*divisorEdgeInverse a b c n+1)/c) : ℕ) : ℤ) := by
    have h := natural_divisor_edge_endpoints hc hca hcb he
    rwa [hback] at h
  have hcn : c*n = a*b*divisorEdgeInverse a b c n+b := by
    calc
      c*n = c*(b*((a*divisorEdgeInverse a b c n+1)/c)) :=
        congrArg (fun x : ℕ => c*x) hback.symm
      _ = b*(c*((a*divisorEdgeInverse a b c n+1)/c)) := by ring
      _ = b*(a*divisorEdgeInverse a b c n+1) := by rw [Nat.mul_div_cancel' hca]
      _ = _ := by ring
  have hend' : (n : ℤ)+j = (a : ℤ)*(((n : ℤ)+j).toNat/a : ℕ) := by
    rw [← hqb]
    exact hend
  exact graph_quotient_residue_majorant B (graphGoodPrimes B a b c)
    (filter_subset _ _) a b c _ _ _ n j
    (fun p hp => (mem_filter.mp hp).2.1)
    (fun p hp => (mem_filter.mp hp).2.2.1)
    (fun p hp => (mem_filter.mp hp).2.2.2) hnb hend' hcn

theorem arithmeticGraphPairWeight_le_base (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (a b c : ℕ) (j : ℤ) (n : ℕ) :
    arithmeticGraphPairWeight B L τ C u v a b c j n ≤
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        (baseArithmeticResidueWeight B (divisorEdgeInverse a b c n) *
          baseArithmeticResidueWeight B (n/b) *
          baseArithmeticResidueWeight B (((n : ℤ)+j).toNat/a)) := by
  have hfac (d l : ℕ) (w : ℝ) (hw : w ≤ 1) :
      (regularCoefficientWeight B L τ C d * arithmeticResidueWeight B L τ C l)*w ≤
        coefficientWeight B d * baseArithmeticResidueWeight B l := by
    apply (mul_le_of_le_one_right (mul_nonneg (regularCoefficientWeight_nonneg B L τ C d)
      (regularResidueWeight_nonneg B L τ C _)) hw).trans
    exact mul_le_mul (regularCoefficientWeight_le B L τ C d)
      (arithmeticResidueWeight_le_base B L τ C l)
      (regularResidueWeight_nonneg B L τ C _) (coefficientWeight_nonneg B d)
  have hC := hfac c (divisorEdgeInverse a b c n) (u c) (hu c).2
  have hA := hfac a (n/b) (v a c) (hv a c).2
  have hB := hfac b (((n : ℤ)+j).toNat/a) (v b c) (hv b c).2
  have hleft : 0 ≤ (u c * regularCoefficientWeight B L τ C c *
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n)) *
      (regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C (n/b) * v a c) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hu c).1 (regularCoefficientWeight_nonneg B L τ C c))
      (regularResidueWeight_nonneg B L τ C _))
      (mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C a)
        (regularResidueWeight_nonneg B L τ C _)) (hv a c).1)
  have hA0 := mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C a)
    (regularResidueWeight_nonneg B L τ C (coefficientPrimeSet B (n/b)))) (hv a c).1
  have hC0 := mul_nonneg (coefficientWeight_nonneg B c)
    (baseArithmeticResidueWeight_nonneg B (divisorEdgeInverse a b c n))
  have hB0 := mul_nonneg (coefficientWeight_nonneg B b)
    (baseArithmeticResidueWeight_nonneg B (((n : ℤ)+j).toNat/a))
  have hCA := mul_le_mul hC hA hA0 hC0
  have hCAB := mul_le_mul_of_nonneg_right hCA hB0
  unfold arithmeticGraphPairWeight
  calc
    _ ≤ ((regularCoefficientWeight B L τ C c *
        arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n))*u c) *
      (regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C (n/b)*v a c) *
        (coefficientWeight B b * baseArithmeticResidueWeight B (((n : ℤ)+j).toNat/a)) := by
      have hh := mul_le_mul_of_nonneg_left hB hleft
      convert hh using 1; ring
    _ ≤ _ := by convert hCAB using 1; ring

theorem arithmeticGraphPairWeight_residue_bound {B L a b c N : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    {j : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    arithmeticGraphPairWeight B L τ C u v a b c j n ≤
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        graphResidueEnvelope B a b c j n :=
  (arithmeticGraphPairWeight_le_base B L τ C u v hu hv a b c j n).trans
    (mul_le_mul_of_nonneg_left (divisorEdge_residue_majorant B ha hb hc he hcop hn)
      (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B c) (coefficientWeight_nonneg B a))
        (coefficientWeight_nonneg B b)))

theorem divisorEdge_small_endpoint {a b c T N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) (hbT : b < 2*(T*c))
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) : n < 2*T*N := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨hmN,ham,_,hca,_⟩ := mem_filter.mp hm
  have hN : 0 < N := Nat.pos_of_ne_zero (by intro h; simp [h] at hmN)
  have hcn : c*n = b*(a*divisorEdgeInverse a b c n+1) := by
    calc
      c*n = c*(b*((a*divisorEdgeInverse a b c n+1)/c)) :=
        congrArg (fun x : ℕ => c*x) hback.symm
      _ = b*(c*((a*divisorEdgeInverse a b c n+1)/c)) := by ring
      _ = _ := by rw [Nat.mul_div_cancel' hca]
  have h1 : c*n ≤ b*N := by rw [hcn]; exact Nat.mul_le_mul_left b (by omega)
  have h2 : b*N < (2*(T*c))*N := Nat.mul_lt_mul_of_pos_right hbT hN
  have hh : c*n < c*(2*T*N) := by nlinarith [h1.trans_lt h2]
  exact Nat.lt_of_mul_lt_mul_left hh

end JointDickman

end OAI
