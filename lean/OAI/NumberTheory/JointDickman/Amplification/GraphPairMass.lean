import OAI.NumberTheory.JointDickman.Counting.GraphCoefficientMass

namespace OAI

/-! # A periodic upper bound for each actual graph representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphResidueEnvelope_nonneg (B a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ graphResidueEnvelope B a b c j n := by
  unfold graphResidueEnvelope
  apply mul_nonneg
  · have hR : 0 ≤ auxiliaryRatio B := by unfold auxiliaryRatio; positivity
    exact pow_nonneg (Real.rpow_nonneg hR _) _
  · exact prod_nonneg (fun p _ => mul_nonneg
      (mul_nonneg (residueWeight_nonneg _ _ (by norm_num))
        (residueWeight_nonneg _ _ (by norm_num))) (residueWeight_nonneg _ _ (by norm_num)))

theorem graphEdgeEnvelope_nonneg (B a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ graphEdgeEnvelope B a b c j n := by
  classical
  unfold graphEdgeEnvelope
  split_ifs
  · exact graphResidueEnvelope_nonneg B a b c j n
  · rfl

theorem graphPair_mass_le_prefix {B L T a b c : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (hu : ∀ d, u d ∈ Set.Icc (0 : ℝ) 1)
    {j : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs) (N : ℕ) :
    (∑ n ∈ divisorEdgeNew a b c N j,
      arithmeticGraphPairWeight B L τ C u (amplificationInnerWeight T) a b c j n) ≤
    (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
      ∑ n ∈ range (2*T*N), graphEdgeEnvelope B a b c j n := by
  classical
  let w := arithmeticGraphPairWeight B L τ C u (amplificationInnerWeight T) a b c j
  let E := divisorEdgeNew a b c N j
  have hsupport (n : ℕ) (hn : n ∈ E) (hw : w n ≠ 0) : n < 2*T*N := by
    have hv : amplificationInnerWeight T b c ≠ 0 := by
      intro hv
      apply hw
      simp only [w, arithmeticGraphPairWeight, hv, mul_zero]
    exact divisorEdge_small_endpoint ha hc he hcop (amplificationInnerWeight_support hv).2 hn
  have hfilter : (∑ n ∈ E, w n) = ∑ n ∈ E.filter (fun n => n < 2*T*N), w n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (hsupport n hn hne)
  rw [show (∑ n ∈ divisorEdgeNew a b c N j,
      arithmeticGraphPairWeight B L τ C u (amplificationInnerWeight T) a b c j n) =
      ∑ n ∈ E.filter (fun n => n < 2*T*N), w n from hfilter]
  rw [mul_sum]
  apply (sum_le_sum (fun n hn => ?_)).trans
    (sum_le_sum_of_subset_of_nonneg (fun n hn => mem_range.mpr (mem_filter.mp hn).2)
      (fun n _ _ => mul_nonneg (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B c)
        (coefficientWeight_nonneg B a)) (coefficientWeight_nonneg B b))
        (graphEdgeEnvelope_nonneg B a b c j n)))
  have hn' := (mem_filter.mp hn).1
  have hbnd := arithmeticGraphPairWeight_residue_bound (B := B) (L := L) τ C u (amplificationInnerWeight T)
    hu (fun _ _ => amplificationBump_bounds _) ha hb hc he hcop hn'
  have hcong := (mem_filter.mp hn').2
  have hcong' : b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j := ⟨hcong.1,hcong.2.1⟩
  simpa only [w, graphEdgeEnvelope, ite_eq_left hcong'] using hbnd

theorem mean_scaled_multiple {f : ℕ → ℝ} {μ : ℝ}
    (h : Tendsto (fun N => (∑ n ∈ range N, f n)/(N : ℝ)) atTop (𝓝 μ))
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N => (∑ n ∈ range (k*N), f n)/(N : ℝ)) atTop (𝓝 ((k : ℝ)*μ)) := by
  have htop : Tendsto (fun N : ℕ => k*N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id
  have ht := (h.comp htop).const_mul (k : ℝ)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  dsimp only [Function.comp_def]
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem graphPair_majorant_tendsto {a b T : ℕ} [NeZero a] [NeZero b]
    (hT : 0 < T) (hab : a.Coprime b) (B c : ℕ) (j : ℤ)
    (hj : ∀ p ∈ graphGoodPrimes B a b c, (j : ZMod p) ≠ 0)
    (he : (a : ℤ) = b+j*c) :
    Tendsto (fun N : ℕ =>
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        (∑ n ∈ range (2*T*N), graphEdgeEnvelope B a b c j n)/(N : ℝ))
      atTop (𝓝 ((coefficientWeight B c * coefficientWeight B a * coefficientWeight B b) *
        (2*(T : ℝ))*graphEdgeMean B a b c)) := by
  have h := (mean_scaled_multiple (graphEdgeEnvelope_average_tendsto hab B c j hj he)
    (Nat.mul_pos (by norm_num : 0 < 2) hT)).const_mul
      (coefficientWeight B c * coefficientWeight B a * coefficientWeight B b)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_assoc] using h

end JointDickman

end OAI
