import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Finite geometric buffers with controlled quadratic weight. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.HarmonicWeights

def mass (r m : ℕ) : ℝ := ∑ j ∈ Finset.range m, 1/((r:ℝ)+j)

lemma mass_nonneg (r m : ℕ) : 0 ≤ mass r m := by
  unfold mass
  exact Finset.sum_nonneg (fun j _ => by positivity)

lemma mass_doubling (r m : ℕ) (hr : 0 < r) (hrm : r ≤ m) :
    mass r m+1/3 ≤ mass r (2*m) := by
  have hm : 0 < (m:ℝ) := by exact_mod_cast (lt_of_lt_of_le hr hrm)
  have hc : (1/3:ℝ) ≤ ∑ j ∈ Finset.range m, 1/((r:ℝ)+(m+j)) := by
    calc
      _ = ∑ _j ∈ Finset.range m, 1/(3*(m:ℝ)) := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        field_simp
      _  ≤  _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjm : j < m := Finset.mem_range.mp hj
        apply one_div_le_one_div_of_le (by positivity)
        have hrm' : (r:ℝ) ≤ m := by exact_mod_cast hrm
        have hjm' : (j:ℝ) < m := by exact_mod_cast hjm
        linarith
  unfold mass at *
  rw [show 2*m=m+m by omega,Finset.sum_range_add]
  simp only [Nat.cast_add]
  linarith only [hc]

lemma mass_ge_blocks (r s : ℕ) (hr : 0 < r) : (s:ℝ)/3 ≤ mass r (2^s*r) := by
  induction s with
  | zero => simpa only [pow_zero,one_mul,Nat.cast_zero,zero_div] using mass_nonneg r r
  | succ s ih =>
    have hrm : r ≤ 2^s*r := by
      calc r=1*r := (one_mul r).symm
           _ ≤ 2^s*r := Nat.mul_le_mul_right r (Nat.one_le_pow s 2 (by omega))
    have h := mass_doubling r (2^s*r) hr hrm
    rw [show 2*(2^s*r)=2^(s+1)*r by rw [pow_succ]; ring] at h
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith

def weight (r m : ℕ) (j : ℕ) : ℝ := 4/(mass r m*((r:ℝ)+j))

lemma mass_pos (r m : ℕ) (hr : 0 < r) (hm : 0 < m) : 0 < mass r m := by
  unfold mass
  apply Finset.sum_pos' (fun j _ => by positivity)
  refine ⟨0,Finset.mem_range.mpr hm,?_⟩
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  positivity

lemma weight_pos (r m j : ℕ) (hr : 0 < r) (hm : 0 < m) : 0 < weight r m j := by
  have ht := mass_pos r m hr hm
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  unfold weight
  positivity

lemma sum_weight (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    ∑ j ∈ Finset.range m, weight r m j=4 := by
  have ht := mass_pos r m hr hm
  have he (j : ℕ) : weight r m j=(4/mass r m)*(1/((r:ℝ)+j)) := by
    simp only [weight,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  change (4/mass r m)*mass r m=4
  field_simp

lemma weight_le (r m j : ℕ) (hr : 0 < r) (hm : 0 < m) :
    weight r m j ≤ 4/mass r m := by
  have ht := mass_pos r m hr hm
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  apply div_le_div_of_nonneg_left (by norm_num) ht
  change mass r m ≤ mass r m*((r:ℝ)+j)
  nlinarith [Nat.cast_nonneg (α:=ℝ) j]

lemma energy_mass (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (b : ℕ → ℝ) (hb : ∀ j, j < m → b j ≤ 12*((r:ℝ)+j)) :
    ∑ j ∈ Finset.range m, (weight r m j)^2*b j ≤ 192/mass r m := by
  have ht := mass_pos r m hr hm
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  calc
    _  ≤  ∑ j ∈ Finset.range m, (192/(mass r m)^2)*(1/((r:ℝ)+j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hd : (r:ℝ)+j≠0 := ne_of_gt (by positivity)
      calc
        _  ≤  (weight r m j)^2*(12*((r:ℝ)+j)) := mul_le_mul_of_nonneg_left (hb j (Finset.mem_range.mp hj)) (sq_nonneg _)
        _ = _ := by unfold weight; field_simp; ring
    _ = _ := by
      rw [← Finset.mul_sum]
      change (192/(mass r m)^2)*mass r m=192/mass r m
      field_simp

theorem buffer_weights (r s : ℕ) (hr : 0 < r) (hs : 96 ≤ s)
    (b : ℕ → ℝ) (hb : ∀ j, j < 2^s*r → b j ≤ 12*((r:ℝ)+j)) :
    (∀ j, 0 < weight r (2^s*r) j ∧ weight r (2^s*r) j ≤ 1/8) ∧
    (∑ j ∈ Finset.range (2^s*r), weight r (2^s*r) j)=4 ∧
    (∑ j ∈ Finset.range (2^s*r), (weight r (2^s*r) j)^2*b j) ≤ 576/(s:ℝ) := by
  have hm : 0 < 2^s*r := Nat.mul_pos (pow_pos (by omega) _) hr
  have ht := mass_pos r (2^s*r) hr hm
  have hblocks := mass_ge_blocks r s hr
  have hs' : (96:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : 0 < (s:ℝ) := by linarith
  refine ⟨fun j => ⟨weight_pos r (2^s*r) j hr hm,?_⟩,sum_weight r (2^s*r) hr hm,?_⟩
  · exact (weight_le r (2^s*r) j hr hm).trans ((div_le_iff₀ ht).mpr (by linarith))
  · apply (energy_mass r (2^s*r) hr hm b hb).trans
    apply (div_le_div_iff₀ ht hs0).mpr
    linarith

end PolynomialPEPS.Subvolume.HarmonicWeights

end

end OAI
