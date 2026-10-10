import OAI.NumberTheory.JointDickman.Probability.GraphResidueMean
import OAI.NumberTheory.JointDickman.Amplification.GraphEdgeMajorant

namespace OAI

/-! # The exact density of the endpoint congruences and retained roots -/

namespace JointDickman
open Finset

noncomputable def graphEndpointResidue (a b : ℕ) (j : ℤ) (hab : a.Coprime b) :
    ZMod (a*b) :=
  (ZMod.chineseRemainder hab).symm (-(j : ZMod a), 0)

theorem graph_endpoint_congruence {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (j : ℤ) (n : ℕ) :
    (b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j) ↔
      (n : ZMod (a*b)) = graphEndpointResidue a b j hab := by
  have hn : (ZMod.chineseRemainder hab) (n : ZMod (a*b)) =
      ((n : ZMod a), (n : ZMod b)) := map_natCast _ _
  rw [graphEndpointResidue, ← (ZMod.chineseRemainder hab).apply_eq_iff_eq]
  change _ ↔ (ZMod.chineseRemainder hab) (n : ZMod (a*b)) =
    (ZMod.chineseRemainder hab) ((ZMod.chineseRemainder hab).symm (-(j : ZMod a), 0))
  rw [(ZMod.chineseRemainder hab).apply_symm_apply, hn, Prod.mk.injEq]
  rw [ZMod.natCast_eq_zero_iff, ← add_eq_zero_iff_eq_neg]
  have he : (n : ZMod a)+(j : ZMod a) = ((n : ℤ)+j : ℤ) := by
    simp only [Int.cast_add, Int.cast_natCast]
  rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact and_comm

open Classical in
/-- Exact finite-period mean; the coefficient congruences cost `1/(ab)`.
The three retained roots do not interact with this congruence. -/
theorem graph_endpoint_three_root_mean {a b c : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    [NeZero (∏ p ∈ P, p)] [∀ p : P, NeZero p.val]
    (hcop : (a*b).Coprime (∏ p ∈ P, p)) (j : ℤ)
    (ha : ∀ p ∈ P, ¬p ∣ a) (hb : ∀ p ∈ P, ¬p ∣ b) (hc : ∀ p ∈ P, ¬p ∣ c)
    (hj : ∀ p ∈ P, (j : ZMod p) ≠ 0) (he : (a : ℤ) = b+j*c) :
    (∑ x : ZMod (a*b*∏ p ∈ P, p),
      (if b ∣ x.val ∧ (a : ℤ) ∣ (x.val : ℤ)+j then (1 : ℝ) else 0) *
      ∏ p : P, residueWeight (1/2) (0 : ZMod p.val) (x.val : ZMod p.val) *
        residueWeight (1/2) (-(j : ZMod p.val)) (x.val : ZMod p.val) *
        residueWeight (1/2) ((b : ZMod p.val)*(c : ZMod p.val)⁻¹) (x.val : ZMod p.val)) /
        ((a : ℝ)*b*∏ p ∈ P, (p : ℝ)) =
      (1/((a : ℝ)*b)) * ∏ p ∈ P, (1-3/(2*(p : ℝ))) := by
  have hdist (p : P) :
      (0 : ZMod p.val) ≠ -(j : ZMod p.val) ∧
      (0 : ZMod p.val) ≠ (b : ZMod p.val)*(c : ZMod p.val)⁻¹ ∧
      -(j : ZMod p.val) ≠ (b : ZMod p.val)*(c : ZMod p.val)⁻¹ := by
    let : Fact p.val.Prime := ⟨hP p p.property⟩
    have hne (x : ℕ) (hx : ¬p.val ∣ x) : (x : ZMod p.val) ≠ 0 :=
      fun h => hx ((ZMod.natCast_eq_zero_iff x p.val).mp h)
    have he' : (a : ZMod p.val) = (b : ZMod p.val)+(j : ZMod p.val)*(c : ZMod p.val) := by
      simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul] using
        congrArg (fun x : ℤ => (x : ZMod p.val)) he
    simpa only [div_eq_mul_inv] using graph_roots_distinct (a : ZMod p.val) b c j
      (hne a (ha p p.property)) (hne b (hb p p.property)) (hne c (hc p p.property))
      (hj p p.property) he'
  have h := congruence_three_root_mean P hP hcop (graphEndpointResidue a b j hab)
    (fun p => (0 : ZMod p.val)) (fun p => -(j : ZMod p.val))
    (fun p => (b : ZMod p.val)*(c : ZMod p.val)⁻¹)
    (fun p => (hdist p).1) (fun p => (hdist p).2.1) (fun p => (hdist p).2.2)
  simp_rw [← graph_endpoint_congruence hab j] at h
  simpa only [Nat.cast_mul] using h

end JointDickman

end OAI
