import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.ZeroLeafRateFormula

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation
open MatrixMultiplication.JointEntropyMax

namespace MatrixMultiplication.JointGibbsApproximation

def marginalError {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ) : ℝ :=
  ∑ b, |(q.map f).mass b - (p.map f).mass b| * |v b|

theorem marginalError_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    0 ≤ marginalError p q f v :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem entropy_le_crossEntropy_of_support {A : Type*} [Fintype A]
    (p q : FiniteLaw A) (hsupport : ∀ a, p.mass a = 0 → q.mass a = 0) :
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) := by
  have hterm (a : A) :
      entropyTerm (q.mass a) ≤ -q.mass a * Real.log (p.mass a) + p.mass a - q.mass a := by
    by_cases hp : p.mass a = 0
    · simp [hp, hsupport a hp]
    · exact entropyTerm_le_crossEntropyTerm
        (lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)) (q.nonneg a)
  calc
    finiteEntropy q.mass ≤
        ∑ a, (-q.mass a * Real.log (p.mass a) + p.mass a - q.mass a) :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = ∑ a, -q.mass a * Real.log (p.mass a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.total, q.total]
      ring

private theorem potential_difference_le {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    (∑ a, p.mass a * v (f a)) - (∑ a, q.mass a * v (f a)) ≤
      marginalError p q f v := by
  rw [sum_mass_mul_coordinate p f v, sum_mass_mul_coordinate q f v,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro b _
  calc
    (p.map f).mass b * v b - (q.map f).mass b * v b =
        ((p.map f).mass b - (q.map f).mass b) * v b := by ring
    _ ≤ |((p.map f).mass b - (q.map f).mass b) * v b| := le_abs_self _
    _ = |(q.map f).mass b - (p.map f).mass b| * |v b| := by
      rw [abs_mul, abs_sub_comm]

theorem entropy_le_of_marginal_errors_of_support
    {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    (p q : FiniteLaw A) (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hsupport : ∀ a, p.mass a = 0 → q.mass a = 0)
    (hlog : ∀ a, 0 < p.mass a →
      Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c) :
    finiteEntropy q.mass ≤ finiteEntropy p.mass +
      marginalError p q fX u + marginalError p q fY v + marginalError p q fZ w := by
  have hexpand (r : FiniteLaw A) (hr : ∀ a, p.mass a = 0 → r.mass a = 0) :
      (∑ a, r.mass a * Real.log (p.mass a)) =
        (∑ a, r.mass a * u (fX a)) + (∑ a, r.mass a * v (fY a)) +
          (∑ a, r.mass a * w (fZ a)) - c := by
    have hterm (a : A) : r.mass a * Real.log (p.mass a) =
        r.mass a * (u (fX a) + v (fY a) + w (fZ a) - c) := by
      by_cases hp : p.mass a = 0
      · simp [hr a hp]
      · rw [hlog a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hp))]
    simp_rw [hterm, mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, r.total, one_mul]
  have hcross : (∑ a, -q.mass a * Real.log (p.mass a)) =
      finiteEntropy p.mass +
        ((∑ a, p.mass a * u (fX a)) - (∑ a, q.mass a * u (fX a))) +
        ((∑ a, p.mass a * v (fY a)) - (∑ a, q.mass a * v (fY a))) +
        ((∑ a, p.mass a * w (fZ a)) - (∑ a, q.mass a * w (fZ a))) := by
    have hp : finiteEntropy p.mass = -(∑ a, p.mass a * Real.log (p.mass a)) := by
      simp only [finiteEntropy, entropyTerm, neg_mul, Finset.sum_neg_distrib]
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [hp, hexpand p (fun _ h => h), hexpand q hsupport]
    ring
  calc
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) :=
      entropy_le_crossEntropy_of_support p q hsupport
    _ = _ := hcross
    _ ≤ _ := add_le_add
      (add_le_add (add_le_add le_rfl (potential_difference_le p q fX u))
        (potential_difference_le p q fY v)) (potential_difference_le p q fZ w)

theorem entropy_le_of_marginal_errors
    {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    (p q : FiniteLaw A) (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hp : ∀ a, 0 < p.mass a)
    (hlog : ∀ a, Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c) :
    finiteEntropy q.mass ≤ finiteEntropy p.mass +
      marginalError p q fX u + marginalError p q fY v + marginalError p q fZ w :=
  entropy_le_of_marginal_errors_of_support p q fX fY fZ u v w c
    (fun a h => ((hp a).ne' h).elim) (fun a _ => hlog a)

theorem tendsto_map_mass {I A B : Type*} [Fintype A] [Fintype B]
    {l : Filter I} {pN : I → FiniteLaw A} {p : FiniteLaw A}
    (h : ∀ a, Tendsto (fun n => (pN n).mass a) l (𝓝 (p.mass a)))
    (f : A → B) (b : B) :
    Tendsto (fun n => ((pN n).map f).mass b) l (𝓝 ((p.map f).mass b)) := by
  classical
  simp_rw [FiniteLaw.map_mass]
  apply tendsto_finsetSum
  intro a _
  by_cases hab : f a = b
  · simpa only [hab, ite_true] using h a
  · simp only [hab, ite_false]
    exact tendsto_const_nhds

theorem tendsto_marginalError {I A B : Type*} [Fintype A] [Fintype B]
    {l : Filter I} {pN : I → FiniteLaw A} {p : FiniteLaw A}
    (h : ∀ a, Tendsto (fun n => (pN n).mass a) l (𝓝 (p.mass a)))
    (f : A → B) (v : B → ℝ) :
    Tendsto (fun n => marginalError p (pN n) f v) l (𝓝 0) := by
  have hterm (b : B) :
      Tendsto (fun n => |((pN n).map f).mass b - (p.map f).mass b| * |v b|)
        l (𝓝 0) := by
    have hconst : Tendsto (fun _ : I => (p.map f).mass b) l
        (𝓝 ((p.map f).mass b)) := tendsto_const_nhds
    simpa only [sub_self, abs_zero, zero_mul] using
      ((tendsto_map_mass h f b).sub hconst).abs.mul_const |v b|
  simpa only [marginalError, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun b _ => hterm b)

theorem eventually_entropy_le_of_tendsto_of_support
    {I A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    {l : Filter I} (p : FiniteLaw A) (pN : I → FiniteLaw A)
    (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hlog : ∀ a, 0 < p.mass a →
      Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c)
    (hN : ∀ a, Tendsto (fun n => (pN n).mass a) l (𝓝 (p.mass a)))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in l, ∀ q : FiniteLaw A,
      (∀ a, p.mass a = 0 → q.mass a = 0) →
      (q.map fX).mass = ((pN n).map fX).mass →
      (q.map fY).mass = ((pN n).map fY).mass →
      (q.map fZ).mass = ((pN n).map fZ).mass →
      finiteEntropy q.mass ≤ finiteEntropy p.mass + η := by
  have herror : Tendsto (fun n => marginalError p (pN n) fX u +
      marginalError p (pN n) fY v + marginalError p (pN n) fZ w) l (𝓝 0) := by
    simpa only [add_zero] using
      ((tendsto_marginalError hN fX u).add (tendsto_marginalError hN fY v)).add
        (tendsto_marginalError hN fZ w)
  have hsmall := herror.eventually (gt_mem_nhds hη)
  filter_upwards [hsmall] with n hn
  intro q hs hX hY hZ
  have hbound := entropy_le_of_marginal_errors_of_support p q fX fY fZ u v w c hs hlog
  have hx : marginalError p q fX u = marginalError p (pN n) fX u := by
    unfold marginalError
    rw [hX]
  have hy : marginalError p q fY v = marginalError p (pN n) fY v := by
    unfold marginalError
    rw [hY]
  have hz : marginalError p q fZ w = marginalError p (pN n) fZ w := by
    unfold marginalError
    rw [hZ]
  rw [hx, hy, hz] at hbound
  linarith

theorem eventually_entropy_le_of_tendsto
    {I A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    {l : Filter I} (p : FiniteLaw A) (pN : I → FiniteLaw A)
    (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hp : ∀ a, 0 < p.mass a)
    (hlog : ∀ a, Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c)
    (hN : ∀ a, Tendsto (fun n => (pN n).mass a) l (𝓝 (p.mass a)))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in l, ∀ q : FiniteLaw A,
      (q.map fX).mass = ((pN n).map fX).mass →
      (q.map fY).mass = ((pN n).map fY).mass →
      (q.map fZ).mass = ((pN n).map fZ).mass →
      finiteEntropy q.mass ≤ finiteEntropy p.mass + η := by
  filter_upwards [eventually_entropy_le_of_tendsto_of_support p pN fX fY fZ u v w c
    (fun a _ => hlog a) hN hη] with n hn
  intro q hX hY hZ
  exact hn q (fun a h => ((hp a).ne' h).elim) hX hY hZ

end MatrixMultiplication.JointGibbsApproximation

end

end MatrixAllFields

end OAI
