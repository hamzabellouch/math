import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_exp_le {α : Type*} [Fintype α] (p : PMF α)
    (X : α → ℝ) (c v lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ a ∈ p.support, |X a| ≤ c)
    (hmean : pmfMean p X ≤ 0) (hvar : pmfMean p (fun a => X a ^ 2) ≤ v) :
    pmfMean p (fun a => Real.exp (lam * X a)) ≤ Real.exp (lam ^ 2 * v) := by
  have hpt (a : α) (ha : a ∈ p.support) :
      Real.exp (lam * X a) ≤ 1 + lam * X a + lam ^ 2 * X a ^ 2 := by
    have hb : |lam * X a| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlam]
      exact (mul_le_mul_of_nonneg_left (hbounded a ha) hlam).trans hclam
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hb)).2
    nlinarith
  calc
    _ ≤ pmfMean p (fun a => (1 + lam * X a) + lam ^ 2 * X a ^ 2) :=
      pmfMean_mono p hpt
    _ = 1 + lam * pmfMean p X + lam ^ 2 * pmfMean p (fun a => X a ^ 2) := by
      rw [pmfMean_add, pmfMean_add, pmfMean_const, pmfMean_const_mul,
        pmfMean_const_mul]
    _ ≤ 1 + lam ^ 2 * v := by
      have hs := mul_le_mul_of_nonneg_left hmean hlam
      have hv := mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
      nlinarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (lam ^ 2 * v)

noncomputable def markovLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α) : ℕ → PMF α
  | 0 => initial
  | k + 1 => (markovLaw initial K k).bind (K k)

theorem markovMean_potential_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (Z : ℕ → α → ℝ)
    (hstep : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (Z (k + 1)) ≤ Z k a) (k : ℕ) :
    pmfMean (markovLaw initial K k) (Z k) ≤ pmfMean initial (Z 0) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [markovLaw, pmfMean_bind]
    exact (pmfMean_mono _ (hstep k)).trans ih

theorem markovMean_exp_compensated_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c lam : ℝ)
    (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) :
    pmfMean (markovLaw initial K k)
      (fun a => Real.exp (lam * X k a - lam ^ 2 * V k a)) ≤
      pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) := by
  apply markovMean_potential_le initial K
    (fun k a => Real.exp (lam * X k a - lam ^ 2 * V k a))
  intro j a ha
  have hmgf := pmfMean_exp_le (K j a) (fun b => X (j + 1) b - X j a)
    c (incrementVar j a) lam hlam hclam (hbounded j a ha) (hmean j a ha) (hvar j a ha)
  have heq : pmfMean (K j a) (fun b => Real.exp (lam * X (j + 1) b - lam ^ 2 * V (j + 1) b)) =
      Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        pmfMean (K j a) (fun b => Real.exp (lam * (X (j + 1) b - X j a))) := by
    rw [← pmfMean_const_mul]
    apply pmfMean_congr
    intro b hb
    rw [hcounter j a ha b hb, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        Real.exp (lam ^ 2 * incrementVar j a) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pmfMean_compensated_tail {α : Type*} [Fintype α] (p : PMF α)
    (X V : α → ℝ) (lam r v : ℝ) (hlam : 0 ≤ lam)
    (hmgf : pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) ≤ 1) :
    pmfMean p (fun a => if r ≤ X a ∧ V a ≤ v then 1 else 0) ≤
      Real.exp (-lam * r + lam ^ 2 * v) := by
  classical
  have hevent (a : α) :
      (if r ≤ X a ∧ V a ≤ v then (1 : ℝ) else 0) ≤
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v) := by
    split_ifs with ha
    · rw [← Real.exp_add, Real.one_le_exp_iff]
      have hx := mul_le_mul_of_nonneg_left ha.1 hlam
      have hv := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg lam)
      linarith
    · positivity
  calc
    _ ≤ pmfMean p (fun a =>
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v)) :=
      pmfMean_mono p (fun a _ => hevent a)
    _ = pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) *
        Real.exp (-lam * r + lam ^ 2 * v) := pmfMean_mul_const _ _ _
    _ ≤ 1 * Real.exp (-lam * r + lam ^ 2 * v) :=
      mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = _ := one_mul _

theorem finite_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c : ℝ) (hc : 0 < c)
    (hinitial : ∀ a ∈ initial.support, X 0 a ≤ 0 ∧ 0 ≤ V 0 a)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) (r v : ℝ) (hr : 0 < r) (hv : 0 ≤ v) :
    pmfMean (markovLaw initial K k)
      (fun a => if r ≤ X k a ∧ V k a ≤ v then 1 else 0) ≤
      Real.exp (-r ^ 2 / (4 * (v + c * r))) := by
  classical
  let A : ℝ := v + c * r
  have hA : 0 < A := by dsimp [A]; positivity
  let lam : ℝ := r / (2 * A)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hclam : lam * c ≤ 1 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_pos hc hr]
  have hmgf := markovMean_exp_compensated_le initial K X V incrementVar c lam hlam hclam
    hbounded hmean hvar hcounter k
  have hi : pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) ≤ 1 := by
    rw [← pmfMean_const initial 1]
    apply pmfMean_mono
    intro a ha
    apply Real.exp_le_one_iff.mpr
    obtain ⟨hx, hv⟩ := hinitial a ha
    have hx' := mul_le_mul_of_nonneg_left hx hlam
    have hv' := mul_nonneg (sq_nonneg lam) hv
    linarith
  have hhalf : lam * v ≤ r / 2 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_nonneg hc.le (sq_nonneg r)]
  have hexponent : -lam * r + lam ^ 2 * v ≤ -r ^ 2 / (4 * (v + c * r)) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf hlam
    calc
      _ ≤ -lam * r / 2 := by nlinarith
      _ = _ := by
        dsimp [lam]
        change -(r / (2 * A)) * r / 2 = -r ^ 2 / (4 * A)
        field_simp
        ring
  exact (pmfMean_compensated_tail _ (X k) (V k) lam r v hlam (hmgf.trans hi)).trans
    (Real.exp_le_exp.mpr hexponent)

end SharpTerminalLeave

end

end OAI
