import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The finite probability estimate in the phase argument

This is the Hellinger-affinity calculation in §7, proof of `phase:quantile-gap`,
of *A uniform Hilbert transform estimate for Lipschitz directions*.
The finite probability calculation is proved directly.
-/

open scoped BigOperators

namespace LipschitzHilbert

/-- Hellinger affinity of finite probability weights. -/
noncomputable def affinity {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i) * Real.sqrt (q i)

/-- Squared total variation estimate, before division of the `ℓ¹` distance by two. -/
theorem l1_sq_le_affinity {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (∑ i, |p i - q i|) ^ 2 ≤ 4 * (1 - affinity p q ^ 2) := by
  classical
  have hid (i : ι) :
      |p i - q i| = |Real.sqrt (p i) - Real.sqrt (q i)| *
        (Real.sqrt (p i) + Real.sqrt (q i)) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
  have hm : (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) =
      2 - 2 * affinity p q := by
    have hi (i : ι) : |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2 =
        p i + q i - 2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by
      rw [sq_abs, sub_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
      ring
    simp_rw [hi]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hp1, hq1, affinity]
    ring
  have ha : (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) =
      2 + 2 * affinity p q := by
    have hi (i : ι) : (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 =
        p i + q i + 2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by
      rw [add_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
      ring
    simp_rw [hi]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1, affinity]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun i => |Real.sqrt (p i) - Real.sqrt (q i)|)
    (fun i => Real.sqrt (p i) + Real.sqrt (q i))
  simp_rw [← hid] at hcs
  rw [hm, ha] at hcs
  nlinarith

/-- Each event deficit is at most the total variation distance. -/
theorem event_deficit_le_l1_half {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (s : Finset ι) :
    2 * |∑ i ∈ s, (p i - q i)| ≤ ∑ i, |p i - q i| := by
  classical
  have hsum : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
  have hcomp : ∑ i ∈ Finset.univ \ s, (p i - q i) =
      -(∑ i ∈ s, (p i - q i)) := by
    have ht := Finset.sum_sdiff (f := fun i => p i - q i) (Finset.subset_univ s)
    rw [hsum] at ht
    linarith
  have hs := Finset.abs_sum_le_sum_abs (f := fun i => p i - q i) (s := s)
  have ht := Finset.abs_sum_le_sum_abs (f := fun i => p i - q i)
    (s := Finset.univ \ s)
  rw [hcomp, abs_neg] at ht
  have hadd := Finset.sum_sdiff (f := fun i => |p i - q i|) (Finset.subset_univ s)
  linarith

/-- The event estimate used to turn a quantile deficit into a fourth-moment gap. -/
theorem event_deficit_sq_le_one_sub_affinity_sq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) (s : Finset ι) :
    (∑ i ∈ s, (p i - q i)) ^ 2 ≤ 1 - affinity p q ^ 2 := by
  have h1 := event_deficit_le_l1_half p q hp1 hq1 s
  have h2 := l1_sq_le_affinity p q hp hq hp1 hq1
  have hn : 0 ≤ ∑ i, |p i - q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h3 : (2 * |∑ i ∈ s, (p i - q i)|) ^ 2 ≤ (∑ i, |p i - q i|) ^ 2 :=
    (sq_le_sq₀ (by positivity) hn).mpr h1
  rw [mul_pow, sq_abs] at h3
  nlinarith

/-- The completed triple law may have mass less than one. Adjoining its missing
mass at one point, where the independent law has mass zero, preserves affinity. -/
theorem subprobability_event_deficit_sq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i ≤ 1) (hq1 : ∑ i, q i = 1) (s : Finset ι) :
    (∑ i ∈ s, (q i - p i)) ^ 2 ≤ 1 - affinity p q ^ 2 := by
  classical
  let p' : Option ι → ℝ := fun i => i.elim (1 - ∑ j, p j) p
  let q' : Option ι → ℝ := fun i => i.elim 0 q
  have hp' : ∀ i, 0 ≤ p' i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hp1
    | some i => exact hp i
  have hq' : ∀ i, 0 ≤ q' i := by
    intro i
    cases i with
    | none => exact le_rfl
    | some i => exact hq i
  have hp1' : ∑ i, p' i = 1 := by simp [p', Fintype.sum_option]
  have hq1' : ∑ i, q' i = 1 := by simp [q', Fintype.sum_option, hq1]
  have ha : affinity p' q' = affinity p q := by
    simp [affinity, Fintype.sum_option, p', q']
  have hs : (∑ i ∈ s.image Option.some, (p' i - q' i)) =
      -(∑ i ∈ s, (q i - p i)) := by
    rw [Finset.sum_image]
    · simp only [p', q', Option.elim_some, Finset.sum_sub_distrib]
      ring
    · intro a _ b _ hab
      exact Option.some.inj hab
  have h := event_deficit_sq_le_one_sub_affinity_sq p' q' hp' hq' hp1' hq1'
    (s.image Option.some)
  rwa [hs, neg_sq, ha] at h

/-- A definite event deficit forces the strict fourth-moment gain. This is the
last algebraic step of the manuscript's quantile-gap argument. -/
theorem strict_gap_of_event_deficit {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i ≤ 1) (hq1 : ∑ i, q i = 1) (s : Finset ι)
    {Q g : ℝ} (hQ : 0 ≤ Q) (hg : 0 ≤ g)
    (hgain : Q ^ 2 ≤ affinity p q)
    (hdeficit : g ≤ ∑ i ∈ s, (q i - p i)) :
    Q ≤ 1 - g ^ 2 / 4 := by
  have hevent := subprobability_event_deficit_sq p q hp hq hp1 hq1 s
  have hd : 0 ≤ ∑ i ∈ s, (q i - p i) := hg.trans hdeficit
  have hgsq : g ^ 2 ≤ (∑ i ∈ s, (q i - p i)) ^ 2 :=
    (sq_le_sq₀ hg hd).mpr hdeficit
  have haf : 0 ≤ affinity p q := (sq_nonneg Q).trans hgain
  have hfour : Q ^ 4 ≤ affinity p q ^ 2 := by
    have ht := (sq_le_sq₀ (sq_nonneg Q) haf).mpr hgain
    nlinarith
  have hpoly : Q ^ 4 ≥ 1 - 4 * (1 - Q) := by
    nlinarith [sq_nonneg (Q - 1), mul_nonneg (sq_nonneg (Q - 1))
      (show 0 ≤ Q ^ 2 + 2 * Q + 3 by positivity)]
  nlinarith

end LipschitzHilbert

end OAI
