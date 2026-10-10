import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Charge-transfer penalty at half filling

The diagonal part of the finite fermion model keeps long-range direct
Coulomb interactions. A symmetric interaction matrix with bounded absolute
row sums gives a gap against every nonsingly occupied configuration.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

/-- Symmetric row-sum control bounds the entire quadratic interaction form. -/
theorem symmetric_interaction_form_bound {m : ℕ} (V : Fin m → Fin m → ℝ)
    (d : Fin m → ℝ) (R : ℝ) (hsymm : ∀ i j, V i j = V j i)
    (hrow : ∀ i, ∑ j, |V i j| ≤ R) :
    |∑ i, ∑ j, V i j * d i * d j| ≤ R * ∑ i, d i ^ 2 := by
  have hterm (i j : Fin m) :
      |V i j * d i * d j| ≤ |V i j| * (d i ^ 2 + d j ^ 2) / 2 := by
    rw [abs_mul, abs_mul]
    have h : |d i| * |d j| ≤ (d i ^ 2 + d j ^ 2) / 2 := by
      nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
    convert mul_le_mul_of_nonneg_left h (abs_nonneg (V i j)) using 1 <;> ring
  have hsum : |∑ i, ∑ j, V i j * d i * d j| ≤
      ∑ i, ∑ j, |V i j| * (d i ^ 2 + d j ^ 2) / 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => hterm i j)
  have hsplit : (∑ i, ∑ j, |V i j| * (d i ^ 2 + d j ^ 2) / 2) =
      ∑ i, (∑ j, |V i j|) * d i ^ 2 := by
    simp only [mul_add, add_div, Finset.sum_add_distrib]
    have hswap : (∑ i, ∑ j, |V i j| * d j ^ 2 / 2) =
        ∑ i, ∑ j, |V i j| * d i ^ 2 / 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm j i]
    rw [hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∑ j, |V i j| * d i ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ ∑ i, (∑ j, |V i j|) * d i ^ 2 := hsum.trans_eq hsplit
    _ ≤ ∑ i, R * d i ^ 2 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
    _ = R * ∑ i, d i ^ 2 := (Finset.mul_sum _ _ _).symm

def occupationDeviation {m : ℕ} (occupation : Fin m → Fin 3) (i : Fin m) : ℝ :=
  (occupation i : ℕ) - 1

/-- Number conservation forces a charge defect to contain at least one
empty and one doubly occupied site, so its squared charge is at least two. -/
theorem occupation_defect_size {m : ℕ} (occupation : Fin m → Fin 3)
    (hfill : ∑ i, (occupation i : ℕ) = m)
    (hdefect : ¬ ∀ i, occupation i = 1) :
    2 ≤ ∑ i, occupationDeviation occupation i ^ 2 := by
  classical
  let emptySites := Finset.univ.filter (fun i => occupation i = 0)
  have hpoint (i : Fin m) : occupationDeviation occupation i ^ 2 =
      (occupation i : ℕ) - 1 + 2 * (if occupation i = 0 then (1 : ℝ) else 0) := by
    dsimp [occupationDeviation]
    generalize occupation i = k
    fin_cases k <;> norm_num
  have htotal : (∑ i, occupationDeviation occupation i ^ 2) =
      2 * (emptySites.card : ℝ) := by
    simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    have hfillR : (∑ i, ((occupation i : ℕ) : ℝ)) = (m : ℝ) := by exact_mod_cast hfill
    simp only [hfillR, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sub_self, zero_add]
    simp [emptySites]
  obtain ⟨i, hi⟩ := not_forall.mp hdefect
  have hpositive : 0 < ∑ i, occupationDeviation occupation i ^ 2 := by
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg _
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      have hne : occupationDeviation occupation i ≠ 0 := by
        intro hz
        have hv : ((occupation i : ℕ) : ℝ) = 1 := by
          change ((occupation i : ℕ) : ℝ) - 1 = 0 at hz
          linarith
        have hvN : (occupation i : ℕ) = 1 := by exact_mod_cast hv
        exact hi (Fin.ext hvN)
      exact sq_pos_of_ne_zero hne
  have hempty : 0 < emptySites.card := by
    have h : (0 : ℝ) < emptySites.card := by rw [htotal] at hpositive; linarith
    exact_mod_cast h
  have hcard : (1 : ℝ) ≤ emptySites.card := by exact_mod_cast hempty
  rw [htotal]
  linarith

def chargePenalty {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (occupation : Fin m → Fin 3) : ℝ :=
  U / 2 * ∑ i, occupationDeviation occupation i ^ 2 +
    (1 / 2 : ℝ) * ∑ i, ∑ j,
      V i j * occupationDeviation occupation i * occupationDeviation occupation j

/-- The direct Coulomb term and the compensating diagonal one-body term
are exactly the charge penalty minus its fixed scalar shift. Here `V i i=0`
is the physical off-site convention; the algebraic identity needs only
symmetry and conservation of total particle number. -/
theorem chargePenalty_offset_identity {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (occupation : Fin m → Fin 3) (hsymm : ∀ i j, V i j = V j i)
    (hfill : ∑ i, (occupation i : ℕ) = m) :
    U / 2 * (∑ i, ((occupation i : ℕ) : ℝ) * (((occupation i : ℕ) : ℝ) - 1)) +
        (1 / 2 : ℝ) * (∑ i, ∑ j,
          V i j * ((occupation i : ℕ) : ℝ) * ((occupation j : ℕ) : ℝ)) -
        (∑ i, (∑ j, V i j) * ((occupation i : ℕ) : ℝ)) =
      chargePenalty U V occupation - (1 / 2 : ℝ) * ∑ i, ∑ j, V i j := by
  let x : Fin m → ℝ := fun i => (occupation i : ℕ)
  have hfillR : (∑ i, x i) = (m : ℝ) := by
    dsimp [x]
    exact_mod_cast hfill
  have hlinear : (∑ i, (x i - 1)) = 0 := by
    simp [Finset.sum_sub_distrib, hfillR]
  have honsite : (∑ i, x i * (x i - 1)) = ∑ i, (x i - 1) ^ 2 := by
    have h : (∑ i, x i * (x i - 1)) =
        (∑ i, (x i - 1) ^ 2) + ∑ i, (x i - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h, hlinear, add_zero]
  have hcross : (∑ i, ∑ j, V i j * x j) = ∑ i, ∑ j, V i j * x i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hquadratic : (∑ i, ∑ j, V i j * (x i - 1) * (x j - 1)) =
      (∑ i, ∑ j, V i j * x i * x j) -
        2 * (∑ i, ∑ j, V i j * x i) + ∑ i, ∑ j, V i j := by
    have hexpand : (∑ i, ∑ j, V i j * (x i - 1) * (x j - 1)) =
        (∑ i, ∑ j, V i j * x i * x j) - (∑ i, ∑ j, V i j * x i) -
          (∑ i, ∑ j, V i j * x j) + ∑ i, ∑ j, V i j := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hexpand, hcross]
    ring
  change U / 2 * (∑ i, x i * (x i - 1)) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j * x i * x j) -
    (∑ i, (∑ j, V i j) * x i) = _
  simp only [chargePenalty, occupationDeviation]
  change _ = U / 2 * (∑ i, (x i - 1) ^ 2) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j * (x i - 1) * (x j - 1)) -
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j)
  rw [honsite, hquadratic]
  simp only [Finset.sum_mul]
  ring

/-- All number-conserving charge-transfer configurations cost at least
`U-R`, including every long-range interaction in the row-sum budget. -/
theorem chargePenalty_gap {m : ℕ} (U R : ℝ) (V : Fin m → Fin m → ℝ)
    (occupation : Fin m → Fin 3) (hsymm : ∀ i j, V i j = V j i)
    (hrow : ∀ i, ∑ j, |V i j| ≤ R) (hUR : R ≤ U)
    (hfill : ∑ i, (occupation i : ℕ) = m) (hdefect : ¬ ∀ i, occupation i = 1) :
    U - R ≤ chargePenalty U V occupation := by
  have hinteraction := (abs_le.mp
    (symmetric_interaction_form_bound V (occupationDeviation occupation) R hsymm hrow)).1
  have hsize := occupation_defect_size occupation hfill hdefect
  have hproduct := mul_nonneg (sub_nonneg.mpr hUR) (sub_nonneg.mpr hsize)
  unfold chargePenalty
  nlinarith

theorem chargePenalty_singly_occupied {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ) :
    chargePenalty U V (fun _ => 1) = 0 := by
  simp [chargePenalty, occupationDeviation]

/-- The configuration gap is a gap on arbitrary superpositions, including
spin spectators. The kernel consists of every singly occupied spin state. -/
theorem chargePenalty_complement_form_gap {m : ℕ} {Basis : Type*} [Fintype Basis]
    (U R : ℝ) (V : Fin m → Fin m → ℝ)
    (occupation : Basis → Fin m → Fin 3) (u : Basis → ℂ)
    (hsymm : ∀ i j, V i j = V j i) (hrow : ∀ i, ∑ j, |V i j| ≤ R)
    (hUR : R ≤ U) (hfill : ∀ s, ∑ i, (occupation s i : ℕ) = m)
    (hkernel : ∀ s, (∀ i, occupation s i = 1) → u s = 0) :
    (U - R) * ∑ s, ‖u s‖ ^ 2 ≤
      ∑ s, chargePenalty U V (occupation s) * ‖u s‖ ^ 2 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hsingle : ∀ i, occupation s i = 1
  · simp [hkernel s hsingle]
  · exact mul_le_mul_of_nonneg_right
      (chargePenalty_gap U R V (occupation s) hsymm hrow hUR (hfill s) hsingle)
      (sq_nonneg _)

end ContinuumCoulomb

end

end OAI
