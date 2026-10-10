import OAI.Combinatorics.ContingencyTables.Dense.GridBoundary
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Volume and mass of grid face neighbourhoods

The exact tube volume and a finite integral-cover bound used to turn the
interpolation shell gain into a weighted cut estimate.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def tubeLower (a : I → ℤ) (i : I) (r : ℝ) : I → ℝ :=
  fun j => if j = i then (a j : ℝ) + 1 - r else (a j : ℝ) - r

def tubeUpper (a : I → ℤ) (_i : I) (r : ℝ) : I → ℝ :=
  fun j => (a j : ℝ) + 1 + r

/-- An open rectangular neighbourhood of the positive `i`-face of a bin. -/
def faceTube (a : I → ℤ) (i : I) (r : ℝ) : Set (I → ℝ) :=
  Set.pi Set.univ fun j => Set.Ioo (tubeLower a i r j) (tubeUpper a i r j)

theorem faceTube_measurable (a : I → ℤ) (i : I) (r : ℝ) :
    MeasurableSet (faceTube a i r) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

omit [Fintype I] in
private theorem tube_width (a : I → ℤ) (i j : I) (r : ℝ) :
    tubeUpper a i r j - tubeLower a i r j = if j = i then 2 * r else 1 + 2 * r := by
  by_cases h : j = i <;> simp [tubeUpper, tubeLower, h] <;> ring

private theorem product_one_exception (u v : ℝ) (i : I) :
    (∏ j : I, if j = i then u else v) = u * v ^ (Fintype.card I - 1) := by
  have heq : (fun j : I => if j = i then u else v) = Function.update (fun _ => v) i u := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase]

theorem faceTube_volume (a : I → ℤ) (i : I) (r : ℝ) (hr : 0 ≤ r) :
    volume (faceTube a i r) =
      ENNReal.ofReal (2 * r * (1 + 2 * r) ^ (Fintype.card I - 1)) := by
  rw [faceTube, Real.volume_pi_Ioo]
  simp_rw [tube_width]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [product_one_exception]
  · intro j _
    split_ifs <;> positivity

theorem faceTube_volume_toReal (a : I → ℤ) (i : I) (r : ℝ) (hr : 0 ≤ r) :
    (volume (faceTube a i r)).toReal =
      2 * r * (1 + 2 * r) ^ (Fintype.card I - 1) := by
  rw [faceTube_volume a i r hr, ENNReal.toReal_ofReal (by positivity)]

private theorem reverse_bernoulli (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have haux : (1 + u) * (1 - ((n : ℝ) + 1) * u) ≤ 1 - (n : ℝ) * u := by
      have h := mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sq_nonneg u)
      nlinarith
    calc
      (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
          (1 + u) ^ n * ((1 + u) * (1 - ((n : ℝ) + 1) * u)) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) :=
        mul_le_mul_of_nonneg_left haux (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

/-- The manuscript's tube-volume bound follows without an exponential
estimate: the relevant power is at most two by reverse Bernoulli. -/
theorem faceTube_volume_le_one (a : I → ℤ) (i : I) (r : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 4)
    (hsize : (Fintype.card I - 1 : ℕ) * (2 * r) ≤ (1 / 2 : ℝ)) :
    (volume (faceTube a i r)).toReal ≤ 1 := by
  rw [faceTube_volume_toReal a i r hr]
  have hpow := pow_nonneg (show 0 ≤ 1 + 2 * r by linarith) (Fintype.card I - 1)
  have hbern := reverse_bernoulli (2 * r) (by linarith) (Fintype.card I - 1)
  have htwo : (1 + 2 * r) ^ (Fintype.card I - 1) ≤ 2 := by nlinarith
  nlinarith

omit [Fintype I] in
/-- A point near the positive face belongs to its rectangular tube. -/
theorem mem_faceTube_of_near (a : I → ℤ) (i : I) (r : ℝ) (z w : I → ℝ)
    (hw : ClosedBin a w) (hwi : w i = (a i : ℝ) + 1)
    (hd : ∀ j, |z j - w j| < r) : z ∈ faceTube a i r := by
  intro j _
  have h := abs_lt.mp (hd j)
  by_cases hj : j = i
  · subst j
    simp only [tubeLower, tubeUpper, ite_true]
    rw [hwi] at h
    constructor <;> linarith
  · simp only [tubeLower, tubeUpper, hj, ite_false]
    have hwj := hw j
    constructor <;> linarith

end ContingencyTables.GridBoundary

namespace ContingencyTables

open MeasureTheory
open scoped BigOperators

/-- Integrating a finite cover, allowing overlap and a null exceptional set.
This applies to the face tubes after removing grid hyperplanes. -/
theorem integral_finite_cover {X K : Type*} [MeasurableSpace X] [Fintype K]
    {μ : Measure X} (S : Set X) (E : K → Set X) (ρ : X → ℝ)
    (hS : MeasurableSet S) (hE : ∀ k, MeasurableSet (E k))
    (hiS : IntegrableOn ρ S μ) (hiE : ∀ k, IntegrableOn ρ (E k) μ)
    (hpos : ∀ k x, x ∈ E k → 0 ≤ ρ x)
    (hcover : ∀ᵐ x ∂μ, x ∈ S → ∃ k, x ∈ E k) :
    (∫ x in S, ρ x ∂μ) ≤ ∑ k, ∫ x in E k, ρ x ∂μ := by
  classical
  have hterm (k : K) (x : X) : 0 ≤ (E k).indicator ρ x := by
    by_cases hx : x ∈ E k
    · simpa [hx] using hpos k x hx
    · simp [hx]
  have hmono : S.indicator ρ ≤ᵐ[μ] fun x => ∑ k, (E k).indicator ρ x := by
    filter_upwards [hcover] with x hx
    by_cases hxS : x ∈ S
    · obtain ⟨k, hk⟩ := hx hxS
      simpa [hxS, hk] using
        (Finset.single_le_sum (fun j _ => hterm j x) (Finset.mem_univ k))
    · simpa [hxS] using Finset.sum_nonneg (fun k _ => hterm k x)
  have hint (k : K) : Integrable ((E k).indicator ρ) μ :=
    (hiE k).integrable_indicator (hE k)
  have hbound := integral_mono_ae (hiS.integrable_indicator hS)
    (integrable_finsetSum Finset.univ fun k _ => hint k) hmono
  rw [integral_indicator hS, integral_finsetSum Finset.univ (fun k _ => hint k)] at hbound
  simpa only [integral_indicator (hE _)] using hbound

end ContingencyTables

end OAI
