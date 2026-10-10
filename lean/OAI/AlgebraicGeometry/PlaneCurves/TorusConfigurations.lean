import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.AlgebraicGeometry.PlaneCurves.CollisionBounds
import OAI.AlgebraicGeometry.PlaneCurves.LineSmoothness
import OAI.AlgebraicGeometry.PlaneCurves.MarkedPoints
import OAI.AlgebraicGeometry.PlaneCurves.TorusCharts

namespace OAI

/-!
# Distinct embedded torus configurations and affine avoidance; Nonintegral differences of normalized marked parameters
-/

section

/-!
# Avoiding integral values of finitely many nonconstant affine functions
-/
namespace Nagata.W06

/-- Integer preimages of a nonconstant real affine map in a bounded interval are finite. -/
theorem finite_affine_integer_preimages (a b R : ℝ) (ha : a ≠ 0) :
    {x : ℝ | |x| ≤ R ∧ ∃ k : ℤ, a * x + b = k}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|a| * R + |b|)
  have hfin : ((fun k : ℤ => ((k : ℝ) - b) / a) ''
      Set.Icc (-(N : ℤ)) (N : ℤ)).Finite :=
    (Set.finite_Icc _ _).image _
  apply hfin.subset
  intro x hx
  obtain ⟨hRx, k, hk⟩ := hx
  have hbound : |(k : ℝ)| < (N : ℝ) := by
    calc
      |(k : ℝ)| = |a * x + b| := congrArg abs hk.symm
      _ ≤ |a * x| + |b| := abs_add_le _ _
      _ = |a| * |x| + |b| := by rw [abs_mul]
      _ ≤ |a| * R + |b| := add_le_add (mul_le_mul_of_nonneg_left hRx (abs_nonneg a)) le_rfl
      _ < N := hN
  have hb := abs_le.mp (le_of_lt hbound)
  have hklo : -(N : ℤ) ≤ k := by exact_mod_cast hb.1
  have hkhi : k ≤ (N : ℤ) := by exact_mod_cast hb.2
  refine ⟨k, ⟨hklo, hkhi⟩, ?_⟩
  apply (div_eq_iff ha).mpr
  linarith

/-- Simultaneous delta choice, with no additional finiteness hypothesis. -/
theorem exists_delta_avoiding_affine_integers {ι : Type*} [Finite ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : ρ < B) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 1 / 2 ∧ ρ + Δ * ρ / 9 < B ∧
      ∀ i (k : ℤ), a i * Δ + b i ≠ k := by
  let F : ι → Set ℝ := fun i => {x | |x| ≤ 1 ∧ ∃ k : ℤ, a i * x + b i = k}
  have hF : (⋃ i, F i).Finite := Set.finite_iUnion fun i =>
    finite_affine_integer_preimages (a i) (b i) 1 (ha i)
  obtain ⟨Δ, hΔ, hhalf, hslack, havoid⟩ := exists_delta_avoiding_finite hρ hB hF
  refine ⟨Δ, hΔ, hhalf, hslack, ?_⟩
  intro i k hk
  apply havoid
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_, k, hk⟩
  rw [abs_of_pos hΔ]
  linarith

end Nagata.W06

end

section

namespace Nagata.W06

/-- The simultaneous nonintegrality requirements in the source, together with delta slack.
The relation `h = 3*(d-3*m)` and positivity of `d-3*j` are retained explicitly. -/
theorem exists_source_nonintegral_delta {m u₀ : ℕ} {h d ρ ρstar B : ℝ}
    (hh : 0 < h) (hdegree : h = 3 * (d - 3 * (m : ℝ)))
    (hρ : 0 < ρ) (hB : ρ < B) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 1 / 2 ∧ ρ + Δ * ρ / 9 < B ∧
      (∀ (j : Fin (m + 1)) (k : ℤ),
        h / 9 * (ρstar - Δ) + ((m : ℝ) - (j.val : ℝ)) * ρstar ≠ k) ∧
      (∀ (j : Fin (u₀ + 1)), m < j.val → 0 < d - 3 * (j.val : ℝ) →
        ∀ k : ℤ, (h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9 * (ρstar - Δ) ≠ k) := by
  classical
  let J := {j : Fin (u₀ + 1) // m < j.val ∧ 0 < d - 3 * (j.val : ℝ)}
  let : Fintype J := inferInstance
  let a : Fin (m + 1) ⊕ J → ℝ := Sum.elim
    (fun _ => -(h / 9))
    (fun j => -((h - 9 * ((j.val.val : ℝ) - (m : ℝ))) / 9))
  let b : Fin (m + 1) ⊕ J → ℝ := Sum.elim
    (fun j => h / 9 * ρstar + ((m : ℝ) - (j.val : ℝ)) * ρstar)
    (fun j => (h - 9 * ((j.val.val : ℝ) - (m : ℝ))) / 9 * ρstar)
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    cases i with
    | inl j =>
      dsimp [a]
      exact neg_ne_zero.mpr (div_ne_zero (ne_of_gt hh) (by norm_num))
    | inr j =>
      have hj := j.property.2
      have hnum : 0 < h - 9 * ((j.val.val : ℝ) - (m : ℝ)) := by linarith
      dsimp [a]
      exact neg_ne_zero.mpr (div_ne_zero (ne_of_gt hnum) (by norm_num))
  obtain ⟨Δ, hΔ, hhalf, hslack, hall⟩ :=
    exists_delta_avoiding_affine_integers a b ha hρ hB
  refine ⟨Δ, hΔ, hhalf, hslack, ?_, ?_⟩
  · intro j k hk
    apply hall (Sum.inl j) k
    dsimp [a, b]
    calc
      -(h / 9) * Δ + (h / 9 * ρstar + ((m : ℝ) - (j.val : ℝ)) * ρstar) =
          h / 9 * (ρstar - Δ) + ((m : ℝ) - (j.val : ℝ)) * ρstar := by ring
      _ = k := hk
  · intro j hjm hjd k hk
    apply hall (Sum.inr ⟨j, hjm, hjd⟩) k
    dsimp [a, b]
    calc
      -((h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9) * Δ +
          (h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9 * ρstar =
          (h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9 * (ρstar - Δ) := by ring
      _ = k := hk

end Nagata.W06

end

section

/-!
# The simultaneous nine-plus-q marked torus configuration
-/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05
open Nagata.W21
open Filter
open scoped Topology

/-- Distinct exponents inside (0,1) define distinct actual torus points. -/
theorem rayTorusPoint_injective_on_unit_interval {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    Set.InjOn (fun s : ℝ => torusPointMk (positivePeriod τ hτ) (rayPoint τ s))
      (Set.Ioo 0 1) := by
  intro x hx y hy heq
  have horbit : torusOrbitSetoid (positivePeriod τ hτ) (rayPoint τ x) (rayPoint τ y) :=
    Quotient.exact heq
  obtain ⟨a, ha⟩ := (torusOrbitSetoid_iff_coe _ _ _).mp horbit
  have he : Complex.exp ((y * Real.log τ : ℝ) : ℂ) =
      (τ : ℂ) ^ a * Complex.exp ((x * Real.log τ : ℝ) : ℂ) := by
    simpa only [positivePeriod, rayPoint, Units.val_mk0] using ha
  obtain ⟨b, hb⟩ := exp_orbit_lattice hτ
    ((x * Real.log τ : ℝ) : ℂ) ((y * Real.log τ : ℝ) : ℂ) a he
  have hre : y * Real.log τ - x * Real.log τ = (a : ℝ) * Real.log τ := by
    simpa using congrArg Complex.re hb
  have hlog : Real.log τ ≠ 0 := ne_of_lt (Real.log_neg hτ hτ1)
  have hdiff : y - x = (a : ℝ) := by
    apply mul_right_cancel₀ hlog
    nlinarith [hre]
  exact (Nagata.W06.eq_of_sub_eq_integer hy.1 hy.2 hx.1 hx.2 a hdiff).symm

/-- The fixed lifts followed by the q moving lifts in the common exponential chart. -/
def coverTuple (τ x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) :
    Fin (9 + q) → ℂˣ :=
  fun t => Sum.elim (fun i => rayPoint τ (xi i)) (fun j => chartPoint τ x0 (ξ j))
    ((finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t)

/-- The corresponding actual torus tuple. -/
def torusTuple (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) : Fin (9 + q) → TorusPoint (positivePeriod τ hτ) :=
  fun t => torusPointMk (positivePeriod τ hτ) (coverTuple τ x0 xi ξ t)

@[simp] theorem coverTuple_left (τ x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    coverTuple τ x0 xi ξ (finSumFinEquiv (Sum.inl i)) = rayPoint τ (xi i) := by
  simp [coverTuple]

@[simp] theorem coverTuple_right (τ x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin q) :
    coverTuple τ x0 xi ξ (finSumFinEquiv (Sum.inr i)) = chartPoint τ x0 (ξ i) := by
  simp [coverTuple]

@[simp] theorem torusTuple_left (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    torusTuple τ hτ x0 xi ξ (finSumFinEquiv (Sum.inl i)) =
      torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)) := by
  unfold torusTuple
  rw [coverTuple_left]

@[simp] theorem torusTuple_right (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin q) :
    torusTuple τ hτ x0 xi ξ (finSumFinEquiv (Sum.inr i)) = torusChart τ hτ x0 (ξ i) := by
  unfold torusTuple torusChart
  rw [coverTuple_right]

theorem torusTuple_eq_sum (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    torusTuple τ hτ x0 xi ξ t =
      Sum.elim (fun i : Fin 9 => torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)))
        (fun j : Fin q => torusChart τ hτ x0 (ξ j))
        ((finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t) := by
  unfold torusTuple coverTuple
  cases (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t <;> rfl

/-- Pairwise distinctness of the complete source tuple, with every quantitative
common-chart bound explicit. No cubic embedding is assumed in this theorem. -/
theorem torusTuple_injective {τ R : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2)
    (hR : 0 < R) (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|)
    (hmargin : R < markedGap (1 / 2) xi * |Real.log τ|)
    {q : ℕ} (ξ : Fin q → ℂ) (hξ : Function.Injective ξ) (hξR : ∀ j, ‖ξ j‖ < R) :
    Function.Injective (torusTuple τ hτ (1 / 2) xi ξ) := by
  have hfixed : Function.Injective (fun i : Fin 9 =>
      torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i))) := by
    intro i j hij
    apply hxi
    exact rayTorusPoint_injective_on_unit_interval hτ hτ1
      ⟨(hxi_bounds i).1, by linarith [(hxi_bounds i).2]⟩
      ⟨(hxi_bounds j).1, by linarith [(hxi_bounds j).2]⟩ hij
  have hmoving : Function.Injective (fun j : Fin q => torusChart τ hτ (1 / 2) (ξ j)) := by
    intro i j hij
    exact hξ (torusChart_injective_on_disk hτ hR hRpi hlog (1 / 2) (hξR i) (hξR j) hij)
  have hcross : ∀ i : Fin 9, ∀ j : Fin q,
      torusChart τ hτ (1 / 2) (ξ j) ≠
        torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)) := by
    intro i j
    have hb := hxi_bounds i
    exact torusChart_avoids_mark hτ (by linarith) (by linarith)
      (markedGap_le (1 / 2) xi i).1 (markedGap_le (1 / 2) xi i).2 hmargin (hξR j)
  have hsum : Function.Injective (Sum.elim
      (fun i : Fin 9 => torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)))
      (fun j : Fin q => torusChart τ hτ (1 / 2) (ξ j))) := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hfixed hab)
      | inr j => exact False.elim (hcross i j hab.symm)
    | inr i =>
      cases b with
      | inl j => exact False.elim (hcross j i hab)
      | inr j => exact congrArg Sum.inr (hmoving hab)
  intro a b hab
  apply (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm.injective
  apply hsum
  simpa only [torusTuple_eq_sum] using hab

/-- One common disk works for every q and every distinct q-tuple in that disk,
uniformly for all sufficiently small positive τ. -/
theorem exists_eventual_injective_torusTuple (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi / 2 ∧
      ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ ∧ τ < 1 ∧
        ∀ (hτ : 0 < τ) (q : ℕ) (ξ : Fin q → ℂ),
          Function.Injective ξ → (∀ j, ‖ξ j‖ < R) →
          Function.Injective (torusTuple τ hτ (1 / 2) xi ξ) := by
  have hgap : ∀ i, 0 < (1 / 2 : ℝ) - xi i ∧ (1 / 2 : ℝ) - xi i < 1 := by
    intro i
    have h := hxi_bounds i
    constructor <;> linarith
  obtain ⟨R, hR, hRpi, hδ, hexp, heventual⟩ := exists_eventual_common_chart (1 / 2) xi hgap
  refine ⟨R, hR, hRpi, ?_⟩
  filter_upwards [heventual] with τ hτ
  refine ⟨hτ.1, hτ.2.1, ?_⟩
  intro hpos q ξ hξ hξR
  exact torusTuple_injective hpos hτ.2.1 xi hxi hxi_bounds hR hRpi
    hτ.2.2.1 hτ.2.2.2.1 ξ hξ hξR

end Nagata.W06.TorusConfiguration

end
end

section

/-!
# Actual ordered projective configurations from the marked torus tuple
-/
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W21 Nagata.ProjectiveGeometry
open Filter Metric
open scoped Topology

/-- Composition with a supplied genuine injective projective map. -/
def embeddedConfiguration {τ : ℝ} (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (embed : TorusPoint (positivePeriod τ hτ) → PlanePoint)
    (hembed : Function.Injective embed) : OrderedDistinctPoints (9 + q) :=
  ⟨embed ∘ torusTuple τ hτ x0 xi ξ, hembed.comp hinj⟩

@[simp] theorem embeddedConfiguration_apply {τ : ℝ} (hτ : 0 < τ)
    (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (embed : TorusPoint (positivePeriod τ hτ) → PlanePoint)
    (hembed : Function.Injective embed) (t : Fin (9 + q)) :
    (embeddedConfiguration hτ x0 xi ξ hinj embed hembed).val t =
      embed (torusTuple τ hτ x0 xi ξ t) := rfl

/-- Reindexing preserves the actual points and changes only the tuple's index type. -/
def reindexConfiguration {r s : ℕ} (hrs : r = s) (p : OrderedDistinctPoints s) :
    OrderedDistinctPoints r :=
  ⟨fun i => p.val (Fin.cast hrs i), p.property.comp (Fin.cast_injective hrs)⟩

@[simp] theorem reindexConfiguration_apply {r s : ℕ} (hrs : r = s)
    (p : OrderedDistinctPoints s) (i : Fin r) :
    (reindexConfiguration hrs p).val i = p.val (Fin.cast hrs i) := rfl

/-- The source equality r=9+q is retained exactly, with no unused or repeated points. -/
def embeddedConfigurationOfEq {r q : ℕ} (hr : r = 9 + q)
    {τ : ℝ} (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ) (ξ : Fin q → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (embed : TorusPoint (positivePeriod τ hτ) → PlanePoint)
    (hembed : Function.Injective embed) : OrderedDistinctPoints r :=
  reindexConfiguration hr (embeddedConfiguration hτ x0 xi ξ hinj embed hembed)

/-- For every r≥9 the literal choice q=r−9 gives an actual r-tuple. -/
def embeddedConfigurationForR (r : ℕ) (hr : 9 ≤ r)
    {τ : ℝ} (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ) (ξ : Fin (r - 9) → ℂ)
    (hinj : Function.Injective (torusTuple τ hτ x0 xi ξ))
    (embed : TorusPoint (positivePeriod τ hτ) → PlanePoint)
    (hembed : Function.Injective embed) : OrderedDistinctPoints r :=
  embeddedConfigurationOfEq (by omega) hτ x0 xi ξ hinj embed hembed

/-- Explicit colliding q-tuples remain distinct from each other and all nine fixed
marks at every sequence index, under the same source common-chart bounds. -/
theorem collisionTorusTuple_injective {τ R : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2)
    (hR : 0 < R) (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|)
    (hmargin : R < markedGap (1 / 2) xi * |Real.log τ|) (q n : ℕ) :
    Function.Injective (torusTuple τ hτ (1 / 2) xi (Nagata.W20.collisionCenters q R n)) := by
  apply torusTuple_injective hτ hτ1 xi hxi hxi_bounds hR hRpi hlog hmargin
    (Nagata.W20.collisionCenters q R n) (Nagata.W20.collisionCenters_injective q hR n)
  intro j
  simpa only [Metric.mem_ball, dist_zero_right] using
    Nagata.W20.collisionCenters_mem_ball q hR n j

/-- One disk and one explicit collision family work uniformly for all q and all
sufficiently small periods; every center tends to zero in the genuine complex chart. -/
theorem exists_eventual_collisionConfiguration (xi : Fin 9 → ℝ)
    (hxi : Function.Injective xi) (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi / 2 ∧
      (∀ q i, Tendsto (fun n => Nagata.W20.collisionCenters q R n i) atTop (𝓝 0)) ∧
      ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ ∧ τ < 1 ∧
        ∀ (hτ : 0 < τ) (q n : ℕ), Function.Injective
          (torusTuple τ hτ (1 / 2) xi (Nagata.W20.collisionCenters q R n)) := by
  obtain ⟨R, hR, hRpi, heventual⟩ := exists_eventual_injective_torusTuple xi hxi hxi_bounds
  refine ⟨R, hR, hRpi, fun q i => Nagata.W20.collisionCenters_tendsto q R i, ?_⟩
  filter_upwards [heventual] with τ ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro hτ q n
  apply ht.2.2 hτ q (Nagata.W20.collisionCenters q R n)
    (Nagata.W20.collisionCenters_injective q hR n)
  intro i
  simpa only [Metric.mem_ball, dist_zero_right] using
    Nagata.W20.collisionCenters_mem_ball q hR n i

end Nagata.W06.TorusConfiguration

end
end

section

/-!
# Arbitrarily many additional smooth points on component zero

This closes the finite-configuration extension needed to apply the triangle
construction for every r≥10, not just r=10. The extra points have U=−(k+2+t).
-/
noncomputable section
namespace Nagata.W06.LineArrangement

/-- A countably infinite explicit sequence of extra points on component zero. -/
def extraPoint (K : Type*) [Field K] (k t : ℕ) : K × K :=
  (-((k + 2 + t : ℕ) : K), 0)

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem extraPoint_zero (k : ℕ) : extraPoint K k 0 = additionalPoint K k := by
  simp [extraPoint, additionalPoint]

theorem extraPoint_injective (k : ℕ) : Function.Injective (extraPoint K k) := by
  intro t u h
  have hn : k + 2 + t = k + 2 + u := Nat.cast_injective (neg_injective (congrArg Prod.fst h))
  exact Nat.add_left_cancel hn

theorem extraPoint_ne_mark (k t : ℕ) (i s : Fin k) :
    extraPoint K k t ≠ markedPoint K k i s := by
  intro h
  have hn : k + 2 + t = markedCoordinate k i.val s :=
    Nat.cast_injective (neg_injective (congrArg Prod.fst h))
  have hb := markedCoordinate_le_succ k i.val s
  omega

theorem extraPoint_not_mem_markedPoints (k t : ℕ) :
    extraPoint K k t ∉ markedPoints K k := by
  classical
  intro h
  obtain ⟨⟨i, s⟩, _, hp⟩ := Finset.mem_image.mp h
  exact extraPoint_ne_mark k t i s hp.symm

omit [CharZero K] in
theorem extraPoint_on_zero (k t : ℕ) :
    lineValue 0 (extraPoint K k t).1 (extraPoint K k t).2 = 0 := by
  simp [extraPoint, lineValue, graphValue]

/-- Every extra point has a concrete nonzero Y-partial derivative. -/
theorem extraPoint_nonsingular_certificate (k : ℕ) (hk : 0 < k) (t : ℕ) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k)
        (extraPoint K k t).1 (extraPoint K k t).2 = 0 ∧
      planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
        (extraPoint K k t).1 (extraPoint K k t).2 ≠ 0 := by
  constructor
  · rw [planeEval_lineUnion]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hk⟩ : Fin k)) (extraPoint_on_zero k t)
  · simpa [extraPoint, graphValue] using
      partialY_lineUnion_negative_mark (K := K) k ⟨0, hk⟩ (k + 2 + t) (by omega)

/-- The finite set of k² original marks and n distinct extra points. -/
def manyMarkedPoints (K : Type*) [Field K] (k n : ℕ) : Finset (K × K) := by
  classical
  exact markedPoints K k ∪ (Finset.range n).image (extraPoint K k)

theorem card_manyMarkedPoints (k n : ℕ) :
    (manyMarkedPoints K k n).card = k ^ 2 + n := by
  classical
  have hd : Disjoint (markedPoints K k) ((Finset.range n).image (extraPoint K k)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    exact extraPoint_not_mem_markedPoints k t hp
  unfold manyMarkedPoints
  rw [Finset.card_union_of_disjoint hd, card_markedPoints,
    Finset.card_image_of_injective _ (extraPoint_injective k), Finset.card_range]

omit [CharZero K] in
theorem markedPoint_mem_manyMarkedPoints (k n : ℕ) (i s : Fin k) :
    markedPoint K k i s ∈ manyMarkedPoints K k n := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨(i, s), Finset.mem_univ _, rfl⟩

omit [CharZero K] in
theorem extraPoint_mem_manyMarkedPoints (k n t : ℕ) (ht : t < n) :
    extraPoint K k t ∈ manyMarkedPoints K k n := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩

theorem manyMarkedPoints_nonsingular (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ∀ p ∈ manyMarkedPoints K k n,
      planeEval (Nagata.Workers.W24.lineUnionEquation K k) p.1 p.2 = 0 ∧
      planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative p.1 p.2 ≠ 0 := by
  classical
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (line_arrangement_marked_configuration k).2 p hp
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact extraPoint_nonsingular_certificate k hk t

/-- Every target scalar of the vertical differential is attainable at every selected point. -/
theorem exists_vertical_displacement_many (k : ℕ) (hk : 0 < k) (n : ℕ)
    (p : K × K) (hp : p ∈ manyMarkedPoints K k n) (c : K) :
    ∃ t : K, planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative p.1 p.2 * t = c := by
  have h := (manyMarkedPoints_nonsingular k hk n p hp).2
  exact ⟨c / planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative p.1 p.2,
    mul_div_cancel₀ c h⟩

/-- Exactly r certified nonsingular affine points for every r≥9 on the triangle. -/
theorem triangle_configuration_every_r (r : ℕ) (hr : 9 ≤ r) :
    (manyMarkedPoints K 3 (r - 9)).card = r ∧
      ∀ p ∈ manyMarkedPoints K 3 (r - 9),
        planeEval (Nagata.Workers.W24.lineUnionEquation K 3) p.1 p.2 = 0 ∧
        planeEval (Nagata.Workers.W24.lineUnionEquation K 3).derivative p.1 p.2 ≠ 0 := by
  refine ⟨?_, manyMarkedPoints_nonsingular 3 (by norm_num) (r - 9)⟩
  rw [card_manyMarkedPoints]
  norm_num
  omega

omit [CharZero K] in
/-- For every r≥10, the point (-5,0) is present alongside the original nine marks. -/
theorem triangle_additionalPoint_mem (r : ℕ) (hr : 10 ≤ r) :
    additionalPoint K 3 ∈ manyMarkedPoints K 3 (r - 9) := by
  rw [← extraPoint_zero]
  exact extraPoint_mem_manyMarkedPoints 3 (r - 9) 0 (by omega)

/-- A direct index type for the ordered original and additional points. -/
def mixedPoint (K : Type*) [Field K] (k n : ℕ) : (Fin k × Fin k) ⊕ Fin n → K × K :=
  Sum.elim (fun p => markedPoint K k p.1 p.2) (fun t => extraPoint K k t.val)

theorem mixedPoint_injective (k n : ℕ) : Function.Injective (mixedPoint K k n) := by
  intro x y h
  cases x with
  | inl p =>
    cases y with
    | inl q => exact congrArg Sum.inl (markedPoint_injective k h)
    | inr t => exact False.elim (extraPoint_ne_mark k t.val p.1 p.2 h.symm)
  | inr t =>
    cases y with
    | inl p => exact False.elim (extraPoint_ne_mark k t.val p.1 p.2 h)
    | inr u => exact congrArg Sum.inr (Fin.ext (extraPoint_injective k h))

end Nagata.W06.LineArrangement

end
end

section

/-!
# The actual ordered projective configurations underlying the line marks
-/
noncomputable section
namespace Nagata.W06.LineArrangement
open Nagata.ProjectiveGeometry

/-- The two affine coordinates of a point, enumerated by Fin 2. -/
def pairCoordinates (p : ℂ × ℂ) : Fin 2 → ℂ := ![p.1, p.2]

theorem pairCoordinates_injective : Function.Injective pairCoordinates := by
  intro p q h
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 1

/-- The genuine projective point [U:Y:1]. -/
def liftAffine (p : ℂ × ℂ) : PlanePoint := chartPoint₂ 2 (pairCoordinates p)

theorem liftAffine_injective : Function.Injective liftAffine :=
  (chartPoint₂_injective 2).comp pairCoordinates_injective

/-- Explicit verification of the homogeneous-coordinate convention. -/
theorem liftAffine_vector (p : ℂ × ℂ) :
    chartVector₂ 2 (pairCoordinates p) = ![p.1, p.2, 1] := by
  funext i
  fin_cases i <;> simp [chartVector₂, pairCoordinates, Fin.insertNth, Fin.succAboveCases]

theorem liftAffine_chartCoordinates (p : ℂ × ℂ) :
    chartCoordinates₂ 2 (liftAffine p) = pairCoordinates p :=
  chartCoordinates₂_chartPoint₂ 2 (pairCoordinates p)

/-- Explicit enumeration of the k² original marks followed by n extra marks. -/
def configurationIndexEquiv (k n : ℕ) :
    ((Fin k × Fin k) ⊕ Fin n) ≃ Fin (k * k + n) :=
  ((finProdFinEquiv : Fin k × Fin k ≃ Fin (k * k)).sumCongr (Equiv.refl (Fin n))).trans
    (finSumFinEquiv : Fin (k * k) ⊕ Fin n ≃ Fin (k * k + n))

def orderedAffinePoint (k n : ℕ) (t : Fin (k * k + n)) : ℂ × ℂ :=
  mixedPoint ℂ k n ((configurationIndexEquiv k n).symm t)

theorem orderedAffinePoint_injective (k n : ℕ) : Function.Injective (orderedAffinePoint k n) :=
  (mixedPoint_injective k n).comp (configurationIndexEquiv k n).symm.injective

/-- An actual element of U_(k²+n), with all projective points explicitly constructed. -/
def orderedProjectiveConfiguration (k n : ℕ) : OrderedDistinctPoints (k * k + n) :=
  ⟨fun t => liftAffine (orderedAffinePoint k n t),
    liftAffine_injective.comp (orderedAffinePoint_injective k n)⟩

/-- Every ordered point retains the verified affine equation and derivative certificate. -/
theorem orderedAffinePoint_nonsingular (k : ℕ) (hk : 0 < k) (n : ℕ)
    (t : Fin (k * k + n)) :
    planeEval (Nagata.Workers.W24.lineUnionEquation ℂ k)
        (orderedAffinePoint k n t).1 (orderedAffinePoint k n t).2 = 0 ∧
      planeEval (Nagata.Workers.W24.lineUnionEquation ℂ k).derivative
        (orderedAffinePoint k n t).1 (orderedAffinePoint k n t).2 ≠ 0 := by
  unfold orderedAffinePoint
  cases h : (configurationIndexEquiv k n).symm t with
  | inl p => exact markedPoint_nonsingular_certificate k p.1 p.2
  | inr s => exact extraPoint_nonsingular_certificate k hk s.val

/-- Every r≥9 has the concrete r-point triangle configuration in the genuine U_r. -/
def triangleOrderedConfiguration (r : ℕ) (hr : 9 ≤ r) : OrderedDistinctPoints r := by
  have h : 3 * 3 + (r - 9) = r := by omega
  exact h ▸ orderedProjectiveConfiguration 3 (r - 9)

end Nagata.W06.LineArrangement

end
end

end OAI
