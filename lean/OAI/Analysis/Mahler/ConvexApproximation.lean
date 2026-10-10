import OAI.Analysis.Mahler.ActualFiniteStrips
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

namespace OAI

/-! Finite-strip approximation with coordinate definitions of the convex body and its polar. -/
namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [Fintype I] [Fintype J]

lemma continuous_pairing (x : I → ℝ) : Continuous (fun p : I → ℝ => ∑ i, p i * x i) := by
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)

lemma coordinatePolar_antitone {K L : Set (I → ℝ)} (h : K ⊆ L) :
    coordinatePolar L ⊆ coordinatePolar K := fun _ hp x hx => hp x (h hx)

lemma zero_mem_coordinatePolar (K : Set (I → ℝ)) : (0 : I → ℝ) ∈ coordinatePolar K := by
  intro x hx
  simp

lemma isClosed_coordinatePolar (K : Set (I → ℝ)) : IsClosed (coordinatePolar K) := by
  have heq : coordinatePolar K = ⋂ x ∈ K, {p | (∑ i, p i*x i) ≤ 1} := by
    ext p
    simp [coordinatePolar]
  rw [heq]
  exact isClosed_biInter (fun x hx => isClosed_le (continuous_pairing x) continuous_const)

lemma pairing_of_dual [DecidableEq I] (f : (I → ℝ) →L[ℝ] ℝ) (x : I → ℝ) :
    (∑ i, f (Pi.single i 1) * x i) = f x := by
  have hx : (∑ i, x i • Pi.single i (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hx, map_sum]
  apply sum_congr rfl
  intro i hi
  rw [map_smul]
  simp only [smul_eq_mul]
  rw [mul_comm]

/-- Strict separation normalized by a positive separator level. The origin
membership makes that level positive, without assuming a supporting maximum. -/
theorem exists_coordinatePolar_separator [DecidableEq I] {K : Set (I → ℝ)}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hzero : (0 : I → ℝ) ∈ K)
    {x : I → ℝ} (hx : x ∉ K) :
    ∃ p ∈ coordinatePolar K, 1 < ∑ i, p i * x i := by
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconv hclosed hx
  have hu0 : 0 < u := by simpa using hu 0 hzero
  refine ⟨fun i => f (Pi.single i 1) / u, ?_, ?_⟩
  · intro v hv
    simp only [div_mul_eq_mul_div, ← sum_div, pairing_of_dual]
    exact (div_le_one hu0).mpr (hu v hv).le
  · simp only [div_mul_eq_mul_div, ← sum_div, pairing_of_dual]
    exact (one_lt_div hu0).mpr hux

lemma polar_pairing_abs {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K)
    {p : I → ℝ} (hp : p ∈ coordinatePolar K) {x : I → ℝ} (hx : x ∈ K) :
    |∑ i, p i * x i| ≤ 1 := by
  refine abs_le.mpr ⟨?_, hp x hx⟩
  have h := hp (-x) (hsym x hx)
  simp only [Pi.neg_apply, mul_neg, sum_neg_distrib] at h
  linarith

/-- Dense polar constraints recover the original closed convex set. -/
theorem dense_polar_strips_intersection [DecidableEq I] {K : Set (I → ℝ)}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hzero : (0 : I → ℝ) ∈ K)
    (hsym : ∀ x ∈ K, -x ∈ K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    {x : I → ℝ | ∀ j, |∑ i, (a j).val i * x i| ≤ 1} = K := by
  ext x
  constructor
  · intro hx
    by_contra hxK
    obtain ⟨p, hp, hpx⟩ := exists_coordinatePolar_separator hconv hclosed hzero hxK
    let C : Set (coordinatePolar K) := {q | (∑ i, q.val i * x i) ≤ 1}
    have hC : IsClosed C :=
      isClosed_le ((continuous_pairing x).comp continuous_subtype_val) continuous_const
    have hr : Set.range a ⊆ C := by
      rintro _ ⟨j, rfl⟩
      exact (le_abs_self _).trans (hx j)
    have hpC : (⟨p, hp⟩ : coordinatePolar K) ∈ C := by
      rw [← hC.closure_eq]
      exact closure_mono hr (ha ⟨p, hp⟩)
    exact (not_le_of_gt hpx) hpC
  · intro hx j
    exact polar_pairing_abs hsym (a j).property hx

end SymmetricMahler

end OAI
