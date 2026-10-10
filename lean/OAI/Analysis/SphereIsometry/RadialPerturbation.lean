import OAI.Analysis.SphereIsometry.Supports
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Small radial perturbations from strict support signs

Compactness is used only on the continuous dual of the span of two vectors.
The public result has no finite-dimensional or completeness hypothesis on the
ambient real normed space.
-/

noncomputable section

namespace Tingley

private theorem exists_dual_gap_of_supportAt_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {v y : V}
    (hv : ‖v‖ = 1)
    (hneg : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ φ : V →L[ℝ] ℝ, ‖φ‖ ≤ 1 → 0 ≤ φ y → φ v ≤ c := by
  classical
  let K : Set (V →L[ℝ] ℝ) :=
    Metric.closedBall 0 1 ∩ {φ | 0 ≤ φ y}
  have heval (z : V) : Continuous (fun φ : V →L[ℝ] ℝ => φ z) :=
    continuous_id.clm_apply continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : V →L[ℝ] ℝ) 1).inter_right
      (isClosed_le continuous_const (heval y))
  have hzero : (0 : V →L[ℝ] ℝ) ∈ K := by simp [K]
  obtain ⟨φ₀, hφ₀, hmax⟩ := hK.exists_isMaxOn ⟨0, hzero⟩ (heval v).continuousOn
  have hφnorm : ‖φ₀‖ ≤ 1 := by
    simpa only [mem_closedBall_zero_iff] using hφ₀.1
  have hc_le : φ₀ v ≤ 1 := by
    simpa only [hv] using apply_le_norm hφnorm v
  have hc_lt : φ₀ v < 1 := by
    by_contra hnot
    have heq : φ₀ v = 1 := le_antisymm hc_le (le_of_not_gt hnot)
    have hs : SupportAt φ₀ v := ⟨hφnorm, heq.trans hv.symm⟩
    exact (not_lt_of_ge hφ₀.2) (hneg φ₀ hs)
  refine ⟨φ₀ v, ?_, hc_lt, ?_⟩
  · simpa using (isMaxOn_iff.mp hmax) 0 hzero
  · intro φ hφ hy
    apply (isMaxOn_iff.mp hmax) φ
    exact ⟨mem_closedBall_zero_iff.mpr hφ, hy⟩

private theorem exists_radial_perturbation_lt_finiteDimensional
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {v y : V} {p : ℝ}
    (hv : ‖v‖ = 1) (hp : 0 < p)
    (hneg : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
      ‖p • v + η • y‖ < p := by
  obtain ⟨c, _hc0, hc, hgap⟩ := exists_dual_gap_of_supportAt_neg hv hneg
  have hden : 0 < ‖y‖ + 1 := by linarith [norm_nonneg y]
  refine ⟨p * (1 - c) / (‖y‖ + 1),
    div_pos (mul_pos hp (sub_pos.mpr hc)) hden, ?_⟩
  intro η hη hηδ
  obtain ⟨φ, hφ⟩ := exists_support (p • v + η • y)
  have hnorm : ‖p • v + η • y‖ = p * φ v + η * φ y := by
    calc
      ‖p • v + η • y‖ = φ (p • v + η • y) := hφ.2.symm
      _ = p * φ v + η * φ y := by simp only [map_add, map_smul, smul_eq_mul]
  rw [hnorm]
  by_cases hnegative : φ y < 0
  · have hunit : φ v ≤ 1 := by simpa only [hv] using apply_le_norm hφ.1 v
    have hfirst : p * φ v ≤ p * 1 := mul_le_mul_of_nonneg_left hunit hp.le
    have hsecond : η * φ y < 0 := mul_neg_of_pos_of_neg hη hnegative
    nlinarith only [hfirst, hsecond]
  · have hvbound : φ v ≤ c := hgap φ hφ.1 (le_of_not_gt hnegative)
    have hybound : φ y ≤ ‖y‖ := apply_le_norm hφ.1 y
    have hfirst : p * φ v ≤ p * c := mul_le_mul_of_nonneg_left hvbound hp.le
    have hsecond : η * φ y ≤ η * ‖y‖ := mul_le_mul_of_nonneg_left hybound hη.le
    have hmul : η * (‖y‖ + 1) < p * (1 - c) := (lt_div_iff₀ hden).mp hηδ
    have hstrict : p * c + η * ‖y‖ < p := by nlinarith only [hmul, hη]
    linarith only [hfirst, hsecond, hstrict]

/-- Strict negativity on the perturbing vector for every support at a unit
vector makes all sufficiently small positive radial perturbations shorter.
Only the span of the two specified vectors is made finite-dimensional. -/
theorem exists_radial_perturbation_lt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v y : X} {p : ℝ} (hv : ‖v‖ = 1) (hp : 0 < p)
    (hneg : ∀ φ : X →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
      ‖p • v + η • y‖ < p := by
  classical
  let V : Submodule ℝ X := Submodule.span ℝ ({v, y} : Set X)
  have hv_mem : v ∈ V := Submodule.subset_span (by simp)
  have hy_mem : y ∈ V := Submodule.subset_span (by simp)
  let v₀ : V := ⟨v, hv_mem⟩
  let y₀ : V := ⟨y, hy_mem⟩
  have : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_singleton y).insert v)
  have hv₀ : ‖v₀‖ = 1 := hv
  have hneg₀ : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v₀ → φ y₀ < 0 :=
    (forall_supportAt_apply_iff_submodule V v₀ y₀ (fun r : ℝ => r < 0)).mp hneg
  obtain ⟨δ, hδ, hsmall⟩ := exists_radial_perturbation_lt_finiteDimensional hv₀ hp hneg₀
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  exact hsmall η hη hηδ

/-- The perturbation may also be chosen below any prescribed positive cap. -/
theorem exists_radial_perturbation_lt_with_cap
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v y : X} {p t : ℝ} (hv : ‖v‖ = 1) (hp : 0 < p) (ht : 0 < t)
    (hneg : ∀ φ : X →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ η : ℝ, 0 < η ∧ η < t ∧ ‖p • v + η • y‖ < p := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_radial_perturbation_lt hv hp hneg
  have hm : 0 < min t δ := lt_min ht hδ
  have hη : 0 < min t δ / 2 := by linarith
  have hηt : min t δ / 2 < t := by linarith [min_le_left t δ]
  have hηδ : min t δ / 2 < δ := by linarith [min_le_right t δ]
  exact ⟨min t δ / 2, hη, hηt, hsmall _ hη hηδ⟩

end Tingley

end

end OAI
