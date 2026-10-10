import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibility
import OAI.Geometry.IsometricImmersion.Metrics.FixedMetricRemainder
import OAI.Geometry.IsometricImmersion.Assembly.SupportedPerturbations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

def BoundedAdmissibleHeight (g : MetricField) (M : ℕ) (z : Coord → ℝ) : Prop :=
  0 < M ∧ PatchAdmissibleHeight g z ∧
  (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ (M : ℝ)) ∧
  (∀ p ∈ modelSquare, 1 / (M : ℝ) ≤ |covHessian g z p 1 1| ∧
    |covHessian g z p 1 1| ≤ (M : ℝ)) ∧
  (∀ p ∈ modelSquare, 1 / (M : ℝ) ≤ heightEnergy g z p)

theorem PatchAdmissibleHeight.exists_integer_bound {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) : ∃ M : ℕ, BoundedAdmissibleHeight g M z := by
  have horiginal := h
  obtain ⟨U, hU, hSU, hg, hz, _, hE, hyy, _⟩ := h
  obtain ⟨Z, _, hzB⟩ := compact_finite_fullJet_bound hz hU modelSquare_isCompact hSU 8
  have hHcont : ContinuousOn (fun p => covHessian g z p 1 1) modelSquare :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.mono hSU
  obtain ⟨H, hH⟩ := modelSquare_isCompact.exists_bound_of_continuousOn hHcont
  obtain ⟨c, hc, hcfloor⟩ := modelSquare_isCompact.exists_forall_le'
    hHcont.abs (fun p hp => abs_pos.mpr (hyy p hp))
  obtain ⟨e, he, hefloor⟩ := modelSquare_isCompact.exists_forall_le'
    ((heightEnergy_contDiffOn hg hU hz).continuousOn.mono hSU) hE
  let B := max 1 (max Z (max H (max (1 / c) (1 / e))))
  obtain ⟨M, hM⟩ := exists_nat_ge B
  have hMone : (1 : ℝ) ≤ (M : ℝ) := (le_max_left _ _).trans hM
  have hMposR : (0 : ℝ) < (M : ℝ) := zero_lt_one.trans_le hMone
  have hMpos : 0 < M := Nat.cast_pos.mp hMposR
  have hZM : Z ≤ (M : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hM
  have hHM : H ≤ (M : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hM
  have hcM : 1 / c ≤ (M : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans hM
  have heM : 1 / e ≤ (M : ℝ) :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans hM
  have hMc : 1 / (M : ℝ) ≤ c := (one_div_le hMposR hc).mpr hcM
  have hMe : 1 / (M : ℝ) ≤ e := (one_div_le hMposR he).mpr heM
  refine ⟨M, hMpos, horiginal, ?_, ?_, ?_⟩
  · intro k hk p hp
    exact (hzB k hk p hp).trans hZM
  · intro p hp
    refine ⟨hMc.trans (hcfloor p hp), ?_⟩
    have hh : |covHessian g z p 1 1| ≤ H := by
      simpa only [Real.norm_eq_abs] using hH p hp
    exact hh.trans hHM
  · intro p hp
    exact hMe.trans (hefloor p hp)

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def boundedClassSpeed (kappa : ℝ) (M : ℕ) : ℝ :=
  Real.sqrt (kappa / 2) * (M : ℝ) ^ (-(3 : ℝ) / 2)

def boundedClassWidth (kappa : ℝ) (M : ℕ) : ℝ :=
  100 * (1 + (boundedClassSpeed kappa M)⁻¹)

theorem boundedClassSpeed_pos {kappa : ℝ} (hkappa : 0 < kappa) {M : ℕ} (hM : 0 < M) :
    0 < boundedClassSpeed kappa M :=
  mul_pos (Real.sqrt_pos.mpr (div_pos hkappa (by norm_num)))
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hM) _)

theorem boundedClassWidth_ge_hundred (kappa : ℝ) (M : ℕ) :
    100 ≤ boundedClassWidth kappa M := by
  have hv : 0 ≤ boundedClassSpeed kappa M :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hi := inv_nonneg.mpr hv
  dsimp only [boundedClassWidth]
  linarith

theorem boundedClassWidth_pos (kappa : ℝ) (M : ℕ) :
    0 < boundedClassWidth kappa M :=
  (by norm_num : (0 : ℝ) < 100).trans_le (boundedClassWidth_ge_hundred kappa M)

theorem exists_rational_bounded_class_label (kappa : ℝ) (M : ℕ) (q : ℝ) :
    ∃ q0 : ℚ, |q - (q0 : ℝ)| < 1 / (100 * boundedClassWidth kappa M) := by
  let epsilon := 1 / (100 * boundedClassWidth kappa M)
  have hepsilon : 0 < epsilon := one_div_pos.mpr
    (mul_pos (by norm_num) (boundedClassWidth_pos kappa M))
  obtain ⟨q0, hlower, hupper⟩ := exists_rat_btwn
    (show q - epsilon < q + epsilon by linarith)
  refine ⟨q0, abs_lt.mpr ⟨?_, ?_⟩⟩ <;> linarith

def admissiblePatchMetricSet (g0 : MetricField) (kappa : ℝ) : Set (metricPatchSet g0 kappa) :=
  {eta | ∃ z : Coord → ℝ, PatchAdmissibleHeight (perturbedMetric g0 eta.val) z}

def boundedHeightClass (g0 : MetricField) (kappa : ℝ) (M : ℕ) (q0 : ℚ) :
    Set (metricPatchSet g0 kappa) :=
  {eta | ∃ z : Coord → ℝ, BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
    |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
      1 / (100 * boundedClassWidth kappa M)}

theorem boundedHeightClass_subset_admissible (g0 : MetricField) (kappa : ℝ) (M : ℕ) (q0 : ℚ) :
    boundedHeightClass g0 kappa M q0 ⊆ admissiblePatchMetricSet g0 kappa := by
  intro eta heta
  obtain ⟨z, hz, _⟩ := heta
  exact ⟨z, hz.2.1⟩

theorem every_admissible_height_has_class {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) (kappa : ℝ) :
    ∃ M : ℕ, BoundedAdmissibleHeight g M z ∧
      ∃ q0 : ℚ, |hessianQuotient g z 0 - (q0 : ℝ)| <
        1 / (100 * boundedClassWidth kappa M) := by
  obtain ⟨M, hM⟩ := h.exists_integer_bound
  obtain ⟨q0, hq0⟩ := exists_rational_bounded_class_label kappa M (hessianQuotient g z 0)
  exact ⟨M, hM, q0, hq0⟩

theorem admissiblePatchMetricSet_eq_iUnion (g0 : MetricField) (kappa : ℝ) :
    admissiblePatchMetricSet g0 kappa =
      ⋃ M : ℕ, ⋃ q0 : ℚ, boundedHeightClass g0 kappa M q0 := by
  ext eta
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨M, hM, q0, hq0⟩ := every_admissible_height_has_class hz kappa
    exact mem_iUnion.mpr ⟨M, mem_iUnion.mpr ⟨q0, z, hM, hq0⟩⟩
  · intro heta
    obtain ⟨M, heta⟩ := mem_iUnion.mp heta
    obtain ⟨q0, heta⟩ := mem_iUnion.mp heta
    exact boundedHeightClass_subset_admissible g0 kappa M q0 heta

theorem boundedHeightClass_family_countable (g0 : MetricField) (kappa : ℝ) :
    (Set.range (fun index : ℕ × ℚ => boundedHeightClass g0 kappa index.1 index.2)).Countable :=
  Set.countable_range _

theorem boundedHeightClass_label_abs_lt {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    (hne : (boundedHeightClass g0 kappa M q0).Nonempty) : |(q0 : ℝ)| < 1 / 20 := by
  obtain ⟨eta, z, hz, hlabel⟩ := hne
  obtain ⟨_, _, _, _, _, _, _, _, hq⟩ := hz.2.1
  have hzero : (0 : Coord) ∈ SmoothLocal.Flow.modelSquare := by
    constructor <;> intro _ <;> norm_num
  have hqzero := hq 0 hzero
  have hL := boundedClassWidth_ge_hundred kappa M
  have hden : (100 : ℝ) < 100 * boundedClassWidth kappa M := by linarith
  have htolerance : 1 / (100 * boundedClassWidth kappa M) < (1 : ℝ) / 100 :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  have htriangle : |(q0 : ℝ)| ≤
      |(q0 : ℝ) - hessianQuotient (perturbedMetric g0 eta.val) z 0| +
        |hessianQuotient (perturbedMetric g0 eta.val) z 0| := by
    simpa only [sub_add_cancel] using
      abs_add_le ((q0 : ℝ) - hessianQuotient (perturbedMetric g0 eta.val) z 0)
        (hessianQuotient (perturbedMetric g0 eta.val) z 0)
  rw [abs_sub_comm] at htriangle
  linarith

end SmoothLocal.Perturbation

end

end OAI
