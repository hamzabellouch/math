import OAI.Probability.InvariantIsing.Core.Variational
import OAI.Probability.InvariantIsing.Spectral.SpectralEndpoints

namespace OAI

/-! The reconstructed finite-alphabet overlap paths in manuscript `rot:full-paths`.
The formulas and their positivity and sum constraints are proved here;
identification with limiting Gibbs overlaps is separate. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def spectralPathDensity (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (r : ℝ) : ℝ :=
  projectedResolventDerivative ρ eig hρ hρsum a (deficit p r)

def spectralGroupPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (s : ℝ) : ℝ :=
  ∫ r in 0..p s, spectralPathDensity ρ eig hρ hρsum p a r

def spectralGroupDiagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) : ℝ :=
  ∫ r in 0..1, spectralPathDensity ρ eig hρ hρsum p a r

theorem spectralPathDensity_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (r : ℝ) :
    0 ≤ spectralPathDensity ρ eig hρ hρsum p a r :=
  (projectedResolventDerivative_pos ρ eig hρ hρsum a (deficit p r)).le

theorem spectralPathDensity_continuousOn (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    ContinuousOn (spectralPathDensity ρ eig hρ hρsum p a) (Icc 0 1) :=
  (continuousOn_projectedResolventDerivative ρ eig hρ hρsum a).comp
    (continuous_deficit p).continuousOn (fun _r hr => deficit_mem_unit p hr)

theorem spectralPathDensity_intervalIntegrable (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (spectralPathDensity ρ eig hρ hρsum p a) volume 0 q :=
  ((spectralPathDensity_continuousOn ρ eig hρ hρsum p a).mono
    (Icc_subset_Icc le_rfl hq.2)).intervalIntegrable_of_Icc hq.1

theorem spectralGroupPath_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (s : ℝ) :
    0 ≤ spectralGroupPath ρ eig hρ hρsum p a s :=
  intervalIntegral.integral_nonneg_of_forall (p.nonneg s)
    (spectralPathDensity_nonneg ρ eig hρ hρsum p a)

theorem spectralGroupDiagonal_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    0 ≤ spectralGroupDiagonal ρ eig hρ hρsum p a :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one
    (spectralPathDensity_nonneg ρ eig hρ hρsum p a)

theorem spectralGroupPath_monotone (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Monotone (spectralGroupPath ρ eig hρ hρsum p a) := by
  intro s t hst
  exact intervalIntegral.integral_mono_interval le_rfl (p.nonneg s) (p.monotone hst)
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨p.nonneg t, p.le_one t⟩)

theorem sum_spectralGroupPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (s : ℝ) :
    (∑ a, spectralGroupPath ρ eig hρ hρsum p a s) = p s := by
  unfold spectralGroupPath
  rw [← intervalIntegral.integral_finsetSum
    (fun a _ => spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a
      ⟨p.nonneg s, p.le_one s⟩)]
  simp only [spectralPathDensity, sum_projectedResolventDerivative,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

theorem sum_spectralGroupDiagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    (∑ a, spectralGroupDiagonal ρ eig hρ hρsum p a) = 1 := by
  unfold spectralGroupDiagonal
  rw [← intervalIntegral.integral_finsetSum
    (fun a _ => spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a
      ⟨zero_le_one, le_rfl⟩)]
  simp only [spectralPathDensity, sum_projectedResolventDerivative,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

theorem spectralGroupPath_le_diagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (s : ℝ) :
    spectralGroupPath ρ eig hρ hρsum p a s ≤ spectralGroupDiagonal ρ eig hρ hρsum p a :=
  intervalIntegral.integral_mono_interval le_rfl (p.nonneg s) (p.le_one s)
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨zero_le_one, le_rfl⟩)

theorem spectralGroup_diagonalExcess_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (top : ℝ) :
    0 ≤ spectralGroupDiagonal ρ eig hρ hρsum p a - spectralGroupPath ρ eig hρ hρsum p a top :=
  sub_nonneg.mpr (spectralGroupPath_le_diagonal ρ eig hρ hρsum p a top)

theorem spectralGroup_diagonalExcess_eq_integral (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (top : ℝ) :
    spectralGroupDiagonal ρ eig hρ hρsum p a - spectralGroupPath ρ eig hρ hρsum p a top =
      ∫ r in p top..1, spectralPathDensity ρ eig hρ hρsum p a r := by
  have h0 := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a
    ⟨p.nonneg top, p.le_one top⟩
  have h1 : IntervalIntegrable (spectralPathDensity ρ eig hρ hρsum p a) volume (p top) 1 :=
    ((spectralPathDensity_continuousOn ρ eig hρ hρsum p a).mono
      (Icc_subset_Icc (p.nonneg top) le_rfl)).intervalIntegrable_of_Icc (p.le_one top)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0 h1
  unfold spectralGroupDiagonal spectralGroupPath
  linarith

theorem spectralGroup_diagonalExcess_zero_of_top_one
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) {top : ℝ} (htop : p top = 1) :
    spectralGroupDiagonal ρ eig hρ hρsum p a - spectralGroupPath ρ eig hρ hρsum p a top = 0 := by
  rw [spectralGroup_diagonalExcess_eq_integral, htop, intervalIntegral.integral_same]

theorem spectralGroupDiagonal_le_one (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    spectralGroupDiagonal ρ eig hρ hρsum p a ≤ 1 := by
  rw [← sum_spectralGroupDiagonal ρ eig hρ hρsum p]
  exact Finset.single_le_sum (fun b _ => spectralGroupDiagonal_nonneg ρ eig hρ hρsum p b)
    (Finset.mem_univ a)

theorem spectralGroupPath_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (c : ℝ) (p : OverlapPath) (a : ι) (s : ℝ) :
    spectralGroupPath ρ (fun _ => c) hρ hρsum p a s = ρ a * p s := by
  simp only [spectralGroupPath, spectralPathDensity, projectedResolventDerivative_constant,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

theorem spectralGroupDiagonal_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (c : ℝ) (p : OverlapPath) (a : ι) :
    spectralGroupDiagonal ρ (fun _ => c) hρ hρsum p a = ρ a := by
  simp only [spectralGroupDiagonal, spectralPathDensity, projectedResolventDerivative_constant,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]

end InvariantIsing

end

end OAI
