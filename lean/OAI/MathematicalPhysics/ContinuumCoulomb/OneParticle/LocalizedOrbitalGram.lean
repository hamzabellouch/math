import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedTransition
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombGramApprox
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

namespace OAI

/-! The actual localized L2 orbitals form a well-conditioned independent
family whenever the exponentially small pair overlaps have a small row sum.
In particular their finite span has an actual orthonormal basis. -/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_upper {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, A i i ≤ a)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (∑ i, ∑ j, A i j * d i * d j) ≤ (a + m * delta) * ∑ i, d i ^ 2 := by
  have h := dualMatrix_quadratic_lower (fun i j => -A i j) hdelta
    (fun i => neg_le_neg (hdiag i)) (fun i j hij => by simpa only [abs_neg] using hoff i j hij) d
  simp only [neg_mul, Finset.sum_neg_distrib] at h
  linarith

def localizedOrbitalL2 {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    Lp ℝ 2 (volume : Measure Position) :=
  (continuumLocalizedMode_memLp hfreq u).toLp (continuumLocalizedMode freq u)

theorem localizedOrbitalL2_inner {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    inner ℝ (localizedOrbitalL2 hfreq u) (localizedOrbitalL2 hfreq v) = planarModeOverlap u v := by
  rw [L2.inner_def, ← localizedTransition_mass hfreq u v]
  apply integral_congr_ae
  filter_upwards [(continuumLocalizedMode_memLp hfreq u).coeFn_toLp,
    (continuumLocalizedMode_memLp hfreq v).coeFn_toLp] with x hu hv
  change inner ℝ ((continuumLocalizedMode_memLp hfreq u).toLp (continuumLocalizedMode freq u) x)
    ((continuumLocalizedMode_memLp hfreq v).toLp (continuumLocalizedMode freq v) x) = _
  rw [hu, hv, RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem localizedOrbitalL2_norm {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    ‖localizedOrbitalL2 hfreq u‖ = 1 := by
  have h : ‖localizedOrbitalL2 hfreq u‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, localizedOrbitalL2_inner, planarModeOverlap_diagonal]
  nlinarith [norm_nonneg (localizedOrbitalL2 hfreq u)]

theorem localizedOrbitalL2_sum_norm_sq {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (d : Fin m → ℝ) :
    ‖∑ i, d i • localizedOrbitalL2 hfreq (u i)‖ ^ 2 =
      ∑ i, ∑ j, planarModeOverlap (u i) (u j) * d i * d j := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    localizedOrbitalL2_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def localizedOverlapBound (D : ℝ) : ℝ := planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * D)

theorem localizedOverlapBound_nonnegative (D : ℝ) : 0 ≤ localizedOverlapBound D :=
  mul_nonneg planarOverlapConstant_nonnegative (Real.exp_pos _).le

theorem planarModeOverlap_offsite {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i j : Fin m) (hij : i ≠ j) :
    |planarModeOverlap (u i) (u j)| ≤ localizedOverlapBound D := by
  rw [abs_of_nonneg (planarModeOverlap_nonnegative _ _)]
  exact (planarModeOverlap_decay _ _).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith [hsep i j hij])) planarOverlapConstant_nonnegative)

theorem localizedOrbitalL2_sum_bounds {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (d : Fin m → ℝ) :
    (1 - m * localizedOverlapBound D) * ∑ i, d i ^ 2 ≤
      ‖∑ i, d i • localizedOrbitalL2 hfreq (u i)‖ ^ 2 ∧
    ‖∑ i, d i • localizedOrbitalL2 hfreq (u i)‖ ^ 2 ≤
      (1 + m * localizedOverlapBound D) * ∑ i, d i ^ 2 := by
  rw [localizedOrbitalL2_sum_norm_sq]
  exact ⟨dualMatrix_quadratic_lower _ (localizedOverlapBound_nonnegative D)
      (fun i => (planarModeOverlap_diagonal (u i)).ge) (planarModeOverlap_offsite u hsep) d,
    dualMatrix_quadratic_upper _ (localizedOverlapBound_nonnegative D)
      (fun i => (planarModeOverlap_diagonal (u i)).le) (planarModeOverlap_offsite u hsep) d⟩

theorem localizedOrbitalL2_linearIndependent {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hsmall : m * localizedOverlapBound D < 1) :
    LinearIndependent ℝ (fun i => localizedOrbitalL2 hfreq (u i)) := by
  rw [Fintype.linearIndependent_iff]
  intro d hd i
  have h := (localizedOrbitalL2_sum_bounds hfreq u hsep d).1
  rw [hd, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hs : ∑ j, d j ^ 2 = 0 := by
    have hn : 0 ≤ ∑ j, d j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (d j))
    nlinarith
  have hi : d i ^ 2 ≤ ∑ j, d j ^ 2 := Finset.single_le_sum
    (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i)
  nlinarith [sq_nonneg (d i)]

def orthonormalLocalizedOrbitals {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) : Fin m → Lp ℝ 2 (volume : Measure Position) :=
  gramSchmidtNormed ℝ (fun i => localizedOrbitalL2 hfreq (u i))

theorem orthonormalLocalizedOrbitals_orthonormal {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hsmall : m * localizedOverlapBound D < 1) :
    Orthonormal ℝ (orthonormalLocalizedOrbitals hfreq u) :=
  gramSchmidtNormed_orthonormal (localizedOrbitalL2_linearIndependent hfreq u hsep hsmall)

theorem orthonormalLocalizedOrbitals_span {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    Submodule.span ℝ (Set.range (orthonormalLocalizedOrbitals hfreq u)) =
      Submodule.span ℝ (Set.range (fun i => localizedOrbitalL2 hfreq (u i))) := by
  rw [orthonormalLocalizedOrbitals, span_gramSchmidtNormed_range, span_gramSchmidt]

end ContinuumCoulomb

end

end OAI
