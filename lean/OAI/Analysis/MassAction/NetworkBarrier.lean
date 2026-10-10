import OAI.Analysis.MassAction.SignTolerance
import OAI.Analysis.MassAction.SmallParameter
import OAI.Analysis.MassAction.MonomialOrder
import OAI.Analysis.MassAction.PlateauCertificate
import OAI.Analysis.MassAction.MassActionFlux

namespace OAI

noncomputable section

open Set
open scoped BigOperators

namespace Problem326.BarrierConstruction

/-- The uniform conclusion needed from the arbitrary-tolerance affine lemma.
Slopes are fixed before `h` is
chosen, and every minimizing branch, including ties, must approximate. -/
def UniformAffineApproximation (d : ℕ) : Prop :=
  ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
    ∃ n : ℕ, 0 < n ∧ ∃ (r : Fin n → Fin d → ℝ)
      (c : Fin n → ℝ → ℝ) (h₀ : ℝ), 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
        (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
          AffineActive r (fun k => c k h) (fun i => h ^ p i) j →
          ∀ i, |p i - r j i| < E (r j)

/-- Finite barrier data, after the network, rates, and initial point have been
fixed. The remaining analytic step is trapping and global ODE continuation. -/
structure AffineBarrierData {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x₀ : Fin d → ℝ) where
  n : ℕ
  n_pos : 0 < n
  slope : Fin n → Fin d → ℝ
  offset : Fin n → ℝ
  parameter : ℝ
  parameter_pos : 0 < parameter
  parameter_lt_one : parameter < 1
  constant_branch : Fin n
  slope_constant : slope constant_branch = 0
  initial_active : AffineActive slope offset x₀ constant_branch
  initial_inside : ∀ i, parameter < x₀ i ∧ x₀ i < parameter⁻¹
  inward : ∀ p : Fin d → ℝ, (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
    AffineActive slope offset (fun i => parameter ^ p i) j →
    0 ≤ dot (slope j) (massAction N κ (fun i => parameter ^ p i))
  boundary_excluded : ∀ p : Fin d → ℝ, (∀ i, |p i| ≤ 1) →
    (∃ i, |p i| = 1) →
    ¬ AffineActive slope offset (fun i => parameter ^ p i) constant_branch

/-- Coordinate directions are included alongside all complex differences. -/
def coordinateDirection {d : ℕ} (i : Fin d) : Fin d → ℝ :=
  fun k => if k = i then 1 else 0

def complexDifference {d : ℕ} (y z : Fin d → ℕ) : Fin d → ℝ :=
  fun i => (z i : ℝ) - (y i : ℝ)

@[simp] theorem dot_coordinateDirection {d : ℕ} (p : Fin d → ℝ) (i : Fin d) :
    dot p (coordinateDirection i) = p i := by
  classical
  simp [dot, coordinateDirection, mul_ite]

@[simp] theorem dot_complexDifference {d : ℕ} (p : Fin d → ℝ)
    (y z : Fin d → ℕ) :
    dot p (complexDifference y z) =
      dot p (fun i => (z i : ℝ)) - dot p (fun i => (y i : ℝ)) := by
  simp [dot, complexDifference, mul_sub, Finset.sum_sub_distrib]

def comparisonDirections {d : ℕ} (N : ReactionNetwork d) : Finset (Fin d → ℝ) :=
  (Finset.univ.image coordinateDirection) ∪
    ((N.complexes.product N.complexes).image
      (fun yz => complexDifference yz.1 yz.2))

theorem coordinateDirection_mem {d : ℕ} (N : ReactionNetwork d) (i : Fin d) :
    coordinateDirection i ∈ comparisonDirections N := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem complexDifference_mem {d : ℕ} (N : ReactionNetwork d)
    {y z : Fin d → ℕ} (hy : y ∈ N.complexes) (hz : z ∈ N.complexes) :
    complexDifference y z ∈ comparisonDirections N := by
  classical
  unfold comparisonDirections
  rw [Finset.mem_union]
  right
  apply Finset.mem_image.mpr
  exact ⟨(y, z), Finset.mem_product.mpr ⟨hy, hz⟩, rfl⟩

/-- The full network-aware algebraic assembly. The tolerance is selected first,
then fixed slopes and their positive gap, then the single small parameter.
No compactness or ODE conclusion is assumed in this theorem. -/
theorem exists_affineBarrierData {d : ℕ}
    (happroximation : UniformAffineApproximation d)
    (N : ReactionNetwork d) (κ : Reaction N → ℝ)
    (hweak : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x₀ : Fin d → ℝ) (hx₀ : PositiveState x₀) :
    Nonempty (AffineBarrierData N κ x₀) := by
  classical
  let D := comparisonDirections N
  obtain ⟨E, hE, hEcontrol⟩ := exists_sign_tolerance_function D
  obtain ⟨n, hn, r, c, h₀, hh₀, happ⟩ :=
    happroximation E (fun v => (hE v).1)
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨H, hH, hHone, hHgap⟩ :=
    exists_uniform_dot_gap (Finset.univ.image r) D
  obtain ⟨h, p₀, hh, hhsmall, hh1, hp₀, hrec, hrate⟩ :=
    exists_initial_exponent_parameter x₀ κ hx₀ hH hh₀ hκ
  let cs : Fin n → ℝ := fun j => c j h
  have hcontrol (p : Fin d → ℝ) (hp : ∀ i, |p i| ≤ 1)
      (j : Fin n) (ha : AffineActive r cs (fun i => h ^ p i) j)
      (v : Fin d → ℝ) (hv : v ∈ D) (hne : dot (r j) v ≠ 0) :
      (0 < dot p v ↔ 0 < dot (r j) v) ∧ H < |dot p v| := by
    have hc := hEcontrol (r j) p (happ h hh hhsmall p hp j ha) v hv hne
    have hg := hHgap (r j) (Finset.mem_image_of_mem r (Finset.mem_univ j)) v hv hne
    exact ⟨hc.1, lt_of_le_of_lt hg hc.2.2⟩
  have hp₀cube : ∀ i, |p₀ i| ≤ 1 := fun i => (hp₀ i).le.trans hHone
  have hpoint : (fun i => h ^ p₀ i) = x₀ := funext hrec
  have hinitialgap : ∀ j, AffineActive r cs x₀ j →
      ∀ i, r j i ≠ 0 → H ≤ |p₀ i| := by
    intro j hj i hne
    have ha : AffineActive r cs (fun i => h ^ p₀ i) j := by rwa [hpoint]
    have hc := hcontrol p₀ hp₀cube j ha (coordinateDirection i)
      (coordinateDirection_mem N i) (by simpa using hne)
    simpa using hc.2.le
  obtain ⟨j₀, hj₀⟩ := exists_affineActive r cs x₀
  have hzero : r j₀ = 0 := affineActive_slope_eq_zero r cs x₀ p₀ hp₀ hinitialgap hj₀
  refine ⟨{
    n := n
    n_pos := hn
    slope := r
    offset := cs
    parameter := h
    parameter_pos := hh
    parameter_lt_one := hh1
    constant_branch := j₀
    slope_constant := hzero
    initial_active := hj₀
    initial_inside := ?_
    inward := ?_
    boundary_excluded := ?_ }⟩
  · intro i
    obtain ⟨hpneg, hppos⟩ := abs_lt.mp ((hp₀ i).trans_le hHone)
    constructor
    · have ht := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hppos
      simpa only [Real.rpow_one, hrec i] using ht
    · have ht := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hpneg
      simpa only [Real.rpow_neg_one, hrec i] using ht
  · intro p hp j ha
    apply massAction_inward_of_monomial_order N κ (fun i => h ^ p i) (r j) (h ^ H)
      hweak (fun i => Real.rpow_pos_of_pos hh _) hκ (Real.rpow_nonneg hh.le _) ?_ hrate
    intro y hy z hz hyz
    have hrv : 0 < dot (r j) (complexDifference y z) := by
      rw [dot_complexDifference]
      exact sub_pos.mpr hyz
    have hc := hcontrol p hp j ha (complexDifference y z)
      (complexDifference_mem N hy hz) (ne_of_gt hrv)
    have hpv : 0 < dot p (complexDifference y z) := hc.1.mpr hrv
    have hg : H ≤ dot p (complexDifference y z) := by
      simpa only [abs_of_pos hpv] using hc.2.le
    exact monomial_le_rpow_mul_of_gap hh hh1.le p y z hg
  · intro p hp hpboundary
    exact constant_branch_not_active_on_boundary r cs (fun p i => h ^ p i) E
      (hE 0).2 hzero hpboundary (fun ha => happ h hh hhsmall p hp j₀ ha)

end Problem326.BarrierConstruction

end

end OAI
