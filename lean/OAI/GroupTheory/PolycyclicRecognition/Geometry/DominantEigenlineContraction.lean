import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # Contraction toward a dominant real eigenline

A strict spectral gap contracts cones uniformly. The statement is expressed
on vectors, so it can later be applied to the projective action without a
choice of normalized representatives.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def eigenlineRemainder (φ : V →L[ℝ] ℝ) (v x : V) : V := x - φ x • v

theorem eigenlineRemainder_in_ker (φ : V →L[ℝ] ℝ) (v : V) (hφv : φ v = 1) (x : V) :
    φ (eigenlineRemainder φ v x) = 0 := by
  simp [eigenlineRemainder, hφv]

theorem eigenlineRemainder_action (T : V →L[ℝ] V) (φ : V →L[ℝ] ℝ)
    (v : V) (a : ℝ) (hv : T v = a • v)
    (hφ : ∀ x, φ (T x) = a * φ x) (x : V) :
    eigenlineRemainder φ v (T x) = T (eigenlineRemainder φ v x) := by
  simp only [eigenlineRemainder, hφ, map_sub, map_smul, hv, smul_smul]
  rw [mul_comm a]

theorem eigenline_functional_power (T : V →L[ℝ] V) (φ : V →L[ℝ] ℝ)
    (a : ℝ) (hφ : ∀ x, φ (T x) = a * φ x) (n : ℕ) (x : V) :
    φ ((T ^ n) x) = a ^ n * φ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change φ (T ((T ^ n) x)) = _
    rw [hφ, ih, pow_succ']
    ring

theorem eigenlineRemainder_power_bound (T : V →L[ℝ] V) (φ : V →L[ℝ] ℝ)
    (v : V) (a b : ℝ) (hv : T v = a • v) (hφv : φ v = 1)
    (hφ : ∀ x, φ (T x) = a * φ x) (hb : 0 ≤ b)
    (hker : ∀ x, φ x = 0 → ‖T x‖ ≤ b * ‖x‖) (n : ℕ) (x : V) :
    ‖eigenlineRemainder φ v ((T ^ n) x)‖ ≤ b ^ n * ‖eigenlineRemainder φ v x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ‖eigenlineRemainder φ v (T ((T ^ n) x))‖ ≤ _
    rw [eigenlineRemainder_action T φ v a hv hφ]
    calc
      ‖T (eigenlineRemainder φ v ((T ^ n) x))‖ ≤
          b * ‖eigenlineRemainder φ v ((T ^ n) x)‖ :=
        hker _ (eigenlineRemainder_in_ker φ v hφv _)
      _ ≤ b * (b ^ n * ‖eigenlineRemainder φ v x‖) := mul_le_mul_of_nonneg_left ih hb
      _ = b ^ (n + 1) * ‖eigenlineRemainder φ v x‖ := by rw [pow_succ']; ring

theorem dominant_eigenline_contracts_cones (T : V →L[ℝ] V) (φ : V →L[ℝ] ℝ)
    (v : V) (a b : ℝ) (hv : T v = a • v) (hφv : φ v = 1)
    (hφ : ∀ x, φ (T x) = a * φ x) (hb : 0 ≤ b) (hgap : b < |a|)
    (hker : ∀ x, φ x = 0 → ‖T x‖ ≤ b * ‖x‖)
    (M ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : V,
      ‖eigenlineRemainder φ v x‖ ≤ M * |φ x| →
      ‖eigenlineRemainder φ v ((T ^ n) x)‖ ≤ ε * |φ ((T ^ n) x)| := by
  have ha : 0 < |a| := lt_of_le_of_lt hb hgap
  have hr0 : 0 ≤ b / |a| := div_nonneg hb (le_of_lt ha)
  have hr1 : b / |a| < 1 := (div_lt_one ha).mpr hgap
  have ht : Filter.Tendsto (fun n : ℕ => (b / |a|) ^ n * M) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const M
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨N, fun n hn x hx => ?_⟩
  have hsmall : b ^ n * M ≤ ε * |a| ^ n := by
    have hh := le_of_lt (hN n hn)
    rw [div_pow] at hh
    have hp : 0 < |a| ^ n := pow_pos ha n
    apply (div_le_iff₀ hp).mp
    simpa only [div_mul_eq_mul_div] using hh
  calc
    ‖eigenlineRemainder φ v ((T ^ n) x)‖ ≤ b ^ n * ‖eigenlineRemainder φ v x‖ :=
      eigenlineRemainder_power_bound T φ v a b hv hφv hφ hb hker n x
    _ ≤ b ^ n * (M * |φ x|) := mul_le_mul_of_nonneg_left hx (pow_nonneg hb n)
    _ = (b ^ n * M) * |φ x| := by ring
    _ ≤ (ε * |a| ^ n) * |φ x| := mul_le_mul_of_nonneg_right hsmall (abs_nonneg _)
    _ = ε * |φ ((T ^ n) x)| := by rw [eigenline_functional_power T φ a hφ, abs_mul, abs_pow]; ring


theorem compact_eigenline_ratio_bound (φ : V →L[ℝ] ℝ) (v : V)
    (C : Set V) (hC : IsCompact C) (hφ : ∀ x ∈ C, φ x ≠ 0) :
    ∃ M : ℝ, ∀ x ∈ C, ‖eigenlineRemainder φ v x‖ ≤ M * |φ x| := by
  have hc : Continuous (eigenlineRemainder φ v) :=
    continuous_id.sub (φ.continuous.smul continuous_const)
  have hr : ContinuousOn (fun x => ‖eigenlineRemainder φ v x‖ / |φ x|) C :=
    hc.norm.continuousOn.div φ.continuous.abs.continuousOn
      (fun x hx => abs_ne_zero.mpr (hφ x hx))
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hr
  refine ⟨M, fun x hx => ?_⟩
  apply (div_le_iff₀ (abs_pos.mpr (hφ x hx))).mp
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM x hx)

theorem dominant_eigenline_compact_contraction (T : V →L[ℝ] V) (φ : V →L[ℝ] ℝ)
    (v : V) (a b : ℝ) (hv : T v = a • v) (hφv : φ v = 1)
    (hφ : ∀ x, φ (T x) = a * φ x) (hb : 0 ≤ b) (hgap : b < |a|)
    (hker : ∀ x, φ x = 0 → ‖T x‖ ≤ b * ‖x‖)
    (C : Set V) (hC : IsCompact C) (hCφ : ∀ x ∈ C, φ x ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ C,
      φ ((T ^ n) x) ≠ 0 ∧
        ‖eigenlineRemainder φ v ((T ^ n) x)‖ ≤ ε * |φ ((T ^ n) x)| := by
  obtain ⟨M, hM⟩ := compact_eigenline_ratio_bound φ v C hC hCφ
  obtain ⟨N, hN⟩ := dominant_eigenline_contracts_cones T φ v a b hv hφv hφ hb hgap
    hker M ε hε
  refine ⟨N, fun n hn x hx => ⟨?_, hN n hn x (hM x hx)⟩⟩
  rw [eigenline_functional_power T φ a hφ]
  apply mul_ne_zero (pow_ne_zero _ ?_) (hCφ x hx)
  exact abs_ne_zero.mp (ne_of_gt (lt_of_le_of_lt hb hgap))

end PolycyclicRecognition

end

end OAI
