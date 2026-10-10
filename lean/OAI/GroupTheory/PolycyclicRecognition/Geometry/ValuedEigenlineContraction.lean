import OAI.GroupTheory.PolycyclicRecognition.Algebra.PowerDominantEigenlines

namespace OAI

/-! # Eigenline contraction over a normed coefficient field

The field change in Tits, Section 4, need not give the original real norm.
This is the concrete linear estimate needed after such a change; no field
embedding or contracting representation is assumed to exist here.
-/

noncomputable section
namespace PolycyclicRecognition.ValuedLinearDynamics

variable {K V : Type*} [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]

def remainder (φ : V →L[K] K) (v x : V) : V := x - φ x • v

theorem remainder_in_ker (φ : V →L[K] K) (v : V) (hφv : φ v = 1) (x : V) :
    φ (remainder φ v x) = 0 := by
  simp [remainder, hφv]

theorem remainder_action (T : V →L[K] V) (φ : V →L[K] K) (v : V) (a : K)
    (hv : T v = a • v) (hφ : ∀ x, φ (T x) = a * φ x) (x : V) :
    remainder φ v (T x) = T (remainder φ v x) := by
  simp only [remainder, hφ, map_sub, map_smul, hv, smul_smul]
  rw [mul_comm a]

theorem functional_power (T : V →L[K] V) (φ : V →L[K] K) (a : K)
    (hφ : ∀ x, φ (T x) = a * φ x) (n : ℕ) (x : V) :
    φ ((T ^ n) x) = a ^ n * φ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change φ (T ((T ^ n) x)) = _
    rw [hφ, ih, pow_succ']
    ring

theorem remainder_power_bound (T : V →L[K] V) (φ : V →L[K] K)
    (v : V) (a : K) (b : ℝ) (hv : T v = a • v) (hφv : φ v = 1)
    (hφ : ∀ x, φ (T x) = a * φ x) (hb : 0 ≤ b)
    (hker : ∀ x, φ x = 0 → ‖T x‖ ≤ b * ‖x‖) (n : ℕ) (x : V) :
    ‖remainder φ v ((T ^ n) x)‖ ≤ b ^ n * ‖remainder φ v x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ‖remainder φ v (T ((T ^ n) x))‖ ≤ _
    rw [remainder_action T φ v a hv hφ]
    calc
      ‖T (remainder φ v ((T ^ n) x))‖ ≤ b * ‖remainder φ v ((T ^ n) x)‖ :=
        hker _ (remainder_in_ker φ v hφv _)
      _ ≤ b * (b ^ n * ‖remainder φ v x‖) := mul_le_mul_of_nonneg_left ih hb
      _ = b ^ (n + 1) * ‖remainder φ v x‖ := by rw [pow_succ']; ring

theorem contracts_cones (T : V →L[K] V) (φ : V →L[K] K)
    (v : V) (a : K) (b : ℝ) (hv : T v = a • v) (hφv : φ v = 1)
    (hφ : ∀ x, φ (T x) = a * φ x) (hb : 0 ≤ b) (hgap : b < ‖a‖)
    (hker : ∀ x, φ x = 0 → ‖T x‖ ≤ b * ‖x‖)
    (M ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : V,
      ‖remainder φ v x‖ ≤ M * ‖φ x‖ →
      ‖remainder φ v ((T ^ n) x)‖ ≤ ε * ‖φ ((T ^ n) x)‖ := by
  have ha : 0 < ‖a‖ := hb.trans_lt hgap
  have ht : Filter.Tendsto (fun n : ℕ => (b / ‖a‖) ^ n * M) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg hb ha.le) ((div_lt_one ha).mpr hgap)).mul_const M
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨N, fun n hn x hx => ?_⟩
  have hsmall : b ^ n * M ≤ ε * ‖a‖ ^ n := by
    have hh := le_of_lt (hN n hn)
    rw [div_pow] at hh
    apply (div_le_iff₀ (pow_pos ha n)).mp
    simpa only [div_mul_eq_mul_div] using hh
  calc
    ‖remainder φ v ((T ^ n) x)‖ ≤ b ^ n * ‖remainder φ v x‖ :=
      remainder_power_bound T φ v a b hv hφv hφ hb hker n x
    _ ≤ b ^ n * (M * ‖φ x‖) := mul_le_mul_of_nonneg_left hx (pow_nonneg hb n)
    _ = (b ^ n * M) * ‖φ x‖ := by ring
    _ ≤ (ε * ‖a‖ ^ n) * ‖φ x‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
    _ = ε * ‖φ ((T ^ n) x)‖ := by rw [functional_power T φ a hφ, norm_mul, norm_pow]; ring

end PolycyclicRecognition.ValuedLinearDynamics

end

end OAI
