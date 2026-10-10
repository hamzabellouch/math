import Mathlib

namespace OAI

open Filter
open scoped Topology
namespace Problem367
section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

lemma selfAdjoint_pow_norm_sq_le (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (x : E) (n : ℕ) :
    ‖(T ^ n) x‖ ^ 2 ≤ ‖(T ^ (2 * n)) x‖ * ‖x‖ := by
  calc
    ‖(T ^ n) x‖ ^ 2 = RCLike.re (inner 𝕜 ((T ^ n) x) ((T ^ n) x)) :=
      (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (inner 𝕜 ((T ^ n) ((T ^ n) x)) x) :=
      congrArg RCLike.re ((hT.pow n).isSymmetric ((T ^ n) x) x).symm
    _ = RCLike.re (inner 𝕜 ((T ^ (2 * n)) x) x) := by
      rw [two_mul, pow_add, mul_apply_eq_comp]
    _ ≤ ‖(T ^ (2 * n)) x‖ * ‖x‖ := re_inner_le_norm _ _

lemma selfAdjoint_norm_pow_two_pow_le (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (x : E) (hx : ‖x‖ = 1) (n : ℕ) :
    ‖T x‖ ^ (2 ^ n) ≤ ‖(T ^ (2 ^ n)) x‖ := by
  induction n with
  | zero => simp
  | succ n hn =>
    calc
      ‖T x‖ ^ (2 ^ (n + 1)) = (‖T x‖ ^ (2 ^ n)) ^ 2 := by
        rw [pow_succ, pow_mul]
      _ ≤ ‖(T ^ (2 ^ n)) x‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hn 2
      _ ≤ ‖(T ^ (2 * 2 ^ n)) x‖ := by
        simpa [hx] using selfAdjoint_pow_norm_sq_le T hT x (2 ^ n)
      _ = ‖(T ^ (2 ^ (n + 1))) x‖ := by rw [pow_succ, Nat.mul_comm]

lemma selfAdjoint_norm_apply_le_of_unit_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (x : E) (hx : ‖x‖ = 1)
    {rho C : ℝ} (hrho : 0 ≤ rho)
    (hbound : ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T x‖ ≤ rho := by
  rcases eq_or_lt_of_le hrho with hrho | hrho
  · simpa [← hrho] using hbound 1
  by_contra hnot
  have hratio : 1 < ‖T x‖ / rho := (one_lt_div hrho).2 (lt_of_not_ge hnot)
  have hlim : Tendsto (fun n : ℕ => (‖T x‖ / rho) ^ (2 ^ n)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hratio).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  obtain ⟨n, hn⟩ := (hlim.eventually_gt_atTop C).exists
  have hle : (‖T x‖ / rho) ^ (2 ^ n) ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hrho _)]
    exact (selfAdjoint_norm_pow_two_pow_le T hT x hx n).trans (hbound (2 ^ n))
  exact (not_lt_of_ge hle) hn

lemma selfAdjoint_norm_apply_le_of_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (x : E)
    {rho C : ℝ} (hrho : 0 ≤ rho)
    (hbound : ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T x‖ ≤ rho * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
  let y : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, inv_mul_cancel₀ hnx.ne']
  have hby (n : ℕ) : ‖(T ^ n) y‖ ≤ (‖x‖⁻¹ * C) * rho ^ n := by
    simpa [y, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hi, mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound n) hi
  have h := selfAdjoint_norm_apply_le_of_unit_power_bound T hT y hy hrho hby
  have hdiv : ‖T x‖ / ‖x‖ ≤ rho := by
    simpa [y, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hi, div_eq_mul_inv, mul_comm]
      using h
  exact (div_le_iff₀ hnx).mp hdiv

lemma selfAdjoint_norm_apply_le_on_closure_of_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E}
    (hbound : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n)
    {x : E} (hx : x ∈ closure s) : ‖T x‖ ≤ rho * ‖x‖ := by
  have hc : IsClosed {x : E | ‖T x‖ ≤ rho * ‖x‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  have hsub : s ⊆ {x : E | ‖T x‖ ≤ rho * ‖x‖} := by
    intro x hx
    obtain ⟨C, hC⟩ := hbound x hx
    exact selfAdjoint_norm_apply_le_of_power_bound T hT x hrho hC
  exact hc.closure_subset_iff.mpr hsub hx

lemma selfAdjoint_opNorm_le_of_dense_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E} (hs : Dense s)
    (hbound : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T‖ ≤ rho := by
  refine T.opNorm_le_bound hrho fun x => ?_
  exact selfAdjoint_norm_apply_le_on_closure_of_power_bound T hT hrho hbound
    (by rw [hs.closure_eq]; trivial)

lemma selfAdjoint_opNorm_le_of_dense_even_moment_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E} (hs : Dense s)
    (hmoment : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ,
      RCLike.re (inner 𝕜 x ((T ^ (2 * n)) x)) ≤ C * rho ^ (2 * n)) :
    ‖T‖ ≤ rho := by
  apply selfAdjoint_opNorm_le_of_dense_power_bound T hT hrho hs
  intro x hx
  obtain ⟨C, hC⟩ := hmoment x hx
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp only [Nat.mul_zero, pow_zero, one_apply_eq_self, mul_one,
      inner_self_eq_norm_sq] at h
    exact (sq_nonneg ‖x‖).trans h
  refine ⟨Real.sqrt C, fun n => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hrho _))).mp
  rw [mul_pow, Real.sq_sqrt hC0, ← pow_mul, Nat.mul_comm n 2]
  have heq : ‖(T ^ n) x‖ ^ 2 = RCLike.re (inner 𝕜 x ((T ^ (2 * n)) x)) := by
    calc
      ‖(T ^ n) x‖ ^ 2 = RCLike.re (inner 𝕜 ((T ^ n) x) ((T ^ n) x)) :=
        (inner_self_eq_norm_sq _).symm
      _ = RCLike.re (inner 𝕜 x ((T ^ n) ((T ^ n) x))) :=
        congrArg RCLike.re ((hT.pow n).isSymmetric x ((T ^ n) x))
      _ = RCLike.re (inner 𝕜 x ((T ^ (2 * n)) x)) := by
        rw [two_mul, pow_add, mul_apply_eq_comp]
  rw [heq]
  exact hC n

omit [CompleteSpace E] in

lemma norm_pow_apply_le_of_intertwiner
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] E) (A : G →L[𝕜] G) (D : G →L[𝕜] E)
    (hcomm : ∀ x : G, T (D x) = D (A x)) {rho : ℝ}
    (hrho : 0 ≤ rho) (hA : ‖A‖ ≤ rho) (x : G) (n : ℕ) :
    ‖(T ^ n) (D x)‖ ≤ (‖D‖ * ‖x‖) * rho ^ n := by
  have hp (n : ℕ) : (T ^ n) (D x) = D ((A ^ n) x) := by
    induction n with
    | zero => simp
    | succ n hn =>
      simp only [pow_succ', mul_apply_eq_comp, hn, hcomm]
  have hb (n : ℕ) : ‖(A ^ n) x‖ ≤ rho ^ n * ‖x‖ := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ', mul_apply_eq_comp]
      calc
        ‖A ((A ^ n) x)‖ ≤ ‖A‖ * ‖(A ^ n) x‖ := A.le_opNorm _
        _ ≤ rho * (rho ^ n * ‖x‖) :=
          mul_le_mul hA hn (norm_nonneg _) hrho
        _ = rho ^ (n + 1) * ‖x‖ := by ring
  rw [hp]
  calc
    ‖D ((A ^ n) x)‖ ≤ ‖D‖ * ‖(A ^ n) x‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (rho ^ n * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)
    _ = (‖D‖ * ‖x‖) * rho ^ n := by ring

lemma selfAdjoint_norm_apply_le_on_closure_range_of_intertwiner
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (A : G →L[𝕜] G)
    (D : G →L[𝕜] E) (hcomm : ∀ x : G, T (D x) = D (A x))
    {rho : ℝ} (hrho : 0 ≤ rho) (hA : ‖A‖ ≤ rho)
    {x : E} (hx : x ∈ closure (Set.range D)) : ‖T x‖ ≤ rho * ‖x‖ := by
  apply selfAdjoint_norm_apply_le_on_closure_of_power_bound T hT hrho (s := Set.range D) ?_ hx
  rintro _ ⟨y, rfl⟩
  exact ⟨‖D‖ * ‖y‖, norm_pow_apply_le_of_intertwiner T A D hcomm hrho hA y⟩

lemma selfAdjoint_opNorm_le_of_dense_intertwiner
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (A : G →L[𝕜] G)
    (D : G →L[𝕜] E) (hD : DenseRange D)
    (hcomm : ∀ x : G, T (D x) = D (A x)) {rho : ℝ}
    (hrho : 0 ≤ rho) (hA : ‖A‖ ≤ rho) : ‖T‖ ≤ rho := by
  refine T.opNorm_le_bound hrho fun x => ?_
  exact selfAdjoint_norm_apply_le_on_closure_range_of_intertwiner T hT A D hcomm hrho hA
    (by rw [hD.closure_range]; trivial)

end
end Problem367

end OAI
