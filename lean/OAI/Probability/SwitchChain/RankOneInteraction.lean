import Mathlib

namespace OAI

namespace Problem315
namespace RankOneInteraction

theorem interaction_identity
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f p q u v : E) (c x y : ℝ)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1)
    (huv : inner ℝ u v = c)
    (hfu : inner ℝ f u = x + c * y)
    (hfv : inner ℝ f v = c * x + y)
    (hfp : inner ℝ f p = inner ℝ p p)
    (hfq : inner ℝ f q = inner ℝ q q)
    (hpu : inner ℝ p u = x + c * y)
    (hpv : inner ℝ p v = c * (x + c * y))
    (hqu : inner ℝ q u = c * (c * x + y))
    (hqv : inner ℝ q v = c * x + y)
    (hpq : inner ℝ p q = c * (x + c * y) * (c * x + y)) :
    inner ℝ (f - p) (f - q) =
      ‖f - p - q + (c * y) • u + (c * x) • v‖ ^ 2 +
        inner ℝ (y • (v - c • u)) (x • (u - c • v)) := by
  have huf : inner ℝ u f = x + c * y := by rw [real_inner_comm, hfu]
  have hvf : inner ℝ v f = c * x + y := by rw [real_inner_comm, hfv]
  have hpf : inner ℝ p f = inner ℝ p p := by rw [real_inner_comm, hfp]
  have hqf : inner ℝ q f = inner ℝ q q := by rw [real_inner_comm, hfq]
  have hup : inner ℝ u p = x + c * y := by rw [real_inner_comm, hpu]
  have hvp : inner ℝ v p = c * (x + c * y) := by rw [real_inner_comm, hpv]
  have huq : inner ℝ u q = c * (c * x + y) := by rw [real_inner_comm, hqu]
  have hvq : inner ℝ v q = c * x + y := by rw [real_inner_comm, hqv]
  have hvu : inner ℝ v u = c := by rw [real_inner_comm, huv]
  have hqp : inner ℝ q p = c * (x + c * y) * (c * x + y) := by
    rw [real_inner_comm, hpq]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [huu, hvv, huv, hfu, hfv, hfp, hfq, hpu, hpv, hqu, hqv, hpq,
    huf, hvf, hpf, hqf, hup, hvp, huq, hvq, hvu, hqp]
  ring

theorem interaction_lower_bound
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b j h k : E)
    (hid : inner ℝ h k = ‖j‖ ^ 2 + inner ℝ a b) :
    2 * ‖j‖ ^ 2 - ‖a‖ ^ 2 - ‖b‖ ^ 2 ≤ 2 * inner ℝ h k := by
  have hn : 0 ≤ ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    rw [← norm_add_sq_real]
    exact sq_nonneg _
  linarith

theorem exists_plane_coefficients (α β c : ℝ) (hc : 1 - c ^ 2 ≠ 0) :
    ∃ x y : ℝ, α = x + c * y ∧ β = c * x + y := by
  refine ⟨(α - c * β) / (1 - c ^ 2), (β - c * α) / (1 - c ^ 2), ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

theorem projection_interaction_identity
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (u v : E) (c : ℝ)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : ∀ z, P (Q z) = (c * inner ℝ z v) • u)
    (f : E) (x y : ℝ)
    (hfu : inner ℝ f u = x + c * y) (hfv : inner ℝ f v = c * x + y) :
    inner ℝ (f - P f) (f - Q f) =
      ‖f - P f - Q f + (c * y) • u + (c * x) • v‖ ^ 2 +
        inner ℝ (y • (v - c • u)) (x • (u - c • v)) := by
  apply interaction_identity f (P f) (Q f) u v c x y huu hvv huv hfu hfv
  · simpa only [hPi] using (hPs f (P f)).symm
  · simpa only [hQi] using (hQs f (Q f)).symm
  · rw [hPs, hPu, hfu]
  · rw [hPs, hPv, real_inner_smul_right, hfu]
  · rw [hQs, hQu, real_inner_smul_right, hfv]
  · rw [hQs, hQv, hfv]
  · rw [hPs, hPQ, real_inner_smul_right, hfu, hfv]
    ring

theorem projection_remainder_mem_common_kernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P Q : E →ₗ[ℝ] E)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (u v f : E) (c x y : ℝ)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : P (Q f) = (c * (c * x + y)) • u)
    (hQP : Q (P f) = (c * (x + c * y)) • v) :
    P (f - P f - Q f + (c * y) • u + (c * x) • v) = 0 ∧
    Q (f - P f - Q f + (c * y) • u + (c * x) • v) = 0 := by
  constructor
  · simp only [map_add, map_sub, map_smul, hPi, hPQ, hPu, hPv]
    module
  · simp only [map_add, map_sub, map_smul, hQi, hQP, hQu, hQv]
    module

theorem norm_sq_le_of_inner_eq_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w z : E) (h : inner ℝ z w = inner ℝ w w) : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hn := sq_nonneg ‖z - w‖
  rw [norm_sub_sq_real, h, real_inner_self_eq_norm_sq] at hn
  nlinarith

theorem projection_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hPi : ∀ z, P (P z) = P z)
    (z : E) : ‖P z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  apply norm_sq_le_of_inner_eq_self
  simpa only [hPi] using (hPs z (P z)).symm

theorem error_inner_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f u v : E) (c y : ℝ)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hcoordinate : inner ℝ f v - c * inner ℝ f u = y * (1 - c ^ 2)) :
    inner ℝ f (y • (v - c • u)) =
      inner ℝ (y • (v - c • u)) (y • (v - c • u)) := by
  have hvu : inner ℝ v u = c := by rw [real_inner_comm, huv]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
    huu, hvv, huv, hvu]
  rw [hcoordinate]
  ring

theorem error_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →ₗ[ℝ] E) (hRs : R.IsSymmetric) (f w : E)
    (hRw : R w = w) (hfw : inner ℝ f w = inner ℝ w w) :
    ‖w‖ ^ 2 ≤ ‖R f‖ ^ 2 := by
  apply norm_sq_le_of_inner_eq_self
  rw [hRs, hRw, hfw]

theorem rank_one_disjoint_interaction
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (u v : E) (c : ℝ) (hc : 1 - c ^ 2 ≠ 0)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : ∀ z, P (Q z) = (c * inner ℝ z v) • u)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - c • u) = v - c • u)
    (hSline : S (u - c • v) = u - c • v)
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * inner ℝ (f - P f) (f - Q f) := by
  obtain ⟨x, y, hfu, hfv⟩ := exists_plane_coefficients (inner ℝ f u) (inner ℝ f v) c hc
  let j := f - P f - Q f + (c * y) • u + (c * x) • v
  let a := y • (v - c • u)
  let b := x • (u - c • v)
  have hid : inner ℝ (f - P f) (f - Q f) = ‖j‖ ^ 2 + inner ℝ a b :=
    projection_interaction_identity P Q hPs hQs hPi hQi u v c huu hvv huv
      hPu hPv hQu hQv hPQ f x y hfu hfv
  have hGu : G u = 0 := by rw [← hPu, hGP]
  have hGv : G v = 0 := by rw [← hQv, hGQ]
  have hGj : G j = G f := by
    simp only [j, map_add, map_sub, map_smul, hGP, hGQ, hGu, hGv,
      smul_zero, sub_zero, add_zero]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [← hGj]
    exact projection_norm_sq_le G hGs hGi j
  have hfa : inner ℝ f a = inner ℝ a a := by
    apply error_inner_self f u v c y huu hvv huv
    rw [hfu, hfv]
    ring
  have hfb : inner ℝ f b = inner ℝ b b := by
    apply error_inner_self f v u c x hvv huu
      (by rw [real_inner_comm, huv])
    rw [hfu, hfv]
    ring
  have hra : ‖a‖ ^ 2 ≤ ‖R f‖ ^ 2 :=
    error_norm_sq_le R hRs f a (by simp only [a, map_smul, hRline]) hfa
  have hsb : ‖b‖ ^ 2 ≤ ‖S f‖ ^ 2 :=
    error_norm_sq_le S hSs f b (by simp only [b, map_smul, hSline]) hfb
  have hlocal := interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

theorem composition_of_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (u v : E) (c : ℝ)
    (hcov : ∀ z w, inner ℝ (P z) (Q w) = c * inner ℝ z u * inner ℝ w v)
    (f : E) : P (Q f) = (c * inner ℝ f v) • u := by
  apply ext_inner_left ℝ
  intro z
  rw [← hPs, hcov, real_inner_smul_right]
  ring

theorem rank_one_disjoint_interaction_of_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (u v : E) (c : ℝ) (hc : 1 - c ^ 2 ≠ 0)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1)
    (hPu : P u = u) (hQv : Q v = v)
    (hcov : ∀ z w, inner ℝ (P z) (Q w) = c * inner ℝ z u * inner ℝ w v)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - c • u) = v - c • u)
    (hSline : S (u - c • v) = u - c • v)
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * inner ℝ (f - P f) (f - Q f) := by
  have hPQ := composition_of_covariance P Q hPs u v c hcov
  have hcov' : ∀ z w, inner ℝ (Q z) (P w) = c * inner ℝ z v * inner ℝ w u := by
    intro z w
    rw [real_inner_comm, hcov]
    ring
  have hQP := composition_of_covariance Q P hQs v u c hcov'
  have hPv : P v = c • u := by simpa only [hQv, hvv, mul_one] using hPQ v
  have hQu : Q u = c • v := by simpa only [hPu, huu, mul_one] using hQP u
  have huv : inner ℝ u v = c := by
    simpa only [hPu, hQv, huu, hvv, mul_one] using hcov u v
  exact rank_one_disjoint_interaction P Q G R S hPs hQs hGs hRs hSs hPi hQi hGi
    u v c hc huu hvv huv hPu hPv hQu hQv hPQ hGP hGQ hRline hSline f

theorem independent_interaction_identity
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hPQ : ∀ z, P (Q z) = 0) (f : E) :
    inner ℝ (f - P f) (f - Q f) = ‖f - P f - Q f‖ ^ 2 := by
  have hfp : inner ℝ f (P f) = inner ℝ (P f) (P f) := by
    simpa only [hPi] using (hPs f (P f)).symm
  have hfq : inner ℝ f (Q f) = inner ℝ (Q f) (Q f) := by
    simpa only [hQi] using (hQs f (Q f)).symm
  have hpf : inner ℝ (P f) f = inner ℝ (P f) (P f) := by rw [real_inner_comm, hfp]
  have hqf : inner ℝ (Q f) f = inner ℝ (Q f) (Q f) := by rw [real_inner_comm, hfq]
  have hpq : inner ℝ (P f) (Q f) = 0 := by rw [hPs, hPQ, inner_zero_right]
  have hqp : inner ℝ (Q f) (P f) = 0 := by rw [real_inner_comm, hpq]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, hfp, hfq, hpf, hqf, hpq, hqp]
  ring

theorem independent_disjoint_interaction
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hPQ : ∀ z, P (Q z) = 0)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (f : E) : ‖G f‖ ^ 2 ≤ inner ℝ (f - P f) (f - Q f) := by
  rw [independent_interaction_identity P Q hPs hQs hPi hQi hPQ f]
  have hG : G (f - P f - Q f) = G f := by
    simp only [map_sub, hGP, hGQ, sub_zero]
  rw [← hG]
  exact projection_norm_sq_le G hGs hGi _

end RankOneInteraction
end Problem315

end OAI
