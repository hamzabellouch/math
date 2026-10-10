import OAI.InformationTheory.QuantumCircuit.ApproximationBudget

namespace OAI

/-! Product input states and their excitation counts. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

def pureProjector {N : ℕ} (ψ : State N) : Operator N :=
  fun x y => ψ x * star (ψ y)

structure ProductInput (N : ℕ) where
  state : State N
  norm_state : ‖state‖ = 1
  test : Count N
  full_support : test.support = Finset.univ
  projector : test.zero = pureProjector state

lemma act_pureProjector {N : ℕ} (ψ ξ : State N) :
    act (pureProjector ψ) ξ = (inner ℂ ψ ξ) • ψ := by
  ext x
  change ∑ y, (ψ x * star (ψ y)) * ξ y = (inner ℂ ψ ξ) * ψ x
  calc
    _ = ψ x * (∑ y, star (ψ y) * ξ y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ψ x * inner ℂ ψ ξ := by
      congr 1
      simp only [PiLp.inner_apply, RCLike.inner_apply]
      apply Finset.sum_congr rfl
      intro y _
      exact mul_comm _ _
    _ = _ := mul_comm _ _

lemma act_smul_state {N : ℕ} (A : Operator N) (c : ℂ) (ψ : State N) :
    act A (c • ψ) = c • act A ψ := by simp [act]

lemma inner_act_right {N : ℕ} (A : Operator N) (ψ ξ : State N) :
    inner ℂ ψ (act A ξ) = inner ℂ (act (star A) ψ) ξ := by
  have hh := ContinuousLinearMap.adjoint_inner_left
    (Matrix.toEuclideanCLM (n := Word N) (𝕜 := ℂ) A) ξ ψ
  simpa only [act, map_star, ContinuousLinearMap.star_eq_adjoint] using hh.symm

lemma projection_inner_self {N : ℕ} (Q : Operator N) (hQ : IsStarProjection Q)
    (ψ : State N) : inner ℂ ψ (act Q ψ) = (‖act Q ψ‖ ^ 2 : ℝ) := by
  calc
    _ = inner ℂ (act Q ψ) (act Q ψ) := by
      have hh := inner_act_right Q ψ (act Q ψ)
      rw [← act_mul, hQ.isIdempotentElem.eq, hQ.isSelfAdjoint.star_eq] at hh
      exact hh
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

lemma conjugated_product_projection_action {N : ℕ} (P : ProductInput N)
    (U : Operator N) (Q : Operator N) (hQ : IsStarProjection Q) :
    act (conjugate U P.test.zero) (act Q (act U P.state)) =
      ((‖act Q (act U P.state)‖ ^ 2 : ℝ) : ℂ) • act U P.state := by
  simp only [conjugate, act_mul, P.projector, act_pureProjector, act_smul_state]
  rw [inner_act_right (star U), star_star, projection_inner_self Q hQ]

theorem uniform_product_overlap_tail (d : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (P : ∀ ν, ProductInput (m ν)) {p h : ℝ} (hp : 0 < p) (hph : p < h) :
    ∀ᶠ ν in atTop, ∀ U : Operator (m ν), IsCircuit d U → ∀ B : Count (m ν),
      ‖act B.zero (act U (P ν).state)‖^2 *
        ‖act (B.high ((m ν : ℝ)^h)) (act U (P ν).state)‖ ≤
          Real.exp (-((m ν : ℝ)^p)) := by
  filter_upwards [hm.eventually (uniform_localization d p h hp.le hph)] with ν hh
  intro U hU B
  let ψ := act U (P ν).state
  have hψ : ‖ψ‖ = 1 := (act_unitary_norm hU.mem_unitary _).trans (P ν).norm_state
  have hb := act_norm_le (B.high ((m ν : ℝ)^h) * conjugate U (P ν).test.zero * B.zero) ψ
  rw [hψ, mul_one] at hb
  have hid := conjugated_product_projection_action (P ν) U B.zero B.zero_projection
  have heq : act (B.high ((m ν : ℝ)^h) * conjugate U (P ν).test.zero * B.zero) ψ =
      ((‖act B.zero ψ‖^2 : ℝ) : ℂ) • act (B.high ((m ν : ℝ)^h)) ψ := by
    rw [act_mul, act_mul, hid, act_smul_state]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
  exact hb.trans (hh U hU B (P ν).test)

 theorem product_overlap_tail (d : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : ∀ ν, Operator (m ν)) (hU : ∀ ν, IsCircuit d (U ν))
    (P : ∀ ν, ProductInput (m ν)) {p h : ℝ} (hp : 0 < p) (hph : p < h) :
    ∀ᶠ ν in atTop, ∀ B : Count (m ν),
      ‖act B.zero (act (U ν) (P ν).state)‖^2 *
        ‖act (B.high ((m ν : ℝ)^h)) (act (U ν) (P ν).state)‖ ≤
          Real.exp (-((m ν : ℝ)^p)) := by
  filter_upwards [uniform_product_overlap_tail d m hm P hp hph] with ν hh
  exact hh (U ν) (hU ν)

end QAC

end

end OAI
