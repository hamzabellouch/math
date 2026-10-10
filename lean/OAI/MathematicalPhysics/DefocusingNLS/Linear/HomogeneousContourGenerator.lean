import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCanonicalContour
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorEigenvector
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSemigroupDecay

namespace OAI

/-! # The generator on the actual contour complement

For the manuscript threshold -1/32, a contracting-plus-finite-rank step
produces a finite-dimensional generator whose eigenvalues are strictly to
the right of that line. The complementary evolution decays exponentially.
-/

open scoped NNReal

namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The exact invariant projection, decaying kernel, and finite generator data. -/
def HasFiniteContourGenerator (S : ℝ≥0 → E →L[ℂ] E) : Prop :=
    ∃ Q : E →L[ℂ] E, IsIdempotentElem Q ∧
      FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
      ∃ hcomm : ∀ s, Commute (S s) Q,
      (∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ s : ℝ≥0, ∀ u, Q u = 0 →
        ‖S s u‖ ≤ D * Real.exp (-δ * (s : ℝ)) * ‖u‖) ∧
      ∃ G : Q.range →L[ℂ] Q.range,
        (∀ s : ℝ≥0, projectionSemigroupRestriction S Q hcomm s =
          NormedSpace.exp ((s : ℝ) • G)) ∧
        ∀ lam : ℂ, ∀ u : Q.range, u ≠ 0 → G u = lam • u → -(1 / 32 : ℝ) < lam.re

theorem semigroup_contour_generator (S : ℝ≥0 → E →L[ℂ] E)
    (hzero : S 0 = 1) (hadd : ∀ s t, S (s + t) = S t * S s)
    (hS : ∀ x : E, Continuous (fun t => S t x))
    (τ : ℝ≥0) (hτ : 0 < τ) (B K : E →L[ℂ] E)
    (hstep : S τ = B + K) (hB : ‖B‖ < 1)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap)) :
    HasFiniteContourGenerator S := by
  have hτR : 0 < (τ : ℝ) := hτ
  have hη : Real.exp (-(τ : ℝ) / 32) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hτR) (by norm_num)
  obtain ⟨r, hηr, hr0, hr1, hres, Q, hQeq, hQ, hfin, hcomm0, C, hC, hpowers⟩ :=
    finiteRank_canonical_contour_decomposition B K hB hK
      (Real.exp (-(τ : ℝ) / 32)) hη
  have hcomm (s : ℝ≥0) : Commute (S s) Q := by
    apply hcomm0
    rw [← hstep]
    change S s * S τ = S τ * S s
    rw [← hadd, ← hadd, add_comm s τ]
  obtain ⟨G, hG⟩ := projectionSemigroupRestriction_eq_exp S Q hcomm hfin hS hzero hadd
  refine ⟨Q, hQ, hfin, hcomm, ?_, G, hG, ?_⟩
  · apply continuous_decay_of_step_decay S hzero hadd hS
      {u | Q u = 0} τ hτ r C hr0 hr1 hC
    intro j u hu
    simpa only [hstep] using hpowers j u hu
  · intro lam u hu hGu
    let : FiniteDimensional ℂ Q.range := hfin
    have hu0 : (u : E) ≠ 0 := by
      intro he
      apply hu
      exact Subtype.ext he
    have hfix : Q (u : E) = u := by
      obtain ⟨v, hv⟩ := u.property
      rw [← hv]
      exact congrArg (fun L : E →L[ℂ] E => L v) hQ
    have he := real_smul_operator_exp_apply_of_eigenvector G lam u hGu (τ : ℝ)
    have hsu : (S τ) (u : E) = Complex.exp (((τ : ℝ) : ℂ) * lam) • (u : E) := by
      have hh := congrArg (fun L : Q.range →L[ℂ] Q.range => (L u : E)) (hG τ)
      change S τ (u : E) = (NormedSpace.exp ((τ : ℝ) • G) u : E) at hh
      rw [he] at hh
      exact hh
    have hmod : r < ‖Complex.exp (((τ : ℝ) : ℂ) * lam)‖ := by
      apply contourComplement_eigenvector_modulus (S τ) hr0
        (fun z hz => by simpa only [hstep] using hres z hz) hu0 hsu
      simpa only [hstep, ← hQeq] using hfix
    apply generator_realPart_gt_of_step_modulus lam (τ : ℝ) (1 / 32) hτR
    convert hηr.trans hmod using 1
    congr 1
    ring

end DefocusingNLS

end OAI
