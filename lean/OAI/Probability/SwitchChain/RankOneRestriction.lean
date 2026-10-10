import OAI.Probability.SwitchChain.RankOneCentering

namespace OAI

noncomputable section

namespace Problem315.RankOneInteraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symmetric_restrict (U : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) :
    (A.restrict hU).IsSymmetric := by
  intro x y
  exact hA x.val y.val

theorem idempotent_restrict (U : Submodule ℝ E) (A : E →ₗ[ℝ] E)
    (hA : ∀ x, A (A x) = A x) (hU : ∀ x ∈ U, A x ∈ U)
    (x : U) : A.restrict hU (A.restrict hU x) = A.restrict hU x := by
  apply Subtype.ext
  exact hA x.val

theorem disjoint_interaction_on_invariant_submodule
    (U : Submodule ℝ E) (P Q G R S : E →ₗ[ℝ] E)
    (hPU : ∀ x ∈ U, P x ∈ U) (hQU : ∀ x ∈ U, Q x ∈ U)
    (hGU : ∀ x ∈ U, G x ∈ U) (hRU : ∀ x ∈ U, R x ∈ U)
    (hSU : ∀ x ∈ U, S x ∈ U)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (e u v : U) (c : ℝ) (hc : 1 - c ^ 2 ≠ 0)
    (hee : inner ℝ e e = 1) (huu : inner ℝ u u = 1)
    (hvv : inner ℝ v v = 1) (hue : inner ℝ u e = 0)
    (hve : inner ℝ v e = 0)
    (hPe : P e = e) (hQe : Q e = e) (hPu : P u = u) (hQv : Q v = v)
    (hcov : ∀ z w : U, inner ℝ (P z) (Q w) =
      inner ℝ z e * inner ℝ w e + c * inner ℝ z u * inner ℝ w v)
    (hGe : G e = 0) (hRe : R e = 0) (hSe : S e = 0)
    (hGP : ∀ z : U, G (P z) = 0) (hGQ : ∀ z : U, G (Q z) = 0)
    (hRline : R ((v : E) - c • (u : E)) = (v : E) - c • (u : E))
    (hSline : S ((u : E) - c • (v : E)) = (u : E) - c • (v : E))
    (f : U) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * inner ℝ ((f : E) - P f) ((f : E) - Q f) := by
  exact disjoint_interaction_with_constants
    (P.restrict hPU) (Q.restrict hQU) (G.restrict hGU)
    (R.restrict hRU) (S.restrict hSU)
    (symmetric_restrict U P hPs hPU) (symmetric_restrict U Q hQs hQU)
    (symmetric_restrict U G hGs hGU) (symmetric_restrict U R hRs hRU)
    (symmetric_restrict U S hSs hSU)
    (idempotent_restrict U P hPi hPU) (idempotent_restrict U Q hQi hQU)
    (idempotent_restrict U G hGi hGU)
    e u v c hc hee huu hvv hue hve
    (Subtype.ext hPe) (Subtype.ext hQe) (Subtype.ext hPu) (Subtype.ext hQv)
    hcov (Subtype.ext hGe) (Subtype.ext hRe) (Subtype.ext hSe)
    (fun z => Subtype.ext (hGP z)) (fun z => Subtype.ext (hGQ z))
    (Subtype.ext hRline) (Subtype.ext hSline) f

theorem independent_interaction_on_invariant_submodule
    (U : Submodule ℝ E) (P Q G : E →ₗ[ℝ] E)
    (hPU : ∀ x ∈ U, P x ∈ U) (hQU : ∀ x ∈ U, Q x ∈ U)
    (hGU : ∀ x ∈ U, G x ∈ U)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (e : U) (hee : inner ℝ e e = 1) (hPe : P e = e) (hQe : Q e = e)
    (hcov : ∀ z w : U, inner ℝ (P z) (Q w) = inner ℝ z e * inner ℝ w e)
    (hGe : G e = 0)
    (hGP : ∀ z : U, G (P z) = 0) (hGQ : ∀ z : U, G (Q z) = 0)
    (f : U) :
    ‖G f‖ ^ 2 ≤ inner ℝ ((f : E) - P f) ((f : E) - Q f) := by
  exact independent_interaction_with_constants
    (P.restrict hPU) (Q.restrict hQU) (G.restrict hGU)
    (symmetric_restrict U P hPs hPU) (symmetric_restrict U Q hQs hQU)
    (symmetric_restrict U G hGs hGU)
    (idempotent_restrict U P hPi hPU) (idempotent_restrict U Q hQi hQU)
    (idempotent_restrict U G hGi hGU)
    e hee (Subtype.ext hPe) (Subtype.ext hQe) hcov (Subtype.ext hGe)
    (fun z => Subtype.ext (hGP z)) (fun z => Subtype.ext (hGQ z)) f

end Problem315.RankOneInteraction

end

end OAI
