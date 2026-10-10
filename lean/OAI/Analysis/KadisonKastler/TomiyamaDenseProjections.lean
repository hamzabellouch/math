import OAI.Analysis.KadisonKastler.TomiyamaBimodule

namespace OAI

/-! # Extension from projections to their norm-closed span -/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A surjective star homomorphism preserves norm-density of projection spans. -/
theorem closed_projection_span_eq_top_of_surjective
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Surjective φ)
    (hdense : (Submodule.span ℂ {e : A | IsStarProjection e}).topologicalClosure = ⊤) :
    (Submodule.span ℂ {e : B | IsStarProjection e}).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℂ {e : B | IsStarProjection e}).topologicalClosure
  let R := S.comap φ.toAlgHom.toLinearMap
  have hR : IsClosed (R : Set A) :=
    (Submodule.isClosed_topologicalClosure _).preimage (map_continuous φ)
  have hspan : Submodule.span ℂ {e : A | IsStarProjection e} ≤ R := by
    apply Submodule.span_le.mpr
    intro e he
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (he.map φ))
  have htop := (Submodule.span ℂ {e : A | IsStarProjection e}).topologicalClosure_minimal
    hspan hR
  rw [hdense] at htop
  apply top_unique
  intro b _
  obtain ⟨a, rfl⟩ := hφ b
  exact htop (show a ∈ (⊤ : Submodule ℂ A) from Submodule.mem_top)

/-- The algebraic projection identities extend to a target whose
projections have norm-dense linear span. -/
theorem tomiyama_map_mul_of_dense_projections
    (hdense : (Submodule.span ℂ {e : B | IsStarProjection e}).topologicalClosure = ⊤)
    (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b) :
    (∀ b x, P (φ b * x) = b * P x) ∧ (∀ x b, P (x * φ b) = P x * b) := by
  have hleft (b : B) (x : A) : P (φ b * x) = b * P x := by
    have hs : (Submodule.span ℂ {e : B | IsStarProjection e} : Set B) ⊆
        {b | P (φ b * x) = b * P x} := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem e he => exact tomiyama_map_projection_mul φ P hP hfix e he x
      | zero =>
        change P (φ 0 * x) = 0 * P x
        simp only [map_zero, zero_mul]
      | add a b ha hb hia hib =>
        change P (φ a * x) = a * P x at hia
        change P (φ b * x) = b * P x at hib
        change P (φ (a + b) * x) = (a + b) * P x
        simp only [map_add, add_mul, hia, hib]
      | smul c a ha hia =>
        change P (φ a * x) = a * P x at hia
        change P (φ (c • a) * x) = (c • a) * P x
        simp only [map_smul, smul_mul_assoc, hia]
    have hc : IsClosed {b : B | P (φ b * x) = b * P x} :=
      isClosed_eq (P.continuous.comp ((map_continuous φ).mul_const x))
        (continuous_id.mul_const (P x))
    have hb : b ∈ closure (Submodule.span ℂ {e : B | IsStarProjection e} : Set B) := by
      rw [← Submodule.topologicalClosure_coe, hdense]
      trivial
    exact (closure_minimal hs hc) hb
  refine ⟨hleft, fun x b => ?_⟩
  have hstar := unital_contraction_map_star P hP
    (by simpa only [map_one] using hfix 1)
  have h := congrArg star (hleft (star b) (star x))
  simpa only [← hstar, star_mul, star_star, ← map_star] using h

end

end KadisonKastler

end OAI
