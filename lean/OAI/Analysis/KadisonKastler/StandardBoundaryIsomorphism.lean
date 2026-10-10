import OAI.Analysis.KadisonKastler.ProductBoundaryIntertwiner
import OAI.Analysis.KadisonKastler.AEBoundaryDiagonal
import OAI.Analysis.KadisonKastler.StandardTraceInvariants

namespace OAI

/-! # Removing the boundary variables in common standard position

The product intertwiner, trace-diagonal comparison and double ergodicity
give an actual near-identity star isomorphism. The scalar invariant-vector
condition and the right-action identities are proved from standard position.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u v w

variable {H : Type u} {G : Type v} {D : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [Group G] [Countable G]
  [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace D]
  {μ : Measure D} [IsProbabilityMeasure μ] {M N : VonNeumannAlgebra H}

/-- A close algebra-valued measurable cocycle yields a nearby star
isomorphism, with constant `18δ`. -/
theorem exists_standard_starEquiv_of_boundary_cocycle
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (hΩ : pM.vector = pN.vector)
    (α : NonsingularAction G D μ) (m₂ : ScalarBoundaryMean α.prod)
    (hTom : PublishedFieldTomiyama (G := G × G) (H := H) (μ := μ.prod μ))
    (herg : UnitaryDoubleErgodic.{v, w, u} α)
    (U : G →* unitary (Algebra M))
    (hU : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ g, traceTwoNorm pM.trace ((u : Algebra M) - U g) < ε)
    (W : G → D → unitary (Algebra N))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : Algebra N).val ξ) μ)
    (hc : ∀ g t, ∀ᵐ x ∂μ, (W (g * t) x : Algebra N) =
      (W g x : Algebra N) * W t (α.toPerm g⁻¹ x))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hclose : ∀ g, ∀ᵐ x ∂μ,
      ‖(W g x : Algebra N).val - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) -
      (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ)
    (hproduct : 2 * δ + 2 * κ < 1) (hdiag : 2 * δ < 1)
    (hsmall : 3 * (18 * δ) + (18 * δ) ^ 2 < 2)
    (hgap : kkDistance M N + 18 * δ < 1) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤ 18 * δ * ‖x‖ := by
  let W₀ : G → D → unitary (H →L[ℂ] H) :=
    fun g x => ambientAlgebraUnitary (W g x)
  have hc₀ (g t : G) : ∀ᵐ x ∂μ,
      (W₀ g x : H →L[ℂ] H) * W₀ t (α.toPerm g⁻¹ x) = W₀ (g * t) x := by
    filter_upwards [hc g t] with x hx
    exact congrArg Subtype.val hx.symm
  obtain ⟨L, hLm, hLn, hL⟩ := exists_product_boundary_intertwiner pM pN α m₂ hTom U W₀
    hW (fun g => Filter.Eventually.of_forall fun x => (W g x : Algebra N).property)
    hc₀ hδ hκ hproduct hclose hJ
  obtain ⟨aN, ham, han, hac⟩ := pN.exists_ae_diagonal_unitary_comparison α W hc hW
    (fun g => ambientAlgebraUnitary (U g)) hδ hdiag hclose
  let a : D × D → unitary (H →L[ℂ] H) :=
    fun x => ambientAlgebraUnitary (aN x.1 x.2)
  let R : G → D → unitary (H →L[ℂ] H) := fun g x =>
    conjugationUnitary pN.conjugation pN.conjugation_involutive (W₀ g x)
  have hLdiag (g : G) : ∀ᵐ x ∂μ.prod μ,
      (L x : H →L[ℂ] H) * pM.diagonalRepresentation U g =
        ((W₀ g x.1 : H →L[ℂ] H) * R g x.2) * L (α.diagonal.toPerm g⁻¹ x) :=
    hL (g, g)
  have hR (g : G) : ∀ᵐ x ∂μ.prod μ,
      (R g x.2 : H →L[ℂ] H) * a (α.diagonal.toPerm g⁻¹ x) =
        (a (α.diagonal.toPerm g⁻¹ x) : H →L[ℂ] H) * R g x.2 := by
    apply Filter.Eventually.of_forall
    intro x
    exact (pN.commute_conjugationOperator
      (a (α.diagonal.toPerm g⁻¹ x)) (W₀ g x.2)
      (aN _ _ : Algebra N).property (W g x.2 : Algebra N).property).eq.symm
  have hRΩ (g : G) : ∀ᵐ x ∂μ.prod μ,
      (R g x.2 : H →L[ℂ] H) pM.vector = star (W₀ g x.2 : H →L[ℂ] H) pM.vector := by
    apply Filter.Eventually.of_forall
    intro x
    change pN.conjugation ((W g x.2 : Algebra N).val (pN.conjugation pM.vector)) = _
    rw [hΩ, pN.conjugation_vector]
    exact pN.conjugation_algebraVector (W g x.2)
  have han₀ (x : D × D) : ‖(a x : H →L[ℂ] H) - 1‖ ≤ 4 * δ := han x.1 x.2
  have hnear : ∀ᵐ x ∂μ.prod μ,
      ‖star (L x : H →L[ℂ] H) * (a x : H →L[ℂ] H) - 1‖ ≤
        (4 * δ + 4 * κ) + 4 * δ := by
    filter_upwards [hLn] with x hx
    have ht := norm_unitary_mul_sub_one_le (star (L x)) (a x)
    have hstar : ‖((star (L x) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
        ‖(L x : H →L[ℂ] H) - 1‖ := by
      simpa only [Unitary.coe_star, star_sub, star_one] using
        norm_star ((L x : H →L[ℂ] H) - 1)
    rw [hstar] at ht
    exact ht.trans (add_le_add hx (han₀ x))
  obtain ⟨z, hz, hzn, hzvec⟩ := exists_boundary_scalar_from_comparison α herg
    (pM.diagonalRepresentation U) pM.vector pM.vector_norm
    (pM.scalar_of_diagonal_invariant U (traceHilbert_factor hM) hU)
    L a W₀ R
    (operator_adjoint_eval_aestronglyMeasurable _ hLm)
    (ham pM.vector) hLdiag
    (fun g => (hac g).mono fun x hx => congrArg Subtype.val hx)
    hR hRΩ hnear
  have hWone : ∀ᵐ x ∂μ, (W₀ 1 x : H →L[ℂ] H) = 1 := by
    filter_upwards [hc₀ 1 1] with x hx
    simp only [one_mul, inv_one, α.one_apply] at hx
    apply (Unitary.toUnits (W₀ 1 x)).isUnit.mul_left_cancel
    simpa only [Unitary.val_toUnits_apply, mul_one] using hx
  have hLleft (g : G) : ∀ᵐ x ∂μ.prod μ,
      (L x : H →L[ℂ] H) * ambientAlgebraUnitary (U g) =
        (W₀ g x.1 : H →L[ℂ] H) * L (α.toPerm g⁻¹ x.1, x.2) := by
    filter_upwards [hL (g, 1), (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hWone]
      with x hx hone
    change (L x : H →L[ℂ] H) * (U g : Algebra M).val =
      (W₀ g x.1 : H →L[ℂ] H) * L (α.toPerm g⁻¹ x.1, x.2)
    simpa only [productBoundaryRepresentation_coe, Prod.fst, Prod.snd, map_one,
      OneMemClass.coe_one, productBoundaryValue_coe, hone,
      conjugationOperator_one pM.conjugation pM.conjugation_involutive,
      conjugationOperator_one pN.conjugation pN.conjugation_involutive,
      mul_one, Prod.inv_mk, inv_one, NonsingularAction.prod_apply, Equiv.Perm.one_apply,
      α.one_apply] using hx
  have hnsmall : 3 * (2 * (2 * (4 * δ) + δ)) + (2 * (2 * (4 * δ) + δ)) ^ 2 < 2 := by
    nlinarith only [hsmall]
  obtain ⟨θ, hθ⟩ := exists_starEquiv_of_boundary_normalization hM hN
    pM.trace pN.trace pM.finiteVectorTrace pN.finiteVectorTrace pM.vector
    pM.vectorMap_norm (by simpa only [hΩ] using pN.vectorMap_norm)
    U hU α L a W₀
    (fun x => (aN x.1 x.2 : Algebra N).property)
    (fun g x => (W g x : Algebra N).property)
    z hz hzvec hLleft (by positivity) hzn hLn
    (Filter.Eventually.of_forall han₀)
    (fun g => (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hclose g))
    hnsmall (by nlinarith only [hgap])
  refine ⟨θ, fun x => ?_⟩
  convert hθ x using 1; ring

end

end KadisonKastler

end OAI
