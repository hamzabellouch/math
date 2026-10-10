import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
import OAI.Combinatorics.Progressions.Estimates.FullRestrictedGradeMajorMatching
import OAI.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_bounded_full_chart_grade_major_matching (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι Γ : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (v : Γ → F.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = fast)
      (H : ℕ) (_hHpos : 1 ≤ H)
      (_hv : ∀ i j, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H)
      (p₀ : ℝ) (_hp₀ : 0 ≤ p₀)
      (_hrows : (Fintype.card ι : ℝ) ≤ p₀) (_hcols : (Fintype.card Γ : ℝ) ≤ p₀)
      (_hH : (H : ℝ) ≤ Real.exp p₀)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast),
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
        ∃ (eQ : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ fast))
          (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded) (qS : ℕ),
          Function.RightInverse lift fast.mkQ ∧
          Function.RightInverse (lift.baseChange ℝ) (fast.mkQ.baseChange ℝ) ∧
          0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p₀ + 2) ^ 47) ∧
          (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p₀ + 2) ^ 45)) ∧
          (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
          (∀ j i, RationalHeightLE (((eQ.coord j).comp fast.mkQ)
            (F.associatedGradedBasis b ω hF i)) ⌈Real.exp ((p₀ + 2) ^ 7)⌉₊) ∧
      ∀ (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : Fin d → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : Fin d → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
            (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
              (fullTaggedVariableWeight J) fast k (left⁻¹ * Z * right⁻¹).coord))) β (R j).eval u‖) →
      FullChartDetectedMajorGradeConclusion (M := M) F b ω hF J k fast (eQ.baseChange ℝ) lift
        Z left right K₀ U poly c N ((p + C) ^ C) := by
  classical
  obtain ⟨C, hC, hmatching⟩ := exists_full_restricted_grade_major_matching m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι Γ _ _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast
    v hspan H hHpos hv p₀ hp₀ hrows hcols hH hfast
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates (F.associatedGradedBasis b ω hF)
      fast v hspan hHpos hv hp₀ hrows hcols hH
  refine ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord, ?_⟩
  intro Z left right K₀ hK₀ hlower periodCap coverCap Lip W D htk R N poly hpoly
    U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hstep := hmatching F b ω hF J fast (eQ.baseChange ℝ) lift hfast hsection
    Z left right K₀ hK₀ hlower W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank
    hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  exact fullChartDetectedMajorGradeConclusion_of_fullTagged F b ω hF J k fast
    (eQ.baseChange ℝ) lift Z left right K₀ U poly c N ((p + C) ^ C) hstep

theorem exists_bounded_full_chart_grade_major_family (m : ℕ) :
    ∃ C : ℕ → ℕ, (∀ n, 2 ≤ C n) ∧ ∀ {X L M ι Γ : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (v : Γ → F.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = fast)
      (H : ℕ) (_hHpos : 1 ≤ H)
      (_hv : ∀ i j, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H)
      (p₀ : ℝ) (_hp₀ : 0 ≤ p₀)
      (_hrows : (Fintype.card ι : ℝ) ≤ p₀) (_hcols : (Fintype.card Γ : ℝ) ≤ p₀)
      (_hH : (H : ℝ) ≤ Real.exp p₀)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast),
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
        ∃ (eQ : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ fast))
          (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded) (qS : ℕ),
          Function.RightInverse lift fast.mkQ ∧
          Function.RightInverse (lift.baseChange ℝ) (fast.mkQ.baseChange ℝ) ∧
          0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p₀ + 2) ^ 47) ∧
          (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p₀ + 2) ^ 45)) ∧
          (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
          (∀ j i, RationalHeightLE (((eQ.coord j).comp fast.mkQ)
            (F.associatedGradedBasis b ω hF i)) ⌈Real.exp ((p₀ + 2) ^ 7)⌉₊) ∧
      ∀ (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < (n + 1),
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : Fin d → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < (n + 1))
      (R : Fin d → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J (n + 1))))
      (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J (n + 1) poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C n) ^ C n) ≤ (N i : ℝ)) →
      Real.exp ((p + C n) ^ C n) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J (n + 1) poly Ψ c
          (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
            (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
              (fullTaggedVariableWeight J) fast (n + 1) (left⁻¹ * Z * right⁻¹).coord))) β (R j).eval u‖) →
      FullChartDetectedMajorGradeConclusion (M := M) F b ω hF J (n + 1) fast (eQ.baseChange ℝ) lift
        Z left right K₀ U poly c N ((p + C n) ^ C n) := by
  classical
  choose C hC hmatching using
    (fun n : ℕ => exists_full_restricted_grade_major_matching m (n + 1) (Nat.zero_lt_succ n))
  refine ⟨C, hC, ?_⟩
  intro X L M ι Γ _ _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast
    v hspan H hHpos hv p₀ hp₀ hrows hcols hH hfast
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates (F.associatedGradedBasis b ω hF)
      fast v hspan hHpos hv hp₀ hrows hcols hH
  refine ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord, ?_⟩
  intro n Z left right K₀ hK₀ hlower periodCap coverCap Lip W D htk R N poly hpoly
    U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hstep := hmatching n F b ω hF J fast (eQ.baseChange ℝ) lift hfast hsection
    Z left right K₀ hK₀ hlower W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank
    hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  exact fullChartDetectedMajorGradeConclusion_of_fullTagged F b ω hF J (n + 1) fast
    (eQ.baseChange ℝ) lift Z left right K₀ U poly c N ((p + C n) ^ C n) hstep

end Erdos3.NilpotentLieFiltration

end

end OAI
