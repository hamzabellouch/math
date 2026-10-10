import OAI.Combinatorics.Progressions.Estimates.ReducedSquareSymbol

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (t : σ → ℚ)

noncomputable def adaptedGradedEvaluation : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.AssociatedGraded where
  toFun p := eval t (F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolMap w p))
  map_add' p q := by simp only [map_add]
  map_smul' c p := by simp only [map_smul, RingHom.id_apply]
  map_lie' {p q} := by
    change eval t (F.gradedSymbolPolynomialLie b ω hlayers w (F.polynomialSymbolMap w ⁅p, q⁆)) =
      ⁅eval t (F.gradedSymbolPolynomialLie b ω hlayers w (F.polynomialSymbolMap w p)),
        eval t (F.gradedSymbolPolynomialLie b ω hlayers w (F.polynomialSymbolMap w q))⁆
    rw [LieHom.map_lie, LieHom.map_lie]
    exact (evalLie t).map_lie _ _

theorem adaptedGradedEvaluation_apply (p : F.adaptedLieSubalgebra w) :
    F.adaptedGradedEvaluation b ω hlayers w t p =
      eval t (F.shiftedGradedPolynomial b ω hlayers w 0 p.val) := by
  rw [F.shiftedGradedPolynomial_zero]
  rfl

noncomputable def adaptedShiftedGradedEvaluation (k : ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] F.AssociatedGraded where
  toFun p := eval t (F.shiftedGradedPolynomial b ω hlayers w k p.val)
  map_add' p q := by
    change eval t (F.shiftedGradedPolynomial b ω hlayers w k (p.val + q.val)) = _
    rw [map_add, map_add]
  map_smul' c p := by
    change eval t (F.shiftedGradedPolynomial b ω hlayers w k (c • p.val)) = _
    rw [map_smul, map_smul, RingHom.id_apply]

@[simp] theorem adaptedShiftedGradedEvaluation_apply (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    F.adaptedShiftedGradedEvaluation b ω hlayers w t k p =
      eval t (F.shiftedGradedPolynomial b ω hlayers w k p.val) := rfl

theorem adaptedShiftedGradedEvaluation_lie (p q : F.adaptedLieSubalgebra w)
    (hq : q ∈ F.shiftedPolynomialIdeal w 1) :
    F.adaptedShiftedGradedEvaluation b ω hlayers w t 1 ⁅p, q⁆ =
      ⁅F.adaptedGradedEvaluation b ω hlayers w t p,
        F.adaptedShiftedGradedEvaluation b ω hlayers w t 1 q⁆ := by
  have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  have hq' : q.val ∈ F.shiftedAdaptedSubmodule w 1 := hq
  have he := F.shiftedGradedPolynomial_lie b ω hlayers w (i := 0) (j := 1)
    (p := p.val) (q := q.val) hp hq'
  rw [F.adaptedGradedEvaluation_apply, F.adaptedShiftedGradedEvaluation_apply,
    F.adaptedShiftedGradedEvaluation_apply]
  rw [LieSubalgebra.coe_bracket, he]
  exact (evalLie t).map_lie
    (F.shiftedGradedPolynomial b ω hlayers w 0 p.val)
    (F.shiftedGradedPolynomial b ω hlayers w 1 q.val)

@[simp] theorem adaptedShiftedGradedEvaluation_constant (k : ℕ) (x : L) :
    F.adaptedShiftedGradedEvaluation b ω hlayers w t k (F.adaptedConstant w x) =
      F.gradedPieceProjection b ω hlayers k x := by
  rw [F.adaptedShiftedGradedEvaluation_apply]
  change eval t (F.shiftedGradedPolynomial b ω hlayers w k (monomial 0 x)) = _
  rw [F.shiftedGradedPolynomial_monomial, eval_monomial, map_zero, Nat.zero_add,
    Finsupp.prod_zero_index, one_smul]

variable [Fintype σ] (h : σ → ℚ)

theorem adaptedGradedJet_evaluation (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualLinearLift (F.adaptedGradedEvaluation b ω hlayers (fun _ => 1) t)
        (F.adaptedShiftedGradedEvaluation b ω hlayers (fun _ => 1) t 1)
        (F.adaptedPolynomialJet h p).coord =
      dualEvalLie t h (F.gradedSymbolPolynomial b ω hlayers (fun _ => 1)
        (F.polynomialSymbolMap (fun _ => 1) p)) := by
  apply dual_ext
  · rw [dualLinearLift_base, F.adaptedPolynomialJet_base, dualEvalLie_base]
    rw [F.adaptedGradedEvaluation_apply, F.shiftedGradedPolynomial_zero]
  · rw [dualLinearLift_tangent, F.adaptedPolynomialJet_tangent, dualEvalLie_tangent]
    rw [F.adaptedShiftedGradedEvaluation_apply, F.adaptedDirectionalDerivative_coe]
    change eval t (F.shiftedGradedPolynomial b ω hlayers (fun _ => 1) 1
      (directionalDerivative h p.val)) = _
    rw [← F.shiftedGradedPolynomial_zero b ω hlayers (fun _ => 1) p,
      ← F.shiftedGradedPolynomial_directionalDerivative b ω hlayers h 0 p.val]

theorem shiftedGradedEvaluation_logDerivative (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftedGradedEvaluation b ω hlayers (fun _ => 1) t 1 (F.adaptedLogDerivative h p) =
      polynomialLogDerivative (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot) t h
        (⟨F.gradedSymbolPolynomial b ω hlayers (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)⟩ :
          PolynomialGroup σ F.associatedGradedFiltration.lowerCentralSeries_eq_bot) := by
  have hz : dualTangentLinear (F.adaptedPolynomialJet h p).coord ∈
      F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 := by
    rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h p
  dsimp only [adaptedLogDerivative, polynomialLogDerivative]
  have he := dualLinearLift_logDerivative_eq
    (hL := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot)
    F.associatedGradedFiltration.lowerCentralSeries_eq_bot
    (F.shiftedPolynomialIdeal (fun _ : σ => 1) 1)
    (F.adaptedGradedEvaluation b ω hlayers (fun _ => 1) t)
    (F.adaptedShiftedGradedEvaluation b ω hlayers (fun _ => 1) t 1)
    (F.adaptedShiftedGradedEvaluation_lie b ω hlayers (fun _ => 1) t) (F.adaptedPolynomialJet h p) hz
    (polynomialFirstJetHom (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot) t h
      (⟨F.gradedSymbolPolynomial b ω hlayers (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)⟩ :
        PolynomialGroup σ F.associatedGradedFiltration.lowerCentralSeries_eq_bot))
    (by
      rw [polynomialFirstJetHom, map_coord]
      dsimp only
      convert F.adaptedGradedJet_evaluation b ω hlayers t h p using 1)
  convert he using 1

omit [Fintype σ] in
theorem shiftedGradedEvaluation_adjoint (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) (x : L) :
    F.adaptedShiftedGradedEvaluation b ω hlayers (fun _ => 1) t 1
        (dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
          (F.adaptedConstant (fun _ => 1) x)) =
      dualAdjoint (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot)
        (polynomialValueHom (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot) t
        (⟨F.gradedSymbolPolynomial b ω hlayers (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)⟩ :
          PolynomialGroup σ F.associatedGradedFiltration.lowerCentralSeries_eq_bot))
        (F.gradedPieceProjection b ω hlayers 1 x) := by
  apply dualLinearLift_adjoint_eq F.associatedGradedFiltration.lowerCentralSeries_eq_bot
    (F.shiftedPolynomialIdeal (fun _ : σ => 1) 1)
    (F.adaptedGradedEvaluation b ω hlayers (fun _ => 1) t)
    (F.adaptedShiftedGradedEvaluation b ω hlayers (fun _ => 1) t 1)
    (F.adaptedShiftedGradedEvaluation_lie b ω hlayers (fun _ => 1) t)
    (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) (F.adaptedConstant (fun _ => 1) x)
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) x)
  · simp only [polynomialValueHom, map_coord, evalLie_apply]
    rw [F.adaptedGradedEvaluation_apply, F.shiftedGradedPolynomial_zero]
  · exact F.adaptedShiftedGradedEvaluation_constant b ω hlayers (fun _ => 1) t 1 x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem shiftedGradedPolynomial_one_eq_of_firstJet_eq (w : σ → ℕ)
    {p q : F.adaptedLieSubalgebra w}
    (he : F.filteredFirstJetMap w p = F.filteredFirstJetMap w q) :
    F.shiftedGradedPolynomial b ω hlayers w 1 p.val =
      F.shiftedGradedPolynomial b ω hlayers w 1 q.val := by
  have hd : p.val - q.val ∈ F.shiftedAdaptedSubmodule w 2 :=
    (F.filteredFirstJetMap_eq_iff w p q).mp he
  have hd' : p.val - q.val ∈ F.shiftedAdaptedSubmodule w 1 :=
    F.shiftedAdaptedSubmodule_antitone w (by decide : 1 ≤ 2) hd
  rw [← sub_eq_zero, ← map_sub]
  exact (F.shiftedGradedPolynomial_eq_zero_iff b ω hlayers w 1 hd').mpr hd

theorem relativeSquareSymbol_eq_iff_shiftedGraded (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p q : F.normalizedRelativeSubmodule w) :
    F.relativeSquareSymbolMap w hw p = F.relativeSquareSymbolMap w hw q ↔
      F.shiftedGradedPolynomial b ω hlayers w 1 p.val.val =
        F.shiftedGradedPolynomial b ω hlayers w 1 q.val.val := by
  rw [F.relativeSquareSymbolMap_eq_iff]
  change F.filteredFirstJetMap w p.val = F.filteredFirstJetMap w q.val ↔ _
  constructor
  · exact F.shiftedGradedPolynomial_one_eq_of_firstJet_eq b ω hlayers w
  · intro he
    have hd : p.val.val - q.val.val ∈ F.shiftedAdaptedSubmodule w 1 :=
      (F.shiftedAdaptedSubmodule w 1).sub_mem p.property.1 q.property.1
    rw [← sub_eq_zero, ← map_sub] at he
    exact (F.filteredFirstJetMap_eq_iff w p.val q.val).mpr
      ((F.shiftedGradedPolynomial_eq_zero_iff b ω hlayers w 1 hd).mp he)

theorem graded_normalizedRelativeLog [Fintype σ] (t h : σ → ℚ) (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    eval t (F.shiftedGradedPolynomial b ω hlayers (fun _ => 1) 1
      (F.normalizedRelativeLog h e m p).val) =
      polynomialLogDerivative (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot) t h
        (⟨F.gradedSymbolPolynomial b ω hlayers (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)⟩ :
          PolynomialGroup σ F.associatedGradedFiltration.lowerCentralSeries_eq_bot) -
        F.gradedPieceProjection b ω hlayers 1 e -
        dualAdjoint (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot)
          (polynomialValueHom (hnil := F.associatedGradedFiltration.lowerCentralSeries_eq_bot) t
          (⟨F.gradedSymbolPolynomial b ω hlayers (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)⟩ :
            PolynomialGroup σ F.associatedGradedFiltration.lowerCentralSeries_eq_bot))
          (F.gradedPieceProjection b ω hlayers 1 m) := by
  have he := F.shiftedGradedPolynomial_one_eq_of_firstJet_eq b ω hlayers (fun _ => 1)
    (F.filteredFirstJet_normalizedRelativeLog h e m p)
  rw [he]
  rw [← F.adaptedShiftedGradedEvaluation_apply b ω hlayers (fun _ => 1) t 1
    (F.adaptedLogDerivative h p - F.adaptedConstant (fun _ => 1) e -
      dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (F.adaptedConstant (fun _ => 1) m))]
  rw [map_sub, map_sub, F.shiftedGradedEvaluation_logDerivative b ω hlayers t h p,
    F.adaptedShiftedGradedEvaluation_constant b ω hlayers (fun _ => 1) t 1 e,
    F.shiftedGradedEvaluation_adjoint b ω hlayers t p m]

end Erdos3.NilpotentLieFiltration

end

end OAI
