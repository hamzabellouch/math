import OAI.Combinatorics.Progressions.Dynamics.MarkedNativeFreezingBudget
import OAI.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

def NativeMarkedFactorizationAt
    {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (w : σ → ℕ)
    (m : ℕ) (T : σ → ℝ) (A : ℝ)
    (g : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  ∃ (e middle r : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (q : (D.filtration.gradedRefiltration U).realification.PolynomialOrbit w),
    e * middle * r = g ∧
    D.filtration.realPolynomialGroupMap G φ hφ w e = EF ∧
    D.filtration.realPolynomialGroupMap G φ hφ w r = RF ∧
    D.filtration.realPolynomialGroupMap G φ hφ w middle =
      EF⁻¹ * D.filtration.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
    D.filtration.PolynomialSlowBound D.basis w T A e ∧
    D.filtration.PolynomialRationalGrid D.basis w m r ∧
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra U).incl)).toLinearMap q.log =
        (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
    ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
      (hnil := (D.filtration.gradedRefiltration U).lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra U).incl
      ((D.filtration.gradedRefiltration U).realification.polynomialOrbitRealEval w t q) =
        D.filtration.adaptedPolynomialRealValueHom w t middle

theorem exists_controlled_native_marked_freezing (s a u : ℕ) :
    ∃ C Cfreeze : ℕ, 2 ≤ C ∧ 2 ≤ Cfreeze ∧
    ∀ {σ κ ξ μ L M : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [Fintype ξ] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (G : NilpotentLieFiltration M s)
      (c : Basis κ ℚ M) (ω : Fin d → ℕ)
      (hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : μ → D.filtration.AssociatedGraded),
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hDlayers) ω U.toSubmodule →
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
    ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card ξ : ℝ) ≤ p →
      (Fintype.card μ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (c.repr ⁅c i, c j⁆ k) ≤ p) →
      (∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ p) →
      (∀ k i, rationalLogHeight (c.repr (φ (D.basis i)) k) ≤ p) →
      (∀ j i, rationalLogHeight
        ((D.filtration.associatedGradedBasis D.basis ω hDlayers).repr (v j) i) ≤ p) →
    ∃ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ D.filtration.layer j),
      Function.RightInverse S φ ∧
      (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
        (rationalKernelHeight (Fintype.card κ) ⌈Real.exp ((p + C) ^ C)⌉₊)) ∧
    ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      D.MarkedAffineSliceFreezing G c φ hφ w S hS m T
        (Real.exp (((p + C) ^ C + 2) ^ 1)) (Real.exp (-(((p + C) ^ C + 2) ^ u)))
        (Real.exp (((p + C) ^ C + Cfreeze) ^ Cfreeze)) ∧
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      G.PolynomialRationalGrid c w l RF →
    ∃ EF' RF' : (G.realification.adaptedPolynomialFiltration w).Group,
      G.realPolynomialSymbolHom c τ hG w EF' = G.realPolynomialSymbolHom c τ hG w EF ∧
      G.realPolynomialSymbolHom c τ hG w RF' = G.realPolynomialSymbolHom c τ hG w RF ∧
      G.PolynomialSlowBound c w T (Real.exp (((p + C) ^ C + 2) ^ 1)) EF' ∧
      G.PolynomialRationalGrid c w m RF' ∧
    ∀ (g : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
      D.filtration.realPolynomialGroupMap G φ hφ w g = X →
    ∀ E P R : D.filtration.RealPolynomialSymbolGroup w,
      E * P * R = D.filtration.realPolynomialSymbolHom D.basis ω hDlayers w g →
      P.coord ∈ realificationLieSubalgebra
        (D.filtration.symbolPointwiseSubalgebra D.basis ω hDlayers w U) →
      D.filtration.SymbolSlowBound D.basis ω hDlayers w T (Real.exp ((p + 2) ^ a)) E →
      D.filtration.SymbolRationalGrid D.basis ω hDlayers w l R →
      ((D.filtration.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
        G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (D.filtration.associatedGradedMap G φ hφ))) →
      (G.realPolynomialSymbolHom c τ hG w RF *
        (D.filtration.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (D.filtration.associatedGradedMap G φ hφ))) →
      D.NativeMarkedFactorizationAt G φ hφ U w m T
        (Real.exp (((p + C) ^ C + 2) ^ 1)) g EF' RF' := by
  obtain ⟨Cf, C₀, C₁, _, _, _, hnative⟩ := exists_controlled_full_marked_native_factorizations s a
  obtain ⟨C, hC, hbudget⟩ := exists_markedNativeFreezingBudget s a Cf C₀ C₁
  obtain ⟨Cfreeze, hCfreeze, hfreeze⟩ := exists_uniform_marked_affine_slice_freezing s 1 u
  refine ⟨C, Cfreeze, hC, hCfreeze, ?_⟩
  intro σ κ ξ μ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d D G c ω hDlayers τ hG φ hφ hsurj
    w hw bk U v hU hvspan p hp hD hκ hξ hμ hσ hc hkernel hentries hv
  obtain ⟨hpq, hnativeq, htargetq⟩ := hbudget p hp
  let q : ℝ := (p + C) ^ C
  have hp1 : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hp_le : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hpq' : p ≤ q := hp_le.trans hpq
  have hq : 0 ≤ q := hp.trans hpq'
  obtain ⟨S, hS, hright, hSb, hfreezing⟩ := hfreeze D G c ω hDlayers τ hG φ hφ hsurj
    w hw q hq (GeometryComplexityLE.mono D hD hpq') (hσ.trans hpq') (hκ.trans hpq')
    (fun i j => (hentries i j).trans hpq')
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp
  let H := ⌈Real.exp p⌉₊
  have hdim : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans hp_le
  obtain ⟨m, hm, hmp, hlm, hfactor⟩ := hnative D.filtration G φ hφ D.basis ω hDlayers c τ hG
    w hw hsurj bk U v hU hvspan H l (p + 1) (one_le_ceil_exp p) hl hp1
    hdim (hκ.trans hp_le) (hξ.trans hp_le) (hμ.trans hp_le) (hσ.trans hp_le)
    (ceil_exp_le_exp_add_one hp) (hlp.trans (Real.exp_le_exp.mpr hp_le))
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun i j => rationalHeightLE_ceil_exp (hkernel i j))
    (fun i j => rationalHeightLE_ceil_exp (hentries i j))
    (fun j i => rationalHeightLE_ceil_exp (hv j i))
  have hmq : (m : ℝ) ≤ Real.exp q := hmp.trans (Real.exp_le_exp.mpr hnativeq)
  refine ⟨m, hm, hmq, hlm, ?_⟩
  intro T hT
  refine ⟨hfreezing m hm hmq T hT, ?_⟩
  intro X EF RF hEF hRF
  have hscale : Real.exp ((p + 2) ^ a) ≤ Real.exp ((p + 1 + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (add_nonneg hp (by norm_num))
      (add_le_add hp_le (le_refl 2)) a)
  obtain ⟨z, zrat, EF', RF', _, _, _, _, hESym, hRSym, hEFslow, hRFgrid, hlift⟩ :=
    hfactor T hT X EF RF (G.polynomialSlowBound_mono c w T hT hscale EF hEF) hRF
  have htargetcap : Real.exp ((fullMarkedNativeInput s a Cf (p + 1) + C₀) ^ C₀) ≤
      Real.exp ((q + 2) ^ 1) := Real.exp_le_exp.mpr (by
    simpa only [pow_one] using htargetq.trans (le_add_of_nonneg_right (by norm_num)))
  refine ⟨EF', RF', hESym, hRSym, G.polynomialSlowBound_mono c w T hT
    htargetcap EF' hEFslow, hRFgrid, ?_⟩
  intro g hg E P R hprod hP hEslow hRgrid hleft hright
  obtain ⟨e, middle, r, qnative, hprod', heF, hrF, hpF, heslow, hrgrid, hlog, hvalues⟩ :=
    hlift g hg E P R hprod hP
      (D.filtration.symbolSlowBound_mono D.basis ω hDlayers w T hT hscale E hEslow)
      hRgrid hleft hright
  have hnativecap : Real.exp ((markedNativeLiftInput
      (fixedMarkedNativeInput 1 C₀ (fullMarkedNativeInput s a Cf (p + 1))) + C₁) ^ C₁) ≤
      Real.exp ((q + 2) ^ 1) := Real.exp_le_exp.mpr (by
    simpa only [pow_one] using hnativeq.trans (le_add_of_nonneg_right (by norm_num)))
  exact ⟨e, middle, r, qnative, hprod', heF, hrF, hpF.trans (by rw [hg]),
    D.filtration.polynomialSlowBound_mono D.basis w T hT hnativecap e heslow,
    hrgrid, hlog, hvalues⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
