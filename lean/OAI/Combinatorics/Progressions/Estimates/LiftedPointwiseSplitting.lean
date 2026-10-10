import OAI.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_lifted_pointwise_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ F.AssociatedGraded) (v : η → κ → F.AssociatedGraded),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω (U j).toSubmodule) →
      ∀ (Γ : Subgroup F.Group) (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ →
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid l →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ j i k, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j i) k) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, ∀ t : σ → ℝ,
        eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (P j).coord) ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
        (q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra (⨅ j, U j))),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ C)) e₀ ∧
        F.PolynomialRationalGrid b w m r₀ ∧
        (F.realGradedRefiltration (⨅ j, U j)).Adapted w q ∧
        VectorPolynomial.map (F.realGradedRefiltrationSubalgebra (⨅ j, U j)).incl.toLinearMap q = p₀.coord ∧
        coefficients q 0 = 0 ∧
        (∀ t : σ → ℝ, F.realification.polynomialOrbitRealEval w t
          (F.realification.adaptedBCHToOrbit w p₀) ∈
            NilpotentLieBCHGroup.realificationSubgroup (hnil := F.lowerCentralSeries_eq_bot)
              (F.gradedRefiltrationSubalgebra (⨅ j, U j))) := by
  obtain ⟨N, _, hnormalize⟩ := exists_bounded_polynomial_normalization s
  obtain ⟨S, hS, hsplit⟩ := exists_pointwise_refiltered_splitting s a
  let A := max S ((N + 1) * N)
  obtain ⟨B, _, hslow⟩ := exists_polynomial_slow_product_bound s A 2
  obtain ⟨D, _, hrat⟩ := exists_polynomial_rational_product_bound s 2
  let C := 2 + S + (B + 1) * B + (S + 2) * ((D + 1) * D)
  have hSC : S ≤ C := by dsimp [C]; omega
  have hBC : (B + 1) * B ≤ C := by dsimp [C]; omega
  have hDC : (S + 2) * ((D + 1) * D) ≤ C := by dsimp [C]; omega
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ _ _ _ F b ω hlayers w hw U v hspan hgraded Γ H l p hH hl hp
    hι hσ hκ hη hHp hlp hinner houter hb hv T hT g E P R hX hP hE hR
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith only [hp]
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTS : ∀ i, Real.exp ((p + 2) ^ S) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase hSC)).trans (hT i)
  obtain ⟨c, γ, g₀, hc, hγ, hnorm, hg0, hsymbol⟩ :=
    hnormalize F b ω hlayers w Γ l H p hl hinner hb hp hι hHp hlp g
  obtain ⟨m₀, e, mid, r, q, hm₀, hm₀p, hlm₀, hfactor, hq, hqmap, hq0, hvalues, he, hr, _, _⟩ :=
    hsplit F b ω hlayers w hw U v hspan hgraded H l p hH hl hp hι hσ hκ hη hHp hlp hb hv
      T hTS g₀ hg0 E P R (fun j => (hX j).trans hsymbol.symm) hP hE hR
  let left := F.realification.adaptedConstantGroupHom w c * e
  let right := r * F.realification.adaptedConstantGroupHom w γ
  have hleftinput : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ A))
      (F.realification.adaptedConstantGroupHom w c) := by
    apply F.polynomialSlowBound_constant b w T hTpos (Real.exp_nonneg _)
    intro i
    exact (hc i).trans (Real.exp_le_exp.mpr
      ((shifted_self_power_le_base_power hp N).trans
        (pow_le_pow_right₀ hbase (le_max_right _ _))))
  have heinput : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ A)) e :=
    F.polynomialSlowBound_mono b w T hTpos
      (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))) e he
  have hleft : F.PolynomialSlowBound b w T (Real.exp ((p + B) ^ B)) left := by
    have h := hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hTpos
      [F.realification.adaptedConstantGroupHom w c, e] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hleftinput
        · exact heinput)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using h
  let p' := (p + 2) ^ S
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hpp' : p ≤ p' := le_power_budget hp (by omega)
  obtain ⟨m, hm, hmp, hm₀m, hprod⟩ := hrat F b ω hlayers w hw H p' hH hp'
    (hι.trans hpp') (hσ.trans hpp') (hHp.trans (Real.exp_le_exp.mpr hpp')) hb m₀ hm₀ hm₀p
  have hγgrid : (fun i => (b.baseChange ℝ).repr γ.coord i) ∈ realDenominatorGrid l :=
    NilpotentLieBCHGroup.realification_subgroup_grid b Γ l houter γ hγ
  have hrightinput : F.PolynomialRationalGrid b w m₀ (F.realification.adaptedConstantGroupHom w γ) :=
    F.polynomialRationalGrid_of_dvd b w hl hlm₀ _ (F.polynomialRationalGrid_constant b w l γ hγgrid)
  have hright : F.PolynomialRationalGrid b w m right := by
    have h := hprod [r, F.realification.adaptedConstantGroupHom w γ] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hr
      · exact hrightinput)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using h
  have hcost : (p' + D) ^ D ≤ (p + 2) ^ C :=
    ((shifted_self_power_le_base_power hp' D).trans
      (shifted_power_budget_le hp S ((D + 1) * D))).trans (pow_le_pow_right₀ hbase hDC)
  refine ⟨m, left, mid, right, q, hm, hmp.trans (Real.exp_le_exp.mpr hcost), hlm₀.trans hm₀m,
    ?_, ?_, hright, hq, hqmap, hq0, hvalues⟩
  · calc
      left * mid * right = F.realification.adaptedConstantGroupHom w c * (e * mid * r) *
          F.realification.adaptedConstantGroupHom w γ := by simp only [left, right, mul_assoc]
      _ = g := by rw [hfactor]; exact hnorm
  · exact F.polynomialSlowBound_mono b w T hTpos
      (Real.exp_le_exp.mpr ((shifted_self_power_le_base_power hp B).trans
        (pow_le_pow_right₀ hbase hBC))) left hleft

end Erdos3.NilpotentLieFiltration

end

end OAI
