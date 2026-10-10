import OAI.Combinatorics.Progressions.Estimates.SymbolCommonCorrections
import OAI.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

theorem exists_pointwise_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ F.AssociatedGraded) (v : κ → F.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j) i) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w P.coord) ∈
        realificationLieSubalgebra U) →
      (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w P'.coord) ∈
        realificationLieSubalgebra U) →
      E * P * R = E' * P' * R' →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (E⁻¹ * E').coord) ∈
        realificationLieSubalgebra U) ∧
      (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (R' * R⁻¹).coord) ∈
        realificationLieSubalgebra U) := by
  obtain ⟨K, hK, hcompare⟩ := exists_controlled_symbol_comparison s a
  let C := max 2 (((s + 4) * (s + 3) + 2) * ((K + 1) * K))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan hgraded H l p hH hl hp
    hι hσ hκ hHp hlp hb hv T hT E P R E' P' R' hP hP' heq hE hE' hR hR'
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hcount : (Fintype.card (SymbolBasisIndex w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × κ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hlayers))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hι hσ hκ)
  have hcost : (q + K) ^ K ≤ (p + 2) ^ C := by
    apply (symbol_spanning_shifted_parameter_power_bound s K hp).trans
    apply pow_le_pow_right₀ (by linarith only [hp] : 1 ≤ p + 2)
    exact le_max_right _ _
  have hTq : ∀ i, Real.exp ((q + K) ^ K) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hcost).trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hslow : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a)
  obtain ⟨hA, hD⟩ := hcompare F b ω hlayers w hw
    (F.symbolPointwiseSubalgebra b ω hlayers w U) (F.pointwiseSymbolSpanningFamily b ω hlayers w v)
    (F.pointwiseSymbolSpanningFamily_span b ω hlayers w U hgraded v hspan)
    H l q hH hl hq (hι.trans hpq) (hσ.trans hpq) hcount
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hb
    (F.pointwiseSymbolSpanningFamily_height b ω hlayers w v hH hv) T hTq E P R E' P' R'
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w U P.coord).mpr hP)
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w U P'.coord).mpr hP') heq
    (F.symbolSlowBound_mono b ω hlayers w T hTpos hslow E hE)
    (F.symbolSlowBound_mono b ω hlayers w T hTpos hslow E' hE') hR hR'
  exact ⟨(F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w U _).mp hA,
    (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w U _).mp hD⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
