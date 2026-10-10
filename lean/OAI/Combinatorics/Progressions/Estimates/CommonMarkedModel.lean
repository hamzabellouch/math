import OAI.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
import OAI.Combinatorics.Progressions.Lattices.MarkedShiftLattice

namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_model_with_budget (t l : ℕ) (hl : 0 < l) {p : ℝ}
    (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
      ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
        ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
          M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
          M.ComplexityLE (markedShiftModelBudget s p) ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  have ha : a ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t :=
    F.associatedDegree.polynomialShift_finrank_le b ω hF hω t
  have hd : d ≤ a := (markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le
  have hi : finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ≤ d :=
    (markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_le
  let R := markedShiftInputBudget s p
  let Q := markedShiftHeightBudget s p
  have hpR : p ≤ R := le_markedShiftInputBudget s hp
  have hR : 0 ≤ R := markedShiftInputBudget_nonneg s hp
  have hRQ : R ≤ Q := markedShiftInputBudget_le_height s hp
  have hQS : Q ≤ markedShiftModelBudget s p := markedShiftHeightBudget_le_model s hp
  have haR : (a : ℝ) ≤ R := (Nat.cast_le.mpr ha).trans
    (markedShift_dimension_budget s (Fintype.card ι) t hp hn ht)
  have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr hd).trans haR
  obtain ⟨m, hm, q, hq, B, hB, hdiv, hbound, D, M, hMF, hgrid, hcoords, hcomplex⟩ :=
    exists_markedShiftQuotient_integral_model F b ω hF hω v w marked hw hv hH hc hgen t l hl
  have hmR : (m : ℝ) ≤ R := (Nat.cast_le.mpr (hm.trans hi)).trans hdR
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq).trans hdR
  have hheight : (markedQuotientHeight s (Fintype.card ι) a d m q H : ℝ) ≤ Real.exp Q :=
    markedQuotientHeight_le_exp s (Fintype.card ι) a d m q H hR
      (step_le_markedShiftInputBudget s hp) (hn.trans hpR) haR hdR hmR hqR
      (hHp.trans (Real.exp_le_exp.mpr hpR))
  have hgridS : (B : ℝ) ≤ Real.exp (markedShiftModelBudget s p) := by
    have hb := integral_grid_allowance_le_exp (bchIntegralDenominatorBound (s + 1)) q
      (markedQuotientHeight s (Fintype.card ι) a d m q H) l
      (hR.trans hRQ) (hqR.trans hRQ) hheight
      (hlp.trans (Real.exp_le_exp.mpr (hpR.trans hRQ)))
    exact (Nat.cast_le.mpr hbound).trans (hb.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hR.trans hRQ))))
  refine ⟨q, hq.trans (hd.trans ha), D, M, hMF,
    hcomplex _ (hqR.trans (hRQ.trans hQS)) hgridS
      (hheight.trans (Real.exp_le_exp.mpr hQS)), ?_, ?_⟩
  · rw [hgrid]
    exact hdiv
  · simpa only [hgrid] using hcoords

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_free_markedShift_model (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (marked : X → Bool) (t l : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p → (t : ℝ) ≤ p → 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ q : ℕ,
        ∃ D : RationalFilteredNilmanifold
          (MarkedShiftQuotient (FreeDegreeRankLieAlgebra.filtration X s r w hw hr)
            (FreeDegreeRankLieAlgebra.of X s r w hw) w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = markedShiftMultidegree (FreeDegreeRankLieAlgebra.filtration X s r w hw hr)
              (FreeDegreeRankLieAlgebra.of X s r w hw) w marked hw
              (FreeDegreeRankLieAlgebra.of_mem_layer X s r w hw hr) t ∧
            M.ComplexityLE ((p + C) ^ C) ∧ l ∣ D.grid ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid := by
  obtain ⟨a, _, hfree⟩ := exists_adapted_free_degree_rank_model s
  obtain ⟨b, _, hmodel⟩ := exists_markedShiftModel_budget s
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw marked t l p hp hX ht hl hlp
  let F := FreeDegreeRankLieAlgebra.filtration X s r w hw hr
  let g := FreeDegreeRankLieAlgebra.of X s r w hw
  let T := (p + a) ^ a
  let R := p + T + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hTR : T ≤ R := by dsimp [R]; linarith
  have hT1R : T + 1 ≤ R := by dsimp [R]; linarith
  have hR : 0 ≤ R := hp.trans hpR
  have hbound : (R + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, R, T, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨hdim, e, _, htail, hstructure, htree, _⟩ := hfree X r hr w hw p hp hX
  have htailOrdinary : ∀ i, ∃ c, F.associatedDegree.layer i = basisTail e c := by
    intro i
    obtain ⟨c, _, hc⟩ := htail i 0
    exact ⟨c, hc⟩
  obtain ⟨ω, hω⟩ := F.associatedDegree.exists_weights_of_tails e htailOrdinary
  have hωle := F.associatedDegree.adaptedBasis_weight_le_step e ω hω
  have hg (x : X) (i) : rationalLogHeight (e.repr (g x) i) ≤ T :=
    htree (FreeNilpotentLieAlgebra.of X s x)
      (FreeNilpotentLieAlgebra.of_mem_treeGenerators X s hs x) i
  have hnR : (Fintype.card (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) : ℝ) ≤ R := by
    simpa only [Fintype.card_fin] using hdim.trans hTR
  obtain ⟨q, _, D, M, hMF, hM, hdiv, hcoords⟩ :=
    exists_markedShift_model_with_budget F e ω hω hωle g w marked hw
      (FreeDegreeRankLieAlgebra.of_mem_layer X s r w hw hr) (one_le_ceil_exp T)
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun x i => rationalHeightLE_ceil_exp (hg x i)) t l hl hR hnR (ht.trans hpR)
      ((ceil_exp_le_exp_add_one hT).trans (Real.exp_le_exp.mpr hT1R))
      (hlp.trans (Real.exp_le_exp.mpr hpR))
  exact ⟨q, D, M, hMF, hM.mono M ((hmodel R hR).trans hbound), hdiv, hcoords⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_marked_common_model (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
      (A : ℝ) (t l : ℕ), 0 ≤ A → (W.dim : ℝ) ≤ A → (t : ℝ) ≤ A →
      0 < l → (l : ℝ) ≤ Real.exp A →
      ∃ d : ℕ,
        ∃ E : RationalFilteredNilmanifold
          (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
          ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = D.markedQuotientMultidegree t ∧
            M.ComplexityLE ((A + C) ^ C) ∧ l ∣ E.grid ∧
            bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid := by
  obtain ⟨c, _, hfree⟩ := exists_free_markedShift_model s hs
  let Q : Polynomial ℕ := Polynomial.C (2 * s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P W out H R D A t l hA hdim ht hl hlA
  let K := ((2 * s + 1 : ℕ) : ℝ) * A + 1
  have hcoef : (1 : ℝ) ≤ (2 * s + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * s + 1 by omega)
  have hAK : A ≤ K := by dsimp [K]; nlinarith
  have hK : 0 ≤ K := hA.trans hAK
  have hcard : (Fintype.card D.CoefficientAlphabet : ℝ) ≤ K := by
    calc
      _ ≤ (2 : ℝ) * s * W.dim := by exact_mod_cast D.coefficientAlphabet_card
      _ ≤ (2 : ℝ) * s * A := mul_le_mul_of_nonneg_left hdim (by positivity)
      _ ≤ K := by dsimp [K]; push_cast; nlinarith
  have hbound : (K + c) ^ c ≤ (A + C) ^ C := by
    simpa [Q, K, Polynomial.eval₂_pow] using hbudget A hA
  obtain ⟨d, E, M, hMF, hM, hdiv, hcoords⟩ := hfree D.CoefficientAlphabet r
    W.rank.filtration.rank_le_degree D.coefficientWeight D.coefficientWeight_pos
    D.coefficientIsDependent t l K hK hcard (ht.trans hAK) hl
    (hlA.trans (Real.exp_le_exp.mpr hAK))
  exact ⟨d, E, M, hMF, hM.mono M hbound, hdiv, hcoords⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
