import OAI.Probability.SwitchChain.SliceActualSynthesis
import OAI.Probability.SwitchChain.SliceGramProfile
import OAI.Probability.SwitchChain.SliceSynthesisBounds

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem exists_nonzero_linear_coeff (hN : 3 ≤ Fintype.card V) :
    ∃ u : V → ℝ, (∑ i, u i) = 0 ∧ ofMatrix (linearPair u) ≠ 0 := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i,j,hij⟩ := exists_pair_ne V
  let u : V → ℝ := Pi.single i 1 - Pi.single j 1
  have hu : ∑ k, u k = 0 := by simp [u, Finset.sum_sub_distrib]
  have hui : u i = 1 := by simp [u, hij]
  refine ⟨u, hu, ?_⟩
  intro hc
  have hz : rowSum (linearPair u) i = 0 := by
    unfold rowSum
    apply Finset.sum_eq_zero
    intro k _
    have hh := congrArg (fun c : Coeff V => c (i,k)) hc
    simpa only [ofMatrix_apply, PiLp.zero_apply] using hh
  rw [linearPair_rowSum u hu, hui, mul_one] at hz
  have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  linarith

 theorem linear_orbit_scalar_eq (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (b d : ℝ)
    (hgram : ∀ i j : V, i ≠ j → ∀ k l : V, k ≠ l →
      2 * ⟪column q i j, column q k l⟫ = orbitKernel 1 b d i j k l) :
    1 + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d =
      SliceImageNorm.linearGramScalar (α := V) q := by
  obtain ⟨u,hu,hc⟩ := exists_nonzero_linear_coeff (V := V) hN
  have hg := gram_linear_of_orbit_entries (column q) 1 b d
    (column_diag q) hgram u hu
  have hn := synthesis_linear_norm_sq q hN hq0 hqN u hu
  have hi := (synthesis (column q)).adjoint_inner_right
    (ofMatrix (linearPair u)) (synthesis (column q) (ofMatrix (linearPair u)))
  rw [hg, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hi
  apply mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  linarith

 theorem rowZero_eq_zero_of_card_le_three (hN : Fintype.card V ≤ 3)
    (c : V → V → ℝ) (hrow : ∀ i, rowSum c i = 0)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0) : c = 0 := by
  funext i j
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · have hout : ∀ k ∈ outside i j, ∀ l ∈ outside i j, k = l := by
      intro k hk l hl
      by_contra hkl
      have hk' : k ≠ j ∧ k ≠ i := by simpa [outside] using hk
      have hl' : l ≠ j ∧ l ≠ i := by simpa [outside] using hl
      have hc := Finset.card_le_card (Finset.subset_univ ({i,j,k,l} : Finset V))
      have hfour : ({i,j,k,l} : Finset V).card = 4 := by
        simp [hij, hkl, Ne.symm hk'.1,
          Ne.symm hk'.2, Ne.symm hl'.1, Ne.symm hl'.2]
      rw [hfour, Finset.card_univ] at hc
      omega
    have hz : disjointSum c i j = 0 := by
      unfold disjointSum
      have hs : (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        apply Finset.sum_eq_zero
        intro l hl
        rw [hout k hk l hl]
        exact hdiag l
      rw [hs, zero_div]
    rw [rowZero_disjointSum c hsym hdiag hrow hij] at hz
    exact hz

 theorem column_eq_zero_of_boundary (q : ℕ) (hq : q ≤ Fintype.card V)
    (hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2) (i j : V) :
    column q i j = 0 := by
  by_cases hij : i = j
  · subst j; exact column_diag q i
  · have hr : raw q i j = 0 := by
      ext S
      change (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
      rw [ite_eq_right hij]
      exact SliceMoments.centeredEqual_eq_zero_of_boundary Finset.univ q
        (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
        (by simpa using hb) S.val S.property
    simp [column, hr]

 theorem operator_comparison_nontrivial (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  obtain ⟨b,d,hgram⟩ := SliceGramProfile.exists_normalized_orbit_entries
    (V := V) q hqN.le hp hp1
  let μ₁ : ℝ := 1 + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d
  let μ₂ : ℝ := if 4 ≤ Fintype.card V then 1-2*b+d else 0
  have hμ₁ : μ₁ = SliceImageNorm.linearGramScalar (α := V) q :=
    linear_orbit_scalar_eq q hN hq0 hqN b d hgram
  have hμ₁pos : 0 ≤ μ₁ := by
    rw [hμ₁]
    unfold SliceImageNorm.linearGramScalar
    have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    apply div_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hp.le
  have hb₁ : μ₁ ≤ (Fintype.card V : ℝ)/2 := by
    rw [hμ₁]
    exact SliceImageNorm.linearGramScalar_le hN q hq0 hqN
  have hb₂ : μ₂ ≤ (Fintype.card V : ℝ)-1 := by
    dsimp only [μ₂]
    split_ifs with h4
    · exact degree_two_bound_of_orbit_entries h4 (column q) b d
        (column_diag q) (column_total q (by omega)) hgram hμ₁pos
    · have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
      linarith
  refine Analytic.gram_comparison_of_two_blocks_without_signs
    (E := Space V q) (F := Coeff V) (synthesis (column q)) (SliceEuclideanGenerator.generator q)
    (SliceEuclideanGenerator.generator_symmetric q)
    (SliceEuclideanGenerator.generator_positive q) μ₁ μ₂
    ((Fintype.card V : ℝ)/2) ((Fintype.card V : ℝ)-1) hb₁ hb₂ ?_ f
  intro c
  obtain ⟨u,v,hu,hvrow,hvsym,hvdiag,hdec,horth⟩ :=
    exists_synthesis_decomposition hN (column q) (column_symmetric q)
      (column_diag q) (column_total q (by omega)) c
  refine ⟨ofMatrix (linearPair u),ofMatrix v,hdec,horth,?_,?_,?_,?_⟩
  · exact gram_linear_of_orbit_entries (column q) 1 b d (column_diag q) hgram u hu
  · by_cases h4 : 4 ≤ Fintype.card V
    · simpa only [μ₂, ite_eq_left h4] using gram_rowZero_of_orbit_entries
        (column q) 1 b d (column_diag q) hgram v hvsym hvdiag hvrow
    · have hv := rowZero_eq_zero_of_card_le_three (by omega) v hvrow hvsym hvdiag
      subst v
      simp [ofMatrix, synthesis, μ₂, h4]
  · exact generator_synthesis_linear q u hu
  · exact generator_synthesis_rowZero q v hvrow hvsym hvdiag

 theorem operator_comparison (q : ℕ) (hq : q ≤ Fintype.card V) (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · have hz : synthesis (column (V := V) q) = 0 := by
      ext c S
      simp [synthesis, column_eq_zero_of_boundary q hq hb]
    rw [hz]
    simpa using SliceEuclideanGenerator.generator_positive q f
  · apply operator_comparison_nontrivial
    · omega
    · omega
    · omega

end Problem315.SliceNormalized

end

end OAI
