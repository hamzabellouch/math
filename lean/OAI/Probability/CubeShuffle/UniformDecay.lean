import OAI.Probability.CubeShuffle.SchattenBounds

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

lemma finite_positive_lower_bound {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ f i := by
  have hs (s : Finset ι) : ∃ a : ℝ, 0 < a ∧ ∀ i ∈ s, a ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, h⟩ := ih
      refine ⟨min a (f i), lt_min ha (hf i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h j hj)
  obtain ⟨a, ha, hs⟩ := hs Finset.univ
  exact ⟨a, ha, fun i => hs i (Finset.mem_univ i)⟩

lemma uniformOperator_zero_of_dimension_gt_one {G V : Type*} [Group G]
    [Fintype G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (hdim : 1 < Module.finrank ℂ V) :
    uniformOperator ρ = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  change uniformOperator ρ v = 0
  let u := uniformOperator ρ v
  have hfixed (g : G) : ρ g u = u :=
    congrArg (fun A : V →L[ℂ] V => A v) (uniformOperator_left ρ g)
  let T : Representation.IntertwiningMap (Representation.trivial ℂ G ℂ) ρ :=
    { toLinearMap := LinearMap.toSpanSingleton ℂ V u
      isIntertwining' g := by
        apply LinearMap.ext
        intro z
        change z • u = ρ g (z • u)
        rw [map_smul, hfixed] }
  rcases Representation.IsIrreducible.surjective_or_eq_zero T with hs | hz
  · have hd := LinearMap.finrank_le_finrank_of_surjective (f := T.toLinearMap) hs
    simp only [Module.finrank_self] at hd
    omega
  · have he := congrArg (fun S : Representation.IntertwiningMap
        (Representation.trivial ℂ G ℂ) ρ => S 1) hz
    simpa [T] using he

lemma dimension_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0 = μ.card) :
    dimension μ = 1 := by
  let := tabloid_subsingleton_of_full_row μ hμ
  have h := (space μ).finrank_le
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hcard : Fintype.card (Tabloid μ) ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun _ _ => Subsingleton.elim _ _)
  have he : Module.finrank ℂ (space μ) = 1 := by
    have := Specht.dimension_pos μ
    omega
  simp [dimension, he]

def localExponent (d : ℕ) (μ : Shapes (2^d)) : ℝ :=
  (1 - blockGap d) / (Real.log (dimension μ.1) + 1)

lemma localExponent_pos (d : ℕ) (μ : Shapes (2^d)) : 0 < localExponent d μ := by
  unfold localExponent
  exact div_pos (sub_pos.mpr (blockGap_lt_one d))
    (by have := log_dimension_nonneg μ.1; linarith)

lemma palindrome_local_bound (d : ℕ) (μ : Shapes (2^d)) :
    ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (palindromePerm d)‖ ≤
      Real.exp (-localExponent d μ * Real.log (dimension μ.1)) := by
  let : NormedAddCommGroup (hilbertSpace μ.1) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ.1) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ.1) := inferInstance
  by_cases hdim : dimension μ.1 = 1
  · rw [hdim, Real.log_one, mul_zero, Real.exp_zero]
    exact sampleOperator_norm_le _ (cardRepresentation_unitary d μ) _
  have hgt : 1 < dimension μ.1 :=
    lt_of_le_of_ne (dimension_one_le μ.1) (Ne.symm hdim)
  have hgt' : 1 < Module.finrank ℂ (hilbertSpace μ.1) := by
    rw [finrank_hilbertSpace]
    change 1 < (Module.finrank ℂ (space μ.1) : ℝ) at hgt
    exact_mod_cast hgt
  have hz := uniformOperator_zero_of_dimension_gt_one (V := hilbertSpace μ.1)
    (cardRepresentation d μ) hgt'
  have hgap := palindrome_off_invariants_gap d (V := hilbertSpace μ.1) (cardRepresentation d μ)
    (cardRepresentation_unitary d μ)
  rw [hz, sub_zero, ← sampleOperator_weighted] at hgap
  have he : localExponent d μ * (Real.log (dimension μ.1) + 1) = 1 - blockGap d := by
    exact div_mul_cancel₀ _ (ne_of_gt (by have := log_dimension_nonneg μ.1; linarith))
  have hnum : blockGap d - 1 ≤ -localExponent d μ * Real.log (dimension μ.1) := by
    have := localExponent_pos d μ
    nlinarith
  have hexp : blockGap d ≤ Real.exp (blockGap d - 1) := by
    simpa using Real.add_one_le_exp (blockGap d - 1)
  exact hgap.trans (hexp.trans (Real.exp_le_exp.mpr hnum))

theorem uniform_palindrome_dimension_decay :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ d : ℕ, 1 ≤ d → ∀ μ : Shapes (2^d),
      ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (palindromePerm d)‖ ≤
        Real.exp (-a * Real.log (dimension μ.1)) := by
  obtain ⟨a₀, h, ha₀, hh, hevent⟩ := spectral_regimes
  obtain ⟨d₀, hlarge⟩ := Filter.eventually_atTop.mp hevent
  let ι := (d : Fin d₀) × Shapes (2^d.1)
  obtain ⟨a₁, ha₁, hsmall⟩ := finite_positive_lower_bound
    (fun i : ι => localExponent i.1.1 i.2) (fun i => localExponent_pos _ _)
  let a := min 1 (min a₀ a₁)
  have ha : 0 < a := lt_min zero_lt_one (lt_min ha₀ ha₁)
  have ha₀' : a ≤ a₀ := (min_le_right _ _).trans (min_le_left _ _)
  have ha₁' : a ≤ a₁ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a, ha, min_le_left _ _, ?_⟩
  intro d hd μ
  by_cases hdim : dimension μ.1 = 1
  · rw [hdim, Real.log_one, mul_zero, Real.exp_zero]
    exact sampleOperator_norm_le _ (cardRepresentation_unitary d μ) _
  by_cases hd₀ : d₀ ≤ d
  · by_cases hc : (μ.1.card : ℝ) / 2 < μ.1.colLen 0
    · have hz := palindrome_tall_zero_general d (by omega) μ.1 (cardLabels d μ) hc
      change sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)
        (palindromePerm d) = 0 at hz
      rw [hz, norm_zero (E := (hilbertSpace μ.1 →L[ℂ] hilbertSpace μ.1))]
      exact (Real.exp_pos _).le
    · have hj : 0 < μ.1.card - μ.1.rowLen 0 := by
        by_contra hn
        have hrow : μ.1.rowLen 0 = μ.1.card := by
          have := rowLen_zero_le_card μ.1
          omega
        exact hdim (dimension_full_row μ.1 hrow)
      have hspec := (hlarge d hd₀ μ.1 (cardLabels d μ) hj (not_lt.mp hc)).1
      apply hspec.trans (Real.exp_le_exp.mpr ?_)
      have hmul := mul_le_mul_of_nonneg_right ha₀' (log_dimension_nonneg μ.1)
      simpa only [neg_mul, dimension] using neg_le_neg hmul
  · have hbase := palindrome_local_bound d μ
    apply hbase.trans (Real.exp_le_exp.mpr ?_)
    have hs := ha₁'.trans (hsmall ⟨⟨d, by omega⟩, μ⟩)
    have hmul := mul_le_mul_of_nonneg_right hs (log_dimension_nonneg μ.1)
    nlinarith

theorem uniform_sweep_dimension_decay :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ d : ℕ, 1 ≤ d → ∀ μ : Shapes (2^d),
      ‖fourierSweep d μ‖ ≤ dimension μ.1 ^ (-b) := by
  obtain ⟨a, ha, ha1, h⟩ := uniform_palindrome_dimension_decay
  refine ⟨a / 2, by positivity, by linarith, ?_⟩
  intro d hd μ
  have hs := h d hd μ
  rw [← physical_palindrome_norm d _ (cardRepresentation_unitary d μ)] at hs
  have he : (Real.exp (-a * Real.log (dimension μ.1) / 2)) ^ 2 =
      Real.exp (-a * Real.log (dimension μ.1)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnorm : ‖fourierSweep d μ‖ ≤ Real.exp (-a * Real.log (dimension μ.1) / 2) := by
    apply le_of_sq_le_sq ?_ (Real.exp_pos _).le
    exact hs.trans_eq he.symm
  convert hnorm using 1
  rw [Real.rpow_def_of_pos (dimension_pos μ.1)]
  congr 1
  ring

end CubeShuffle.WeightedSweep

end

end OAI
