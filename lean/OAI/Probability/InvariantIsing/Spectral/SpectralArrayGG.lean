import OAI.Probability.IsingPerceptron.JointGGClosure

namespace OAI

/-! Multivariate monomial GG closure for the finite vector of spectral overlaps. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace InvariantIsing

abbrev SpectralEntry (m : ℕ) := Fin m → Set.Icc (-1 : ℝ) 1
abbrev SpectralArray (m : ℕ) := (ℕ × ℕ) → SpectralEntry m
abbrev SpectralBlock (m n : ℕ) := Fin n → Fin n → SpectralEntry m

def spectralEntryMonomial {m : ℕ} (d : Fin m → ℕ) (x : SpectralEntry m) : ℝ :=
  ∏ a, (x a : ℝ) ^ d a

lemma continuous_spectralEntryMonomial {m : ℕ} (d : Fin m → ℕ) :
    Continuous (spectralEntryMonomial d) := by
  exact continuous_finsetProd _ fun a _ => ((continuous_apply a).subtype_val).pow _

def spectralBlockView (m n : ℕ) (x : SpectralArray m) : SpectralBlock m n :=
  fun i j => x (i, j)

def spectralBlockLink (m n i j : ℕ) (x : SpectralArray m) : SpectralBlock m n × SpectralEntry m :=
  (spectralBlockView m n x, x (i, j))

lemma continuous_spectralBlockView (m n : ℕ) : Continuous (spectralBlockView m n) := by
  unfold spectralBlockView
  fun_prop

lemma continuous_spectralBlockLink (m n i j : ℕ) : Continuous (spectralBlockLink m n i j) :=
  (continuous_spectralBlockView m n).prodMk (continuous_apply _)

private def spectralBlockPairCoordinate (m n : ℕ)
    (i : ((Fin n × Fin n) × Fin m) ⊕ Fin m)
    (x : SpectralBlock m n × SpectralEntry m) : ℝ :=
  match i with
  | Sum.inl i => x.1 i.1.1 i.1.2 i.2
  | Sum.inr i => x.2 i

private lemma continuous_spectralBlockPairCoordinate (m n : ℕ)
    (i : ((Fin n × Fin n) × Fin m) ⊕ Fin m) :
    Continuous (spectralBlockPairCoordinate m n i) := by
  cases i <;> unfold spectralBlockPairCoordinate <;> fun_prop

private lemma spectralBlockPairCoordinate_ext (m n : ℕ)
    (x y : SpectralBlock m n × SpectralEntry m)
    (h : ∀ i, spectralBlockPairCoordinate m n i x = spectralBlockPairCoordinate m n i y) : x = y := by
  apply Prod.ext
  · funext i j a
    exact Subtype.ext (h (.inl ((i, j), a)))
  · funext a
    exact Subtype.ext (h (.inr a))

/-- Polynomial moments in the new link, with arbitrary continuous tests
of the old block, determine its full joint law. -/
theorem spectralBlock_pair_monomials_unique (m n : ℕ)
    (P Q : Measure (SpectralBlock m n × SpectralEntry m)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (∫ x, D x.1 * spectralEntryMonomial d x.2 ∂P) =
        ∫ x, D x.1 * spectralEntryMonomial d x.2 ∂Q) : P = Q := by
  classical
  have : TopologicalSpace.SeparableSpace (SpectralBlock m n × SpectralEntry m) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (SpectralBlock m n × SpectralEntry m) := inferInstance
  let I := ((Fin n × Fin n) × Fin m) ⊕ Fin m
  let g : I → ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨spectralBlockPairCoordinate m n i, continuous_spectralBlockPairCoordinate m n i⟩
  let ev : MvPolynomial I ℝ →ₐ[ℝ] ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) :=
    MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : I) (x : SpectralBlock m n × SpectralEntry m) :
      g i x = spectralBlockPairCoordinate m n i x := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i : I, spectralBlockPairCoordinate m n i x ≠
        spectralBlockPairCoordinate m n i y := by
      by_contra! hno
      exact hxy (spectralBlockPairCoordinate_ext m n x y hno)
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using hi
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    let D : SpectralBlock m n → ℝ := fun b =>
      ∏ i : (Fin n × Fin n) × Fin m, (b i.1.1 i.1.2 i.2 : ℝ) ^ k (.inl i)
    have hD : Continuous D := by
      apply continuous_finsetProd
      intro i _
      exact (by fun_prop : Continuous (fun b : SpectralBlock m n => (b i.1.1 i.1.2 i.2 : ℝ))).pow _
    have he (x : SpectralBlock m n × SpectralEntry m) :
        ev (MvPolynomial.monomial k c) x = c * (D x.1 * spectralEntryMonomial (fun a => k (.inr a)) x.2) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [Finsupp.prod_pow]
      simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply,
        BoundedContinuousFunction.coe_prod, BoundedContinuousFunction.coe_pow,
        BoundedContinuousFunction.algebraMap_apply, Finset.prod_apply, Pi.pow_apply, smul_eq_mul, mul_one]
      change c * (∏ i : I, g i x ^ k i) = _
      rw [Fintype.prod_sum_type]
      rfl
    change (∫ x, ev (MvPolynomial.monomial k c) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k c) x ∂Q
    simp only [he, integral_const_mul]
    exact congrArg (c * ·) (h D hD _)

theorem spectral_monomial_measure_identity (m : ℕ) (μ : Measure (SpectralArray m))
    [IsProbabilityMeasure μ] (n : ℕ) (i : Fin n)
    (h : ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) =
        (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ) :
    (n : ℝ≥0∞) • μ.map (spectralBlockLink m n i n) =
      (μ.map (spectralBlockView m n)).prod (μ.map (fun x => x (0, 1))) +
        ∑ j ∈ Finset.univ.erase i, μ.map (spectralBlockLink m n i j) := by
  classical
  let block := μ.map (spectralBlockView m n)
  let pair := μ.map (fun x => x (0, 1))
  let link := fun j : ℕ => μ.map (spectralBlockLink m n i j)
  have : IsProbabilityMeasure block := (Measure.isProbabilityMeasure_map_iff
    (continuous_spectralBlockView m n).measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure pair := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply (0, 1)).aemeasurable).mpr inferInstance
  have (j : ℕ) : IsProbabilityMeasure (link j) := (Measure.isProbabilityMeasure_map_iff
    (continuous_spectralBlockLink m n i j).measurable.aemeasurable).mpr inferInstance
  change (n : ℝ≥0∞) • link n = block.prod pair + ∑ j ∈ Finset.univ.erase i, link j
  have : IsFiniteMeasure ((n : ℝ≥0∞) • link n) := (link n).smul_finite (by simp)
  apply spectralBlock_pair_monomials_unique m n
  intro D hD d
  let F : SpectralBlock m n × SpectralEntry m → ℝ := fun x => D x.1 * spectralEntryMonomial d x.2
  have hF : Continuous F := (hD.comp continuous_fst).mul
    ((continuous_spectralEntryMonomial d).comp continuous_snd)
  have hi (j : ℕ) : (∫ x, F x ∂link j) =
      ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ :=
    integral_map (continuous_spectralBlockLink m n i j).measurable.aemeasurable hF.aestronglyMeasurable
  change (∫ x, F x ∂(n : ℝ≥0∞) • link n) = ∫ x, F x ∂(block.prod pair + ∑ j ∈ Finset.univ.erase i, link j)
  rw [integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul,
    integral_add_measure (compact_integrable hF) (compact_integrable hF),
    integral_finsetSum_measure (fun j _ => compact_integrable hF), hi]
  simp_rw [hi]
  rw [h D hD d]
  congr 1
  have hp := continuous_spectralEntryMonomial d
  have he : (∫ x, F x ∂block.prod pair) =
      (∫ b, D b ∂block) * (∫ x, spectralEntryMonomial d x ∂pair) :=
    integral_prod_mul D (spectralEntryMonomial d)
  rw [he, integral_map (continuous_spectralBlockView m n).measurable.aemeasurable hD.aestronglyMeasurable,
    integral_map (measurable_pi_apply (0, 1)).aemeasurable hp.aestronglyMeasurable]

theorem spectral_monomialGG_measurable (m : ℕ) (μ : Measure (SpectralArray m)) [IsProbabilityMeasure μ]
    (h : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) =
        (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) μ := by
  classical
  intro n hn i A hA t ht
  have he := congrArg (fun ν : Measure (SpectralBlock m n × SpectralEntry m) => (ν (A ×ˢ t)).toReal)
    (spectral_monomial_measure_identity m μ n i (h n hn i))
  have hmap : ∀ j : ℕ, Measurable (spectralBlockLink m n i j) := fun j =>
    (continuous_spectralBlockLink m n i j).measurable
  have hblock := (continuous_spectralBlockView m n).measurable
  have hpair : Measurable (fun x : SpectralArray m => x (0, 1)) := measurable_pi_apply _
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    Measure.add_apply, Measure.prod_prod, Measure.finsetSum_apply,
    Measure.map_apply (hmap _) (hA.prod ht), Measure.map_apply hblock hA, Measure.map_apply hpair ht] at he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at he
  change (n : ℝ) * μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, n) ∈ t}) =
    μ.real {x | spectralBlockView m n x ∈ A} * μ.real {x | x (0, 1) ∈ t} +
    ∑ j ∈ Finset.univ.erase i, μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, j) ∈ t}) at he
  change μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, n) ∈ t}) =
    (μ.real {x | spectralBlockView m n x ∈ A} * μ.real {x | x (0, 1) ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, j) ∈ t})) / n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]
  nlinarith [he]

def spectralMonomialResidual {m : ℕ} (μ : Measure (SpectralArray m)) (n : ℕ) (i : Fin n)
    (D : SpectralBlock m n → ℝ) (d : Fin m → ℕ) : ℝ :=
  (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) -
    (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) -
    ∑ j ∈ Finset.univ.erase i,
      ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ

lemma spectralMonomialResidual_zero {m : ℕ} (μ : Measure (SpectralArray m)) [IsProbabilityMeasure μ]
    (n : ℕ) (i : Fin n) (D : SpectralBlock m n → ℝ) :
    spectralMonomialResidual μ n i D 0 = 0 := by
  classical
  have hn : 1 ≤ n := by have hi := i.isLt; omega
  simp only [spectralMonomialResidual, spectralEntryMonomial, Pi.zero_apply, pow_zero,
    Finset.prod_const_one, mul_one, integral_const, probReal_univ, one_smul,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
  ring

lemma spectralMonomialResidual_weak_limit {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {μ : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 μ))
    (n : ℕ) (i : Fin n) (D : SpectralBlock m n → ℝ) (hD : Continuous D) (d : Fin m → ℕ) :
    Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop
      (𝓝 (spectralMonomialResidual μ n i D d)) := by
  have hI : ∀ F : SpectralArray m → ℝ, Continuous F →
      Tendsto (fun N => ∫ x, F x ∂(L N : Measure (SpectralArray m))) atTop
        (𝓝 (∫ x, F x ∂(μ : Measure (SpectralArray m)))) := by
    intro F hF
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hcD := hD.comp (continuous_spectralBlockView m n)
  have ht (j : ℕ) := hI (fun x => D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)))
    (hcD.mul ((continuous_spectralEntryMonomial d).comp (continuous_apply _)))
  exact (((ht n).const_mul (n : ℝ)).sub ((hI _ hcD).mul
    (hI _ ((continuous_spectralEntryMonomial d).comp (continuous_apply _))))).sub
      (tendsto_finsetSum _ fun j _ => ht j)

/-- Vanishing monomial residuals imply the Ghirlanda–Guerra identities
for the weak limit of the spectral overlap arrays. -/
theorem spectralGG_of_weak_monomial_residuals {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {μ : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (μ : Measure (SpectralArray m)) := by
  apply spectral_monomialGG_measurable
  intro n hn i D hD d
  have he := tendsto_nhds_unique (spectralMonomialResidual_weak_limit hL n i D hD d)
    (hg n hn i D hD d)
  dsimp only [spectralMonomialResidual] at he
  linarith

theorem spectralGG_of_weak_nonconstant_monomial_residuals {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray m)} {μ : ProbabilityMeasure (SpectralArray m)}
    (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D →
      ∀ d : Fin m → ℕ, d ≠ 0 →
        Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (μ : Measure (SpectralArray m)) := by
  apply spectralGG_of_weak_monomial_residuals hL
  intro n hn i D hD d
  by_cases hd : d = 0
  · subst d
    simpa only [spectralMonomialResidual_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact hg n hn i D hD d hd

end InvariantIsing

end

end OAI
