import OAI.Analysis.CircleDomains.Sobolev.BoundedUpperIntegral
import OAI.Analysis.CircleDomains.Selection.FiniteConvexSplit
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace OAI

/-! A finite mixture uniformly controls all compact test configurations if every
probability distribution on configurations admits a good candidate. This is the
finite splitting step of the manuscript's fusion argument. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def probabilityConvexCombination {T : Type*} [MeasurableSpace T]
    (μ ν : ProbabilityMeasure T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ProbabilityMeasure T :=
  ⟨ENNReal.ofReal a • (μ : Measure T) + ENNReal.ofReal b • (ν : Measure T), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]⟩

theorem integral_probabilityConvexCombination {T : Type*} [MeasurableSpace T]
    (μ ν : ProbabilityMeasure T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {f : T → ℝ}
    (hμ : Integrable f (μ : Measure T)) (hν : Integrable f (ν : Measure T)) :
    ∫ t, f t ∂(probabilityConvexCombination μ ν a b ha hb hab : Measure T) =
      a * (∫ t, f t ∂(μ : Measure T)) + b * ∫ t, f t ∂(ν : Measure T) := by
  change ∫ t, f t ∂(ENNReal.ofReal a • (μ : Measure T) +
    ENNReal.ofReal b • (ν : Measure T)) = _
  rw [integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hν.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul]

theorem convex_integral_vectors {I T : Type*} [MeasurableSpace T]
    (f : I → T → ℝ) (hf : ∀ i (μ : ProbabilityMeasure T), Integrable (f i) (μ : Measure T)) :
    Convex ℝ (Set.range (fun μ : ProbabilityMeasure T => fun i => ∫ t, f i t ∂(μ : Measure T))) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  refine ⟨probabilityConvexCombination μ ν a b ha hb hab, ?_⟩
  funext i
  exact integral_probabilityConvexCombination μ ν a b ha hb hab (hf i μ) (hf i ν)

theorem exists_finite_compact_law_split
    {T Z : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (f : Z → T → ℝ) (A : Set Z)
    (hf : ∀ z ∈ A, UpperSemicontinuous (f z))
    (hf0 : ∀ z ∈ A, ∀ t, 0 ≤ f z t)
    {M : ℝ} (hM : 0 < M) (hfM : ∀ z ∈ A, ∀ t, f z t ≤ M)
    {b ε : ℝ} (hε : 0 < ε)
    (htest : ∀ μ : ProbabilityMeasure T, ∃ z ∈ A, ∫ t, f z t ∂(μ : Measure T) ≤ b) :
    ∃ (n : ℕ) (z : Fin n → Z) (w : Fin n → ℝ),
      (∀ i, z i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ t, ∑ i, w i * f (z i) t ≤ b + ε := by
  classical
  let U : A → Set (ProbabilityMeasure T) := fun z =>
    {μ | (∫ t, f z.val t ∂(μ : Measure T)) < b + ε}
  have hU (z : A) : IsOpen (U z) :=
    (upperSemicontinuous_integral_bounded (hf z.val z.property)
      (hf0 z.val z.property) hM (hfM z.val z.property)).isOpen_preimage _
  have hcover : (univ : Set (ProbabilityMeasure T)) ⊆ ⋃ z : A, U z := by
    intro μ _
    obtain ⟨z, hz, hzt⟩ := htest μ
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, lt_of_le_of_lt hzt (by linarith)⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hFne : F.Nonempty := by
    by_contra h
    have hm := hF (mem_univ (diracProba (Classical.arbitrary T)))
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hm
  let I := {z : A // z ∈ F}
  let : Fintype I := inferInstanceAs (Fintype F)
  let : Nonempty I := ⟨⟨hFne.choose, hFne.choose_spec⟩⟩
  let g : I → T → ℝ := fun i => f i.val.val
  have hg (i : I) (μ : ProbabilityMeasure T) : Integrable (g i) (μ : Measure T) := by
    apply Integrable.of_bound (hf i.val.val i.val.property).measurable.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _ i.val.property t)]
      exact hfM _ i.val.property t
  let V : Set (I → ℝ) := Set.range (fun μ : ProbabilityMeasure T =>
    fun i => ∫ t, g i t ∂(μ : Measure T))
  have hV : Convex ℝ V := convex_integral_vectors g hg
  have hVne : V.Nonempty := ⟨_, Set.mem_range_self (diracProba (Classical.arbitrary T))⟩
  have hmiss : ∀ v ∈ V, ∃ i, v i ≤ b + ε := by
    rintro v ⟨μ, rfl⟩
    obtain ⟨z, hz, hzμ⟩ := mem_iUnion₂.mp (hF (mem_univ μ))
    exact ⟨⟨z, hz⟩, le_of_lt hzμ⟩
  obtain ⟨w, hw, hw1, hwV⟩ := finite_nonnegative_separator hV hVne (b + ε) hmiss
  have hpoints (t : T) : ∑ i, w i * f i.val.val t ≤ b + ε := by
    have h := hwV _ (Set.mem_range_self (diracProba t))
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (integral_dirac' (g i) t (hf i.val.val i.val.property).measurable.stronglyMeasurable).symm
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i => (e i).val.val, fun i => w (e i),
    fun i => (e i).val.property, fun i => hw (e i), ?_, ?_⟩
  · exact (e.sum_comp w).trans hw1
  · intro t
    exact (e.sum_comp (fun i => w i * f i.val.val t)).le.trans (hpoints t)

end CircleDomainRigidity

end

end OAI
