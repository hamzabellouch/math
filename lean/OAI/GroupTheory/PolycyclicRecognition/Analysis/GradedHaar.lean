import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePreservingLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasisDynkinHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinTranslations
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GradedGeneratorLimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateTopology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MappedBasisBrackets
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling

namespace OAI

/-! # Haar measure for the actual graded coordinate group -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Topology Manifold

theorem measurePreserving_graded_dynkin_right_of_rescaled
    {L G : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hmeasure : ∀ r q, MeasurePreserving
      (fun x => dynkinProduct a (basisBracket (exponentialRescaleBasis b cost r)) x q)
      volume volume) (q : Fin n → ℝ) :
    MeasurePreserving (fun x => dynkinProduct a (gradedCoordinateBracket b cost) x q)
      volume volume := by
  let B := fun r => basisBracket (exponentialRescaleBasis b cost r)
  let B₀ := gradedCoordinateBracket b cost
  let hg := gradedCoordinateBracket_groupLaws b cost hweight Exp hinj hzero hneg hadd a hm
  let hgr := fun r => basis_polynomialGroupLaws
    (exponentialRescaleBasis b cost r) Exp hinj hzero hneg hadd a hm
  have hB : Tendsto (fun k : ℕ => B k) atTop (𝓝 B₀) :=
    (basisBracket_rescale_tendsto b cost hweight).comp tendsto_natCast_atTop_atTop
  have hlim (x y : Fin n → ℝ) :
      Tendsto (fun k : ℕ => dynkinProduct a (B k) x y) atTop
        (𝓝 (dynkinProduct a B₀ x y)) := by
    exact ((continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
      continuous_id continuous_const continuous_const).tendsto B₀).comp hB
  exact measurePreserving_homeomorph_limit volume (dynkinRightTranslation a B₀ hg q)
    (fun k => dynkinRightTranslation a (B k) (hgr k) q)
    (fun k => hmeasure k q) (fun x => hlim x q) (fun x => hlim x (-q))

/-- The published exponential-Haar input gives the finite-scale invariance;
the limiting invariance follows from the actual rescaled brackets. -/
theorem measurePreserving_model_graded_dynkin_right
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent L) {n c : ℕ} (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (q : Fin n → ℝ) :
    MeasurePreserving (fun x => dynkinProduct a (gradedCoordinateBracket b cost) x q)
      volume volume := by
  have hnilG := e.nilpotent_iff_equiv_nilpotent.mp hnil
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnilG
  have hinj : Function.Injective Exp := by
    have he : Exp = chart := funext fun x => (hchart x).symm
    rw [he]
    exact chart.injective
  apply measurePreserving_graded_dynkin_right_of_rescaled b cost hweight
    (Exp ∘ e) (hinj.comp e.injective) (by simpa using hExp.map_zero)
    (fun x => by simpa using hExp.map_neg (e x))
    (fun x s t => by simpa using hExp.map_add_smul (e x) s t) a
    (model_binary_dynkin e Exp a hm) ?_ q
  intro r z
  have hp := measurePreserving_basis_dynkin_right haar Exp hExp hnilG
    ((exponentialRescaleBasis b cost r).map e.toLinearEquiv) a hm z
  simpa only [basisBracket_map_lieEquiv] using hp

/-- Lebesgue measure in polynomial exponential coordinates is Haar once
right translations preserve it. Inversion is coordinate negation. -/
theorem polynomialCoordinate_haar_of_right_translations
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasureSpace V] [BorelSpace V]
    [(volume : Measure V).IsAddHaarMeasure]
    (m : V → V → V) (h : PolynomialGroupLaws m)
    (hc : Continuous (fun p : V × V => m p.1 p.2))
    (hm : ∀ q, MeasurePreserving (fun x => m x q) volume volume) :
    let e := PolynomialCoordinateGroup.expHomeomorph m h
    let μ := Measure.map e volume
    μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  let G := PolynomialCoordinateGroup m h
  let e := PolynomialCoordinateGroup.expHomeomorph m h
  let μ := Measure.map e volume
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup m h hc
  have hp : MeasurePreserving e volume μ := ⟨e.continuous.measurable, rfl⟩
  have hr : μ.IsMulRightInvariant := by
    constructor
    intro q
    have he : (fun x : V => e (m x (e.symm q))) = (fun g : G => g * q) ∘ e := by
      funext x
      change m x (e.symm q) = m x q
      rfl
    have hh := hp.comp (hm (e.symm q))
    have hhmap := hh.map_eq
    change Measure.map (fun x => e (m x (e.symm q))) volume = μ at hhmap
    rw [he, ← Measure.map_map (measurable_mul_const q) e.continuous.measurable] at hhmap
    exact hhmap
  let : μ.IsMulRightInvariant := hr
  let : μ.IsInvInvariant := isInvInvariant_map_of_neg volume e e.continuous.measurable
    (fun _ => rfl)
  have hi : μ.inv = μ := Measure.inv_eq_self μ
  have hl : μ.IsMulLeftInvariant := by
    rw [← hi]
    infer_instance
  let : μ.IsMulLeftInvariant := hl
  let : IsFiniteMeasureOnCompacts μ := Measure.IsFiniteMeasureOnCompacts.map volume e
  let : μ.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  exact ⟨{}, hr⟩

end PolycyclicRecognition

end

end OAI
