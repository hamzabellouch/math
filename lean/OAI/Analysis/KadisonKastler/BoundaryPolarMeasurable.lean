import OAI.Analysis.KadisonKastler.BoundaryPolarTrace
import OAI.Analysis.KadisonKastler.BoundaryDiagonalMeasurable
import OAI.Analysis.KadisonKastler.TraceFieldMeasurable

namespace OAI

/-! # Measurability of the diagonal unitary polar field

The polar factor is a Lipschitz function of a near-identity operator in
its tracial Hilbert realization. Factoring through the range of the
measurable least field therefore supplies its measurability.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace Set

noncomputable section

section Polar

variable {B E P : Type*} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [SeparableSpace E] [MeasurableSpace P]
local instance boundaryPolarMeasurableOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryPolarMeasurableStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- A uniformly near-identity field has measurable unitary polar factors
whenever the original field is measurable in its tracial Hilbert space. -/
theorem aestronglyMeasurable_polar_trace
    (τ : FaithfulTracialState B) (J : B →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) {μ : Measure P}
    (c : P → B) (a : P → unitary B) {r : ℝ} (hr : r < 1)
    (hnear : ∀ p, ‖c p - 1‖ ≤ r)
    (hpolar : ∀ p, (a p : B) * CFC.abs (c p) = c p)
    (hmeas : AEStronglyMeasurable (fun p => J (c p)) μ) :
    AEStronglyMeasurable (fun p => J (a p : B)) μ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let K : ℝ := (1 - r)⁻¹
  have hK : 0 ≤ K := inv_nonneg.mpr (sub_pos.mpr hr).le
  have hpair (p q : P) : ‖J (a p : B) - J (a q : B)‖ ≤
      K * ‖J (c p) - J (c q)‖ := by
    simpa only [← map_sub, hJ] using
      polar_traceTwoNorm_le_inv_mul τ (c p) (c q) (a p) (a q)
        (hpolar p) (hpolar q) hr (hnear p) (hnear q)
  let S : Set E := Set.range (fun p => J (c p))
  have hrep (z : S) : ∃ p : P, J (c p) = z.val := z.property
  choose rep hrep using hrep
  let F : S → E := fun z => J (a (rep z) : B)
  have hF : LipschitzWith ⟨K, hK⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (F z) (F w) ≤ K * dist z w
    have h := hpair (rep z) (rep w)
    simpa only [F, hrep, Subtype.dist_eq, dist_eq_norm] using h
  let f : P → S := fun p => ⟨J (c p), Set.mem_range_self p⟩
  have hf : AEMeasurable f μ := hmeas.aemeasurable.subtype_mk
  have hFm : AEStronglyMeasurable (fun p => F (f p)) μ :=
    (hF.continuous.measurable.comp_aemeasurable hf).aestronglyMeasurable
  apply hFm.congr
  exact Filter.Eventually.of_forall fun p => by
    have h := hpair (rep (f p)) p
    rw [hrep] at h
    change ‖F (f p) - J (a p : B)‖ ≤ K * ‖J (c p) - J (c p)‖ at h
    rw [sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end Polar

section Diagonal

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
local instance boundaryPolarDiagonalOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder (Algebra M)
local instance boundaryPolarDiagonalStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing (Algebra M)

/-- The diagonal comparison unitary is itself measurable in the trace
Hilbert realization, in addition to its exact covariance and norm bound. -/
theorem exists_measurable_diagonal_unitary_comparison
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ a : D → D → unitary (Algebra M),
      AEStronglyMeasurable (fun p : D × D => J (a p.1 p.2 : Algebra M)) μ ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  obtain ⟨c, a, hcm, hca, hc, ha⟩ :=
    exists_measurable_diagonal_polar_data J hJ hτ shift W hW hWmeas hr0 hr hnear
  refine ⟨a, ?_, fun x y => (hca x y).2.2.2.2, ha⟩
  exact aestronglyMeasurable_polar_trace τ J hJ
    (fun p : D × D => c p.1 p.2) (fun p : D × D => a p.1 p.2) hr
    (fun p => (hca p.1 p.2).2.1) (fun p => (hca p.1 p.2).2.2.2.1) hcm

end Diagonal

/-- In a separably acting finite factor the diagonal comparison field is
measurable after evaluation on every vector of the original Hilbert space. -/
theorem exists_concrete_measurable_diagonal_unitary_comparison
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H] {M : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable (fun p : D × D =>
      concreteTraceEmbedding hM ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ a : D → D → unitary (Algebra M),
      AEStronglyMeasurable (fun p : D × D => concreteTraceEmbedding hM
        (a p.1 p.2 : Algebra M)) μ ∧
      (∀ ξ : H, AEStronglyMeasurable
        (fun p : D × D => ((a p.1 p.2 : Algebra M) : H →L[ℂ] H) ξ) μ) ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  borelize (ConcreteTraceHilbert hM)
  obtain ⟨a, ham, han, hac⟩ := exists_measurable_diagonal_unitary_comparison
    (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    (concreteFactorTrace_finiteVector hM) shift W hW hWmeas hr0 hr hnear
  refine ⟨a, ham, ?_, han, hac⟩
  intro ξ
  exact aestronglyMeasurable_operator_eval_of_trace
    (concreteTraceEmbedding hM) (concreteTraceEmbedding_norm hM)
    (concreteFactorTrace_finiteVector hM)
    (fun p : D × D => (a p.1 p.2 : Algebra M)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun p => norm_unitary_le_one (a p.1 p.2)) ham ξ

end

end KadisonKastler

end OAI
