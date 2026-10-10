import OAI.Geometry.SurfaceImmersion.Correction.FiniteSmootherLinearity
import OAI.Geometry.Immersion.ClosedSurface.SquarePartition
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

/-! Finite chart data with inner and outer cutoffs for smoothing on a closed
surface. All chart and cutoff data are chosen independently of the input. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def chart (p : M) : OpenPartialHomeomorph M Base :=
  (chartAt Plane p).trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toOpenPartialHomeomorph

lemma chart_source (p : M) : (chart p).source = (chartAt Plane p).source := by
  simp [chart]

variable [IsManifold planeModel ∞ M]

lemma chart_smooth (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ, Base) ∞ (chart p) (chart p).source := by
  rw [chart_source]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma chart_symm_smooth (p : M) :
    ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ (chart p).symm (chart p).target := by
  have h := (contMDiffOn_chart_symm (I := planeModel) (x := p) (n := ∞)).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.contMDiffOn
    (fun x (hx : x ∈ (chart p).target) => by simpa [chart] using hx)
  simpa [chart] using h

/-- The outer cutoff is one on the support of the partition weight and has
its own closed support inside the same chart. -/
structure SmoothingAtlas (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] where
  centers : Finset M
  weight : centers → M → ℝ
  outer : centers → M → ℝ
  weight_smooth : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (weight i)
  weight_support : ∀ i, tsupport (weight i) ⊆ (chart (i : M)).source
  outer_smooth : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (outer i)
  outer_support : ∀ i, tsupport (outer i) ⊆ (chart (i : M)).source
  outer_one : ∀ i x, x ∈ tsupport (weight i) → outer i x = 1
  partition : ∀ x, ∑ i, (weight i x) ^ 2 = 1

variable [T2Space M] [CompactSpace M]

/-- A compact smooth surface admits fixed finite smoothing chart data. -/
theorem exists_smoothingAtlas : Nonempty (SmoothingAtlas M) := by
  classical
  obtain ⟨t, ψ, hψ, hsupp, _, _, hsum⟩ :=
    PhaseGeometry.exists_finite_smooth_square_partition (E := Plane)
      (fun p : M => (chart p).source) (fun p => (chart p).open_source)
      (fun p => by rw [chart_source]; exact mem_chart_source Plane p)
  have hout : ∀ i : t, ∃ χ : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (ψ i), χ x = 1 := by
    intro i
    have hc : IsCompact (tsupport (ψ i)) := (isClosed_tsupport _).isCompact
    obtain ⟨O, hO, hKO, hOc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hsupp i))
    obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hO (isClosed_tsupport (ψ i)) hKO
    refine ⟨χ, hχ, ?_, fun x hx => (hχone x).mp hx⟩
    change closure (Function.support χ) ⊆ _
    rw [hχs]
    exact hOc
  choose χ hχ hχs hχone using hout
  exact ⟨⟨t, ψ, χ, hψ, hsupp, hχ, hχs, hχone, hsum⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
