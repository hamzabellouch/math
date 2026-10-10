import OAI.Geometry.Relativity.CKS.SurfaceVolumeLower

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma measure_le_of_restrict_cover {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hcover : ⋃ n, U n = univ) (hle : ∀ n, μ.restrict (U n) ≤ ν.restrict (U n)) : μ ≤ ν := by
  let D := disjointed U
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hU
  have hDc : ⋃ n, D n = univ := iUnion_disjointed.trans hcover
  have hrestr : ∀ n, μ.restrict (D n) ≤ ν.restrict (D n) := by
    intro n
    calc
      _ = (μ.restrict (U n)).restrict (D n) :=
        (Measure.restrict_restrict_of_subset (disjointed_subset U n)).symm
      _ ≤ (ν.restrict (U n)).restrict (D n) :=
        Measure.restrict_mono (Subset.refl _) (hle n)
      _ = _ := Measure.restrict_restrict_of_subset (disjointed_subset U n)
  calc
    μ = μ.restrict (⋃ n, D n) := by rw [hDc,Measure.restrict_univ]
    _ = Measure.sum (fun n => μ.restrict (D n)) :=
      Measure.restrict_iUnion (disjoint_disjointed U) hD
    _ ≤ Measure.sum (fun n => ν.restrict (D n)) := by
      apply Measure.le_iff.2
      intro s hs
      simp only [Measure.sum_apply _ hs]
      exact ENNReal.tsum_le_tsum (fun n => hrestr n s)
    _ = ν.restrict (⋃ n, D n) := (Measure.restrict_iUnion (disjoint_disjointed U) hD).symm
    _ = ν := by rw [hDc,Measure.restrict_univ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem riemannianVolume_lower (g G : Metric (M := M)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x (v : TangentSpace I x), c * g.inner x v v ≤ G.inner x v v) :
    ENNReal.ofReal c • riemannianVolume g ≤ riemannianVolume G := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact le_of_eq (Subsingleton.elim _ _)
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    apply measure_le_of_restrict_cover _ _ (fun n => (extChartAt I (f n)).source)
      (fun n => (isOpen_extChartAt_source (f n)).measurableSet) (eq_univ_of_univ_subset hf)
    intro n
    rw [Measure.restrict_smul,riemannianVolume_isVolume g (f n),riemannianVolume_isVolume G (f n)]
    exact localVolume_lower g G hc hlow (f n)

end CKSSurfaceVolume

end

end OAI
