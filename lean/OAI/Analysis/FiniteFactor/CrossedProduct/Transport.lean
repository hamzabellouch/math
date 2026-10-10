import OAI.Analysis.FiniteFactor.CrossedProduct.MultiplicationAdjoint

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Combined integer base rotation and fiber translation. -/
def sourceTransportIndex (θ : SourceCoordinate → ℝ) (n m : ℤ)
    (z : (SourceCoordinate → ℝ) × ℤ) : (SourceCoordinate → ℝ) × ℤ :=
  (coordinateRotate θ n z.1, z.2 - m)

theorem sourceTransportIndex_preserving (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    MeasurePreserving (sourceTransportIndex θ n m)
      (sourceMeasure SourceCoordinate) (sourceMeasure SourceCoordinate) := by
  have hm : Measurable (fun k : ℤ => k-m) := measurable_of_countable _
  have hi : Function.Injective (fun k : ℤ => k-m) := by intro a b h; dsimp at h; omega
  have hs : Function.Surjective (fun k : ℤ => k-m) := by intro k; exact ⟨k+m, by dsimp; omega⟩
  have hp : MeasurePreserving (fun k : ℤ => k-m) Measure.count Measure.count := by
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← hi.encard_image, Set.image_preimage_eq S hs]
  exact (coordinateRotate_preserving θ n).prod hp

def sourceTransport (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  (Lp.compMeasurePreservingₗᵢ ℂ (sourceTransportIndex θ n m)
    (sourceTransportIndex_preserving θ n m)).toContinuousLinearMap

theorem sourceTransport_apply_ae (θ : SourceCoordinate → ℝ) (n m : ℤ)
    (f : SourceHilbert SourceCoordinate) :
    sourceTransport θ n m f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => f (sourceTransportIndex θ n m z) :=
  Lp.coeFn_compMeasurePreserving f (sourceTransportIndex_preserving θ n m)

theorem sourceTransport_mul (θ : SourceCoordinate → ℝ) (n m p q : ℤ) :
    sourceTransport θ n m * sourceTransport θ p q = sourceTransport θ (n+p) (m+q) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n m).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ p q f)
  filter_upwards [sourceTransport_apply_ae θ n m (sourceTransport θ p q f),
    sourceTransport_apply_ae θ (n+p) (m+q) f, ht] with z h1 h2 h3
  change (sourceTransport θ n m (sourceTransport θ p q f)) z = _
  rw [h1, h2, h3]
  congr 1
  simp [sourceTransportIndex, coordinateRotate_add, sub_sub]

theorem sourceHilbert_cube : ∀ᵐ z ∂sourceMeasure SourceCoordinate,
    ∀ i, z.1 i ∈ Set.Ico (0 : ℝ) 1 := by
  have hc : ∀ᵐ x ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure),
      ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    have hh : ∀ᵐ t ∂(Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)).map
        (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
      rw [Measure.infinitePi_map_eval]
      exact ae_restrict_mem measurableSet_Ico
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh
  exact Measure.quasiMeasurePreserving_fst.ae hc

theorem sourceTransport_zero (θ : SourceCoordinate → ℝ) : sourceTransport θ 0 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourceTransport_apply_ae θ 0 0 f, sourceHilbert_cube] with z hz hc
  change (sourceTransport θ 0 0 f) z = f z
  rw [hz]
  congr 1
  apply Prod.ext
  · funext i
    simpa [sourceTransportIndex, coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  · simp [sourceTransportIndex]

theorem sourceTransport_star (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    star (sourceTransport θ n m) = sourceTransport θ (-n) (-m) := by
  have hi (f h : SourceHilbert SourceCoordinate) :
      inner ℂ (sourceTransport θ n m f) (sourceTransport θ n m h) = inner ℂ f h :=
    (Lp.compMeasurePreservingₗᵢ ℂ (sourceTransportIndex θ n m)
      (sourceTransportIndex_preserving θ n m)).inner_map_map f h
  have hinv : sourceTransport θ n m * sourceTransport θ (-n) (-m) = 1 := by
    rw [sourceTransport_mul]; simp only [add_neg_cancel, sourceTransport_zero]
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  have hih := hi (sourceTransport θ (-n) (-m) f) h
  have he : sourceTransport θ n m (sourceTransport θ (-n) (-m) f) = f := by
    change (sourceTransport θ n m * sourceTransport θ (-n) (-m)) f = f
    rw [hinv]; rfl
  rw [he] at hih
  exact hih.symm

end
end FiniteFactor

end OAI
