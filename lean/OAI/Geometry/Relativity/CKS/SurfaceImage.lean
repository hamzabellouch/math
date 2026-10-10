import OAI.Geometry.Relativity.CKS.SurfaceLocalImage
import OAI.Geometry.Relativity.CKS.SurfaceImageMeasure

namespace OAI

noncomputable section
namespace CKSSurfaceVolume
noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [CompactSpace M]

theorem volume_le_of_surjective_nonexpanding
    (g : Metric (M := M)) (h : Metric (M := N)) (f : M → N)
    (hf : ContMDiff I I 1 f) (hsurj : Function.Surjective f)
    (hshort : ∀ x v, h.inner (f x) (mfderiv I I f x v) (mfderiv I I f x v) ≤
      g.inner x v v) : riemannianVolume h univ ≤ riemannianVolume g univ := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hm =>
    let := hm
    have : IsEmpty N := ⟨fun y => (hsurj y).elim (fun x _ => isEmptyElim x)⟩
    have hu : (univ : Set N) = ∅ := by ext x; exact isEmptyElim x
    rw [hu,measure_empty]
    exact zero_le
  | inr hm =>
    let := hm
    let U : M → Set M := fun x => (extChartAt I x).source ∩ f ⁻¹' (extChartAt I (f x)).source
    have hU : ∀ x, IsOpen (U x) := fun x =>
      (isOpen_extChartAt_source x).inter ((isOpen_extChartAt_source (f x)).preimage hf.continuous)
    have hUx : ∀ x, x ∈ U x := fun x => ⟨mem_extChartAt_source x,mem_extChartAt_source (f x)⟩
    obtain ⟨a,ha⟩ := isLindelof_univ.indexed_countable_subcover U hU
      (fun x _ => mem_iUnion.mpr ⟨x,hUx x⟩)
    let D := disjointed (U ∘ a)
    have hcover : ⋃ n, D n = univ := iUnion_disjointed.trans (eq_univ_of_univ_subset ha)
    have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => (hU (a n)).measurableSet)
    have hDf : ∀ n, MeasurableSet (f '' D n) := fun n => sigmaCompact_measurable
      ((sigmaCompact_disjointed_open (U ∘ a) (fun n => hU (a n)) n).image hf.continuous)
    have hDn : ∀ n, D n ⊆ U (a n) := fun n => disjointed_subset (U ∘ a) n
    have hle : ∀ n, riemannianVolume h (f '' D n) ≤ riemannianVolume g (D n) := by
      intro n
      have hx : D n ⊆ (extChartAt I (a n)).source := fun x hx => (hDn n hx).1
      have hy : MapsTo f (D n) (extChartAt I (f (a n))).source := fun x hx => (hDn n hx).2
      rw [volume_on_subset h (riemannianVolume_isVolume h) (f (a n)) (by rintro y ⟨x,hx,rfl⟩; exact hy hx),
        volume_on_subset g (riemannianVolume_isVolume g) (a n) hx]
      exact localVolume_image_le g h f hf hshort _ _ (hD n) (hDf n) hx hy
    calc
      riemannianVolume h univ = riemannianVolume h (⋃ n, f '' D n) := by
        rw [← image_iUnion,hcover,image_univ,hsurj.range_eq]
      _ ≤ ∑' n, riemannianVolume h (f '' D n) := measure_iUnion_le _
      _ ≤ ∑' n, riemannianVolume g (D n) := ENNReal.tsum_le_tsum hle
      _ = riemannianVolume g (⋃ n, D n) := (measure_iUnion (disjoint_disjointed _) hD).symm
      _ = riemannianVolume g univ := by rw [hcover]
end
end CKSSurfaceVolume

end

end OAI
