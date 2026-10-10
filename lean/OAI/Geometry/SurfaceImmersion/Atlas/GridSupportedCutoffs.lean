import OAI.Geometry.Immersion.ClosedSurface.CompactPartition
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport

namespace OAI

/-! The actual normalized grid cutoffs multiplied by a supported chart
weight. The derivative constant is independent of the number of cells. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.WeightedEstimates

lemma WeightedBound.to_unit_scale {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {s C : ℝ} {m : ℕ}
    {f : E → F} (hb : WeightedBound U s m C f) (hs : 0 < s) (hs1 : s ≤ 1)
    (hC : 0 ≤ C) : WeightedBound U 1 m (C/s^m) f := by
  intro j hj x hx
  simp only [one_pow,one_mul]
  exact (hb.deriv_le hs hj hx).trans (div_le_div_of_nonneg_left hC
    (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1 hj))

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.PhaseGrid
open WeightedEstimates JetPolynomial

def supportedNormalizedCutoff {K : Compacts Base} (f : SupportedField (F := ℝ) K)
    {a : Finset Index} {h : ℝ} (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h)
    (k : Index) : SupportedField (F := ℝ) K := by
  refine ⟨fun x => f x * normalizedCutoff a h k x,?_,?_⟩
  · apply contDiff_of_tsupport_subset (coverRegion_open a h)
      ((tsupport_mul_subset_left.trans f.tsupport_subset).trans hK)
    exact f.contDiff.contDiffOn.mul
      (normalizedCutoff_smooth hh (fun y hy => coverRegion_covers a h hy) k)
  · intro x hx
    change f x * normalizedCutoff a h k x = 0
    simp only [f.zero_on_compl hx,Pi.zero_apply,zero_mul]

@[simp] lemma supportedNormalizedCutoff_apply {K : Compacts Base}
    (f : SupportedField (F := ℝ) K) {a : Finset Index} {h : ℝ}
    (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h) (k : Index) (x : Base) :
    supportedNormalizedCutoff f hh hK k x = f x * normalizedCutoff a h k x := rfl

theorem supported_normalized_cutoff_bounds :
    ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ {K : Compacts Base} (f : SupportedField (F := ℝ) K)
      {a : Finset Index} {h : ℝ} (hh : 0 < h) (_hh1 : h ≤ 1)
      (hK : (K : Set Base) ⊆ coverRegion a h) (P : ℕ → ℝ),
      (∀ m, 0 ≤ P m) → (∀ m, WeightedBound univ 1 m (P m) f) →
      ∀ k m, WeightedBound univ 1 m (C m*P m/h^m)
        (supportedNormalizedCutoff f hh hK k) := by
  obtain ⟨C,hC,hb⟩ := normalizedCutoff_weighted_bounds
  refine ⟨fun m => 2^m*C m,fun m => one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (hC m),?_⟩
  intro K f a h hh hh1 hK P hP hf k m
  let U := coverRegion a h
  have hU : IsOpen U := coverRegion_open a h
  have hnorm := hb h hh a U hU (fun x hx => coverRegion_covers a h hx) k m
  have hsm := normalizedCutoff_smooth hh (fun x hx => coverRegion_covers a h hx) k
  have hprod := ((hf m).shrink_scale hh.le hh1).restrict_open hU
  have hmul := hprod.real_mul hU.uniqueDiffOn hh.le (hP m)
    (zero_le_one.trans (hC m)) f.contDiff.contDiffOn hsm hnorm
  have hd : WeightedBound U h m (2^m*P m*C m) (supportedNormalizedCutoff f hh hK k) :=
    hmul
  have hprod : 0 ≤ 2^m*P m*C m :=
    mul_nonneg (mul_nonneg (by positivity) (hP m)) (zero_le_one.trans (hC m))
  have hall := hd.extend_support hU
    ((supportedNormalizedCutoff f hh hK k).tsupport_subset.trans hK) hprod
  convert hall.to_unit_scale hh hh1 hprod using 1
  ring

end ClosedSurfaceR4.PhaseGrid

end

end OAI
