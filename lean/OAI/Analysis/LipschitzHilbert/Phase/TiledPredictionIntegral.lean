import OAI.Analysis.LipschitzHilbert.Fourier.LineTiling
import OAI.Analysis.LipschitzHilbert.Fourier.LineWeightAverage
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral
import OAI.Analysis.LipschitzHilbert.Estimates.PartitionIntegral

namespace OAI

/-! Cellwise constructed predictions give the reference-line and planar
integral bounds. Auxiliary choices need no joint measurability. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

/-- The finite prediction data on one actual line mesh. -/
structure LineCellMajorant (g : FiniteLineGrid) (T : SlopeBox)
    (K D y B : ℝ) (f : ℝ → ℝ) where
  factor : ℕ → ℝ → ℝ
  nonneg : ∀ n < g.depth, ∀ x, 0 ≤ factor n x
  constant : ∀ n < g.depth, ∀ x z,
    g.index (n + 1) x = g.index (n + 1) z → factor n x = factor n z
  average : ∀ n < g.depth, ∀ i : Fin (g.branching ^ g.depth),
    (∫ x in {x | g.index n x = i}, factor n x ∂volume.restrict g.root) ≤
      (volume.restrict g.root).real {x | g.index n x = i}
  dominates : ∀ x ∈ g.root, f x ≤ B * (T.weight K D (x, y + T.slope * x) *
    ∏ n ∈ Finset.range g.depth, factor n x)

theorem LineCellMajorant.integral_bound {g : FiniteLineGrid} {T : SlopeBox}
    {K D y B : ℝ} {f : ℝ → ℝ} (P : LineCellMajorant g T K D y B f)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hB : 0 ≤ B) (hwidth : g.width ≤ T.length)
    (hf : AEStronglyMeasurable f volume) (hf0 : ∀ x, 0 ≤ f x) :
    IntegrableOn f g.root volume ∧
      (∫ x in g.root, f x) ≤ B * Real.exp (2 * D) *
        ∫ x in g.root, T.weight K D (x, y + T.slope * x) := by
  obtain ⟨hint, hbound⟩ := g.top_weight_average T y hK hD hwidth
    P.factor P.nonneg P.constant P.average
  have hdom : ∀ᵐ x ∂volume.restrict g.root, f x ≤ B *
      (T.weight K D (x, y + T.slope * x) * ∏ n ∈ Finset.range g.depth, P.factor n x) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet g.root from measurableSet_Ico)] with x hx
    exact P.dominates x hx
  have hfi : IntegrableOn f g.root volume := (hint.const_mul B).mono' hf.restrict (by
    filter_upwards [hdom] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hx)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ x in g.root, B * (T.weight K D (x, y + T.slope * x) *
        ∏ n ∈ Finset.range g.depth, P.factor n x) :=
      integral_mono_ae hfi (hint.const_mul B) hdom
    _ = B * ∫ x in g.root, T.weight K D (x, y + T.slope * x) *
        ∏ n ∈ Finset.range g.depth, P.factor n x := integral_const_mul _ _
    _ ≤ B * (Real.exp (2 * D) * ∫ x in g.root, T.weight K D (x, y + T.slope * x)) :=
      mul_le_mul_of_nonneg_left hbound hB
    _ = _ := (mul_assoc _ _ _).symm

theorem tiled_prediction_integral (T : SlopeBox) (origin H : ℝ) (hH : 0 < H)
    (G N : ℕ) (hG : 0 < G) {K D y B : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hB : 0 ≤ B) (hwidth : H ≤ T.length)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hw : Integrable (fun x => T.weight K D (x, y + T.slope * x)) volume)
    (hp : ∀ k : ℤ, Nonempty (LineCellMajorant
      (tiledLineGrid origin H hH G N hG k) T K D y B f)) :
    Integrable f volume ∧ (∫ x, f x) ≤ B * Real.exp (2 * D) *
      ∫ x, T.weight K D (x, y + T.slope * x) := by
  have hcell (k : ℤ) := (Classical.choice (hp k)).integral_bound
    hK hD hB hwidth hf hf0
  exact integral_le_of_partition volume
    (fun k : ℤ => (tiledLineGrid origin H hH G N hG k).root)
    (tiledLineGrid_measurable origin H hH G N hG)
    (tiledLineGrid_pairwise_disjoint origin H hH G N hG)
    (tiledLineGrid_cover origin H hH G N hG) f _ hf0 hw
    (fun k => (hcell k).1) (fun k => (hcell k).2)

/-- Only the original integrand is required to be planar measurable. All
snapshot choices may be made separately on almost every reference line. -/
theorem planar_prediction_integral (T : SlopeBox) (origin H : ℝ) (hH : 0 < H)
    (G N : ℕ) (hG : 0 < G) {K D B : ℝ}
    (hK : 1 ≤ K) (hD : 2 < D) (hB : 0 ≤ B) (hwidth : H ≤ T.length)
    (f : ℝ × ℝ → ℝ) (hf : AEStronglyMeasurable f (volume.prod volume))
    (hf0 : ∀ z, 0 ≤ f z)
    (hp : ∀ᵐ y ∂volume, ∀ k : ℤ, Nonempty (LineCellMajorant
      (tiledLineGrid origin H hH G N hG k) T K D y B
      (fun x => f (x, y + T.slope * x)))) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤
        B * Real.exp (2 * D) * ∫ z, T.weight K D z ∂volume.prod volume := by
  have hw := T.weight_integrable (K := K) (by linarith) hD
  have hs := (slopeShear_measurePreserving T.slope).integrable_comp_of_integrable hw
  have hfmeas := hf.comp_measurePreserving (slopeShear_measurePreserving T.slope)
  have hlines : ∀ᵐ y ∂volume,
      Integrable (fun x => f (x, y + T.slope * x)) volume ∧
        (∫ x, f (x, y + T.slope * x)) ≤ B * Real.exp (2 * D) *
          ∫ x, T.weight K D (x, y + T.slope * x) := by
    filter_upwards [hp, hs.prod_left_ae, hfmeas.prodMk_right] with y hy hwy hfy
    exact tiled_prediction_integral T origin H hH G N hG hK (by linarith) hB hwidth
      _ hfy (fun x => hf0 _) hwy hy
  exact integral_le_of_slope_slices T.slope f (T.weight K D) hf hf0 hw
    (hlines.mono fun _ h => h.1) (hlines.mono fun _ h => h.2)

end LipschitzHilbert

end

end OAI
