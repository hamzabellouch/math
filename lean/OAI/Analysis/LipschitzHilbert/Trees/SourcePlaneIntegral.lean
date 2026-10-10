import OAI.Analysis.LipschitzHilbert.Trees.SourceTiledLineIntegral

namespace OAI

/-! The original measurable source integrand passes from separately chosen
line predictors to the plane. No joint measurability of those auxiliary
predictors is required, and no global integrability of the integrand is
assumed. The final scale dependence is exactly the top area. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem source_plane_integral_of_tiled_lines (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 2 < D) (s H C : ℝ) (hH : 0 < H)
    (f : ℝ × ℝ → ℝ) (hfmeas : AEStronglyMeasurable f (volume.prod volume))
    (hf : ∀ z, 0 ≤ f z)
    (hlocal : ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      IntegrableOn (fun x => f (x,y+s*x)) (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f (x,y+s*x)) ≤
        C*∫ x in sourceLineTile H k, T.weight K D (x,y+s*x)) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤ C*∫ z, T.weight K D z ∂volume.prod volume := by
  have hlines : ∀ᵐ y : ℝ ∂volume,
      Integrable (fun x => f (x,y+s*x)) volume ∧
      (∫ x, f (x,y+s*x)) ≤ C*∫ x, T.weight K D (x,y+s*x) := by
    filter_upwards [hlocal] with y hy
    exact source_top_tiled_line_integral T hK (by linarith) s y H C hH
      (fun x => f (x,y+s*x)) (fun x => hf _) hy
  exact integral_le_of_slope_slices s f (T.weight K D) hfmeas hf
    (T.weight_integrable hK hD) (hlines.mono fun _ h => h.1) (hlines.mono fun _ h => h.2)

/-- The actual top-weight integral contributes precisely K² times its
area and a fixed profile integral depending only on D. -/
theorem source_plane_area_bound (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 2 < D) (s H C : ℝ) (hH : 0 < H)
    (f : ℝ × ℝ → ℝ) (hfmeas : AEStronglyMeasurable f (volume.prod volume))
    (hf : ∀ z, 0 ≤ f z)
    (hlocal : ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      IntegrableOn (fun x => f (x,y+s*x)) (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f (x,y+s*x)) ≤
        C*∫ x in sourceLineTile H k, T.weight K D (x,y+s*x)) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤
        (C*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*T.length*T.width := by
  obtain ⟨hint,hbound⟩ := source_plane_integral_of_tiled_lines T hK hD s H C hH f hfmeas hf hlocal
  refine ⟨hint,?_⟩
  calc
    _ ≤ C*∫ z, T.weight K D z ∂volume.prod volume := hbound
    _ = _ := by rw [T.integral_weight hK D]; ring

/-- Finite top sums retain the same area constant. All original
integrands are integrable before their integrals are interchanged. -/
theorem source_plane_finite_area_sum {ι : Type*} (tops : Finset ι) (T : ι → SlopeBox)
    {K D : ℝ} (hK : 0 < K) (hD : 2 < D) (s H : ι → ℝ) (hH : ∀ i ∈ tops, 0 < H i)
    (C : ℝ) (f : ι → ℝ × ℝ → ℝ)
    (hfmeas : ∀ i ∈ tops, AEStronglyMeasurable (f i) (volume.prod volume))
    (hf : ∀ i ∈ tops, ∀ z, 0 ≤ f i z)
    (hlocal : ∀ i ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      IntegrableOn (fun x => f i (x,y+s i*x)) (sourceLineTile (H i) k) volume ∧
      (∫ x in sourceLineTile (H i) k, f i (x,y+s i*x)) ≤
        C*∫ x in sourceLineTile (H i) k, (T i).weight K D (x,y+s i*x)) :
    Integrable (fun z => ∑ i ∈ tops, f i z) (volume.prod volume) ∧
      (∫ z, ∑ i ∈ tops, f i z ∂volume.prod volume) ≤
        ((C*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*
          ∑ i ∈ tops, (T i).length*(T i).width := by
  have hi (i : ι) (hit : i ∈ tops) := source_plane_area_bound (T i) hK hD
    (s i) (H i) C (hH i hit) (f i) (hfmeas i hit) (hf i hit) (hlocal i hit)
  refine ⟨integrable_finsetSum tops (fun i hit => (hi i hit).1),?_⟩
  rw [integral_finsetSum tops (fun i hit => (hi i hit).1)]
  calc
    _ ≤ ∑ i ∈ tops, (C*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*
        (T i).length*(T i).width := Finset.sum_le_sum fun i hit => (hi i hit).2
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end LipschitzHilbert

end

end OAI
