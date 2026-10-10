import OAI.Geometry.NodalSets.Elliptic.CompactUniformIntegralLimit
import OAI.Geometry.NodalSets.Elliptic.CompactUniformProducts
import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets
import OAI.Geometry.NodalSets.Elliptic.SmoothJet

namespace OAI

namespace Yau.Analysis
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem compact_first_jet_functional_limit
    (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q)
    (a : Fin 4 → Yau.Jets.Coord → ℝ) (b : Yau.Jets.Coord → ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : Continuous b)
    (has : ∀ i x, x ∉ Q → a i x=0) (hbs : ∀ x, x ∉ Q → b x=0)
    (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hv : ContDiff ℝ ∞ v)
    (hconv : ∀ ds, TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop Q) :
    Tendsto (fun j ↦ ∫ x, (∑ i, a i x*partialJet (W j) [i] x)-b x*W j x) atTop
      (𝓝 (∫ x, (∑ i, a i x*partialJet v [i] x)-b x*v x)) := by
  have hcont (f : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) :
      Continuous (fun x ↦ (∑ i, a i x*partialJet f [i] x)-b x*f x) :=
    (continuous_finsetSum _ (fun i _ ↦ (ha i).mul (partialJet_smooth f hf [i]).continuous)).sub
      (hb.mul hf.continuous)
  have hzero (f : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (hx : x ∉ Q) :
      (∑ i, a i x*partialJet f [i] x)-b x*f x=0 := by
    simp [has _ x hx,hbs x hx]
  apply compact_uniform_integral_limit volume Q hQ _ _ (fun j ↦ hcont (W j) (hW j)) (hcont v hv)
    (fun j ↦ hzero (W j)) (hzero v)
  have hsum := finite_uniform_sum Finset.univ Q
    (fun i j x ↦ a i x*partialJet (W j) [i] x) (fun i x ↦ a i x*partialJet v [i] x)
    (fun i _ ↦ compact_uniform_mul Q hQ (fun _ ↦ a i) (fun j ↦ partialJet (W j) [i])
      (a i) (partialJet v [i]) (fun _ ↦ ha i) (fun j ↦ (partialJet_smooth (W j) (hW j) [i]).continuous)
      (ha i) (partialJet_smooth v hv [i]).continuous (by intro s hs; exact Eventually.of_forall (fun _ _ _ ↦ refl_mem_uniformity hs)) (hconv [i]))
  exact hsum.sub (compact_uniform_mul Q hQ (fun _ ↦ b) W b v (fun _ ↦ hb)
    (fun j ↦ (hW j).continuous) hb hv.continuous (by intro s hs; exact Eventually.of_forall (fun _ _ _ ↦ refl_mem_uniformity hs)) (hconv []))

end
end Yau.Analysis

end OAI
