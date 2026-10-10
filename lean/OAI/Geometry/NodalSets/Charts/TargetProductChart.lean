import OAI.Geometry.NodalSets.Charts.ManifoldCompactExtension
import OAI.Geometry.NodalSets.Elliptic.PolynomialEvaluation
import OAI.Geometry.NodalSets.Elliptic.TargetAmbientMeasure

namespace OAI

namespace Yau.Target
open Manifold Set Filter Yau.Jets
open scoped ContDiff Topology NNReal ENNReal
noncomputable section

def modelCoordinateEquiv : Model ≃L[ℝ] Coord × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).prodCongr
    (PiLp.equivOfUnique (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 1 ↦ ℝ))

def productChart (p : Manifold5) (a b : ℝ) (m : Manifold5) : Coord × ℝ :=
  let z := modelCoordinateEquiv (extChartAt modelWithCorners p m)
  (z.1, (z.2-a)/b)

def productChartInverse (p : Manifold5) (a b : ℝ) (z : Coord × ℝ) : Manifold5 :=
  (extChartAt modelWithCorners p).symm (modelCoordinateEquiv.symm (z.1,a+b*z.2))

def productChartDomain (p : Manifold5) (a b : ℝ) : Set (Coord × ℝ) :=
  {z | modelCoordinateEquiv.symm (z.1,a+b*z.2) ∈ (extChartAt modelWithCorners p).target}

lemma productChart_inverse_mem (p : Manifold5) (a b : ℝ) {z : Coord × ℝ}
    (hz : z ∈ productChartDomain p a b) :
    productChartInverse p a b z ∈ (extChartAt modelWithCorners p).source :=
  (extChartAt modelWithCorners p).map_target hz

lemma productChart_right_inv (p : Manifold5) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    {z : Coord × ℝ} (hz : z ∈ productChartDomain p a b) :
    productChart p a b (productChartInverse p a b z) = z := by
  unfold productChart productChartInverse
  rw [(extChartAt modelWithCorners p).right_inv hz, modelCoordinateEquiv.apply_symm_apply]
  simp [hb]

lemma productChart_contMDiffOn (p : Manifold5) (a b : ℝ) :
    ContMDiffOn modelWithCorners 𝓘(ℝ,Coord × ℝ) ∞ (productChart p a b)
      (extChartAt modelWithCorners p).source := by
  have hc : ContMDiffOn modelWithCorners 𝓘(ℝ,Coord × ℝ) ∞
      (fun m ↦ modelCoordinateEquiv (extChartAt modelWithCorners p m))
      (extChartAt modelWithCorners p).source :=
    modelCoordinateEquiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn (by
      simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := modelWithCorners) (x := p)))
  have hn : ContDiff ℝ ∞ (fun z : Coord × ℝ ↦ (z.1,(z.2-a)/b)) :=
    contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const b)
  exact hn.contMDiff.comp_contMDiffOn hc

lemma productChartInverse_continuousOn (p : Manifold5) (a b : ℝ) :
    ContinuousOn (productChartInverse p a b) (productChartDomain p a b) := by
  apply (continuousOn_extChartAt_symm p).comp
    (modelCoordinateEquiv.symm.continuous.comp
      (continuous_fst.prodMk (continuous_const.add (continuous_const.mul continuous_snd)))).continuousOn
  exact fun z hz ↦ hz

lemma compact_productChart_extension (p : Manifold5) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    {K : Set (Coord × ℝ)} (hK : IsCompact K) (hKD : K ⊆ productChartDomain p a b) :
    ∃ P : Manifold5 → Coord × ℝ, ContMDiff modelWithCorners 𝓘(ℝ,Coord × ℝ) ∞ P ∧
      ∀ z ∈ K, P (productChartInverse p a b z) = z := by
  have hL : IsCompact (productChartInverse p a b '' K) :=
    hK.image_of_continuousOn ((productChartInverse_continuousOn p a b).mono hKD)
  obtain ⟨P,hP,_,_,hPK⟩ := Yau.Geometry.manifold_compact_smooth_extension
    (I := modelWithCorners) hL (isOpen_extChartAt_source p)
    (by rintro m ⟨z,hz,rfl⟩; exact productChart_inverse_mem p a b (hKD hz))
    (productChart p a b) (productChart_contMDiffOn p a b)
  refine ⟨P,hP,?_⟩
  intro z hz
  rw [(hPK _ (mem_image_of_mem _ hz)).eq_of_nhds,
    productChart_right_inv p a hb (hKD hz)]

end
end Yau.Target

end OAI
