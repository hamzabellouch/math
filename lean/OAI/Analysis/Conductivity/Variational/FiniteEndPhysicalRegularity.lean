import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactDepthReductionTwo
import OAI.Analysis.Conductivity.Geometry.CollarLocalInverse

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma TwoFieldRankRegular.smoothCoordinates {u : Coord3 → Fin 2 → ℝ}
    {O V : Set Coord3} (hO : IsOpen O) (hV : IsOpen V)
    (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u O) (h : TwoFieldRankRegular u O)
    {g : Coord3 → Coord3} (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g V)
    (hm : MapsTo g V O) (hs : ∀ x∈V,Function.Surjective (fderiv ℝ g x)) :
    TwoFieldRankRegular (u ∘ g) V := by
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    have hd := (hu.differentiableOn (by simp) (g x) (hm hx)).differentiableAt (hO.mem_nhds (hm hx))
    have hdg := (hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
    rw [(hd.hasFDerivAt.comp x hdg.hasFDerivAt).fderiv]
    exact gradientColumns_rank _ ((gradientColumns_surjective _ (h (g x) (hm hx))).comp (hs x hx))
  · right; left
    obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    refine ⟨v ∘ g,l,κ,hv.comp hg hm,hl,?_,fun x hx j => he (g x) (hm hx) j⟩
    intro x hx hz
    have hxv := (hv.differentiableOn (by simp) (g x) (hm hx)).differentiableAt (hO.mem_nhds (hm hx))
    have hdg := (hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
    rw [(hxv.hasFDerivAt.comp x hdg.hasFDerivAt).fderiv] at hz
    apply hd (g x) (hm hx)
    ext y
    obtain ⟨z,rfl⟩ := hs x hx y
    exact congrArg (fun D : Coord3 →L[ℝ] ℝ => D z) hz
  · exact Or.inr (Or.inr ⟨κ,fun x hx => hκ (g x) (hm hx)⟩)

lemma sourceCollarInverse_contDiffAt (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (sourceCollarInverse i j) (sourceCollarPiece i j x) := by
  let f' := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  have hf := (sourceCollarPiece_contDiff i j).contDiffAt (x:=x)
  have hd : HasFDerivAt (sourceCollarPiece i j) (f' : Coord3 →L[ℝ] Coord3) x :=
    (sourceCollarPiece_hasStrictFDeriv i j x (sourceCollarOpenBox_subset hx)).hasFDerivAt
  have hn : (↑(⊤:ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hh := hf.to_localInverse hd hn
  apply hh.congr_of_eventuallyEq
  have he : sourceCollarInverse i j =ᶠ[𝓝 (sourceCollarPiece i j x)] hf.localInverse hd hn :=
    (hf.hasStrictFDerivAt' hd hn).localInverse_unique (sourceCollarInverse_eventually_left i j hx)
  exact he

lemma isOpen_sourceCollarOpenImage (i j : Fin 4) :
    IsOpen (sourceCollarPiece i j '' sourceCollarOpenBox) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x,hx,rfl⟩
  rw [←sourceCollarPiece_map_nhds i j hx]
  exact Filter.image_mem_map (isOpen_sourceCollarOpenBox.mem_nhds hx)

lemma sourceCollarInverse_contDiffOn (i j : Fin 4) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (sourceCollarInverse i j)
      (sourceCollarPiece i j '' sourceCollarOpenBox) := by
  rintro _ ⟨x,hx,rfl⟩
  exact (sourceCollarInverse_contDiffAt i j hx).contDiffWithinAt

lemma sourceCollarInverse_fderiv_surjective (i j : Fin 4) {y : Coord3}
    (hy : y∈sourceCollarPiece i j '' sourceCollarOpenBox) :
    Function.Surjective (fderiv ℝ (sourceCollarInverse i j) y) := by
  obtain ⟨x,hx,rfl⟩ := hy
  rw [(sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt.fderiv]
  exact (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.surjective

end ScalarConductivity

end
end

end OAI
