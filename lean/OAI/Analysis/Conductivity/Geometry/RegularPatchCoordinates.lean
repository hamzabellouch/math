import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.comp {u : Coord3 → Fin 2 → ℝ} {O V : Set Coord3}
    (hO : IsOpen O) (hV : IsOpen V)
    (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u O) (h : TwoFieldRankRegular u O)
    {P : Coord3 → Coord3} (hP : ContDiffOn ℝ (↑(⊤:ℕ∞)) P V)
    (hm : MapsTo P V O) (hd : ∀ x∈V,Function.Surjective (fderiv ℝ P x)) :
    TwoFieldRankRegular (fun x => u (P x)) V := by
  have hPd (x) (hx : x∈V) :=
    (hP.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    have hud := (hu.differentiableOn (by simp) (P x) (hm hx)).differentiableAt
      (hO.mem_nhds (hm hx))
    change LinearIndependent ℝ (gradientColumns (fderiv ℝ (u ∘ P) x)).col
    rw [(hud.hasFDerivAt.comp x (hPd x hx).hasFDerivAt).fderiv]
    exact gradientColumns_rank _ ((gradientColumns_surjective _ (h (P x) (hm hx))).comp (hd x hx))
  · right; left
    obtain ⟨v,l,κ,hv,hl,hvd,he⟩ := h
    refine ⟨fun x => v (P x),l,κ,hv.comp hP hm,hl,?_,fun x hx j => he (P x) (hm hx) j⟩
    intro x hx hz
    have hvd' := (hv.differentiableOn (by simp) (P x) (hm hx)).differentiableAt
      (hO.mem_nhds (hm hx))
    change fderiv ℝ (v ∘ P) x=0 at hz
    rw [(hvd'.hasFDerivAt.comp x (hPd x hx).hasFDerivAt).fderiv] at hz
    apply hvd (P x) (hm hx)
    ext y
    obtain ⟨t,ht⟩ := hd x hx y
    have ht' := congrArg (fun D : Coord3 →L[ℝ] ℝ => D t) hz
    simpa only [ContinuousLinearMap.comp_apply,ht,_root_.zero_apply] using ht'
  · exact Or.inr (Or.inr ⟨κ,fun x hx => hκ (P x) (hm hx)⟩)

lemma RegularPatch.comp {u : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O V : Set Coord3} (h : RegularPatch u A O) (hV : IsOpen V)
    {P : Coord3 → Coord3} (hP : ContDiffOn ℝ (↑(⊤:ℕ∞)) P V)
    (hm : MapsTo P V O) (hd : ∀ x∈V,Function.Surjective (fderiv ℝ P x))
    (hB : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => (B x).val) V) :
    RegularPatch (fun x => u (P x)) B V :=
  ⟨hV,h.2.1.comp hP hm,hB,h.2.2.2.comp h.1 hV h.2.1 hP hm hd⟩

end ScalarConductivity

end
end

end OAI
