import Mathlib
import OAI.Analysis.Conductivity.Sobolev.AxialPairRank

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.translate {u : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (h : TwoFieldRankRegular u O) (c : Coord3) (d : Fin 2 → ℝ) :
    TwoFieldRankRegular (fun x => u (x-c)+d) ((fun x => x-c) ⁻¹' O) := by
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_add_const,fderiv_comp_sub]
    exact h (x-c) hx
  · right; left
    obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    refine ⟨fun x => v (x-c),l,κ+d,?_,hl,?_,?_⟩
    · exact hv.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)
    · intro x hx
      rw [fderiv_comp_sub]
      exact hd (x-c) hx
    · intro x hx j
      simp only [Pi.add_apply,he (x-c) hx j]
      ring
  · exact Or.inr (Or.inr ⟨κ+d,fun x hx => by dsimp only; rw [hκ (x-c) hx]⟩)

lemma RegularPatch.translate {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3} {O : Set Coord3}
    (h : RegularPatch u A O) (c : Coord3) (d : Fin 2 → ℝ) :
    RegularPatch (fun x => u (x-c)+d) (fun x => A (x-c)) ((fun x => x-c) ⁻¹' O) := by
  refine ⟨h.1.preimage (continuous_id.sub continuous_const),?_,?_,h.2.2.2.translate c d⟩
  · exact (h.2.1.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)).add contDiffOn_const
  · exact h.2.2.1.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)

lemma mem_regularRegion_translate {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x c : Coord3} (h : x-c∈regularRegion u A U) (d : Fin 2 → ℝ) :
    x∈regularRegion (fun y => u (y-c)+d) (fun y => A (y-c)) ((fun y => y-c) ⁻¹' U) := by
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨(fun y => y-c) ⁻¹' O,preimage_mono hOU,hO.translate c d,hxO⟩

lemma mem_regularRegion_congr_nhds {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {V U : Set Coord3} {x : Coord3} (h : x∈regularRegion u A V)
    (hu : v =ᶠ[𝓝 x] u) (hA : B =ᶠ[𝓝 x] A) (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion v B U := by
  obtain ⟨O,hOV,hO,hxO⟩ := mem_regularRegion_iff.mp h
  have hh : {y | y∈O ∧ y∈U ∧ v y=u y ∧ B y=A y}∈𝓝 x := by
    filter_upwards [hO.1.mem_nhds hxO,hU.mem_nhds hx,hu,hA] with y hy0 hyU hyu hyA
    exact ⟨hy0,hyU,hyu,hyA⟩
  obtain ⟨W,hWsub,hW,hxW⟩ := mem_nhds_iff.mp hh
  refine mem_regularRegion_iff.mpr ⟨W,fun y hy => (hWsub hy).2.1,?_,hxW⟩
  exact (hO.mono hW (fun y hy => (hWsub hy).1)).congr
    (fun y hy => (hWsub hy).2.2.1) (fun y hy => (hWsub hy).2.2.2)

lemma axialPair_translate (f : Coord3 → ℝ) (c x : Coord3) :
    axialPair f (x-c)+![c 0,0]=axialPair (fun y => f (y-c)) x := by
  ext i
  fin_cases i <;> simp [axialPair]

end ScalarConductivity

end

end OAI
