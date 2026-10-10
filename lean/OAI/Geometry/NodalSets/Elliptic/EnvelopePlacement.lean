import OAI.Geometry.NodalSets.Elliptic.CorrugationFiniteGainLemmas
import OAI.Geometry.NodalSets.Elliptic.CorrugationLargeSlope
import OAI.Geometry.NodalSets.Elliptic.EnvelopeNestedDomainsLemmas
import OAI.Geometry.NodalSets.Elliptic.EnvelopeParameterAdmissibility

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem exists_placed_envelope (o : Coord) {L : ℝ} (hL : 0 < L)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S0 : Coord → ℝ)
    {P U K : Set Coord} (hP : IsOpen P) (hPc : IsCompact (closure P))
    (hU : IsOpen U) (hPU : closure P ⊆ U)
    (hDP : Icc o (fun j ↦ o j+L) ⊆ P) (hK : IsCompact K) (hKP : K ⊆ P)
    (hg : ContDiffOn ℝ ∞ g U) (hS0 : ContDiffOn ℝ ∞ S0 U)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ Icc o (fun j ↦ o j+L), ∀ u v, g x u v = g x v u)
    (hseed : sourceDirectionalAdmissibleOn g S0 (closure P)) (T : ℝ) :
    ∃ (S : Coord → ℝ) (c : ℝ) (C V : Set Coord), 0 < c ∧
      ContDiffOn ℝ ∞ S U ∧ IsCompact C ∧ C ⊆ P ∧
      Icc o (fun j ↦ o j+L) ∪ K ⊆ C ∧
      (∀ x ∈ Icc o (fun j ↦ o j+L) ∪ K, S0 x+c ≤ S x) ∧
      (∀ x ∉ C, S x ≤ S0 x-c) ∧
      IsOpen V ∧ closure P ⊆ V ∧ V ⊆ U ∧ sourceDirectionalAdmissibleOn g S V ∧
      T < ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x := by
  let D := Icc o (fun j ↦ o j+L)
  have hDcl : D ⊆ closure P := hDP.trans subset_closure
  obtain ⟨f,hf,hfb,hf1,C,hC,hCP,hDC,hfout⟩ := exists_signed_envelope_offset
    (isCompact_Icc.union hK) hP (union_subset hDP hKP)
  obtain ⟨δ,hδ,had⟩ := envelope_parameter_admissibility g S0 f hPc hU hPU hg hS0 hf hp hseed
  let t := δ/2
  have ht : 0 < t := by dsimp [t]; positivity
  have htd : |t| < δ := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hadt := had t htd
  have hSt : ContDiffOn ℝ ∞ (S0+t • f) U := hS0.add (contDiff_const.smul hf).contDiffOn
  obtain ⟨w,hw,hwc,hws,hwb,hwbb,hSw,hgain,W,hW,hDW,hWU,hadw⟩ :=
    exists_large_admissible_corrugation o hL g (S0+t • f) hU (hDcl.trans hPU)
      hg hSt hp hsym (fun x hx ↦ hadt x (hDcl hx)) T (by positivity : 0 < t/2)
  have hadall := sourceDirectionalAdmissible_support g (S0+t • f) w
    (hws.trans interior_subset) hadt (fun x hx ↦ hadw x (hDW hx))
  obtain ⟨V,hV,hPV,hVU,hVa⟩ := source_admissibility_neighborhood g ((S0+t • f)+w)
    hU hPU hg hSw hp hadall
  refine ⟨(S0+t • f)+w,t/2,C,V,by positivity,hSw,hC,hCP,hDC,?_,?_,hV,hPV,hVU,hVa,hgain⟩
  · intro x hx
    have hx1 := (hf1 x hx).eq_of_nhds
    have hb := (abs_lt.mp (hwb x)).1
    change S0 x+t/2 ≤ S0 x+t*f x+w x
    rw [hx1]
    linarith
  · intro x hx
    have hxD : x ∉ D := fun hd ↦ hx (hDC (Or.inl hd))
    have hw0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hxD (interior_subset (hws hs)))
    change S0 x+t*f x+w x ≤ S0 x-t/2
    rw [hfout x hx,hw0]
    linarith

end
end Yau.Geometry

end OAI
