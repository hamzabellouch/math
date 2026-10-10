import Mathlib
import OAI.Analysis.Conductivity.Branching.FlatEndingSplice
import OAI.Analysis.Conductivity.Fourier.TorusFourierAnalytic

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusAffineField_analytic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) :
    AnalyticOnNhd ℝ (torusAffineField s κ f) {x | 0<x 0} := by
  exact (analyticOnNhd_const.mul ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).analyticOnNhd _)).add
    (torusRealContinuation_analytic hs f)

lemma branchInitialPair_regular {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) :
    ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion
      (fun y j => torusAffineField s (centralBasisSlopes j i) (f j) y)
      (fun _ => ⟨flatBackgroundTensor s,flatBackgroundTensor_symm s⟩) {x | 0<x 0} := by
  let V := {x : Coord3 | x 0∈Ioo z.d (z.d+z.e)}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_apply 0)
  have hne : V.Nonempty := ⟨![z.d+z.e/2,0,0],by
    change z.d<z.d+z.e/2 ∧ z.d+z.e/2<z.d+z.e
    constructor <;> linarith [z.e_pos]⟩
  obtain ⟨x,hx,hreg⟩  := Measure.exists_mem_of_measure_ne_zero_of_ae (hV.measure_ne_zero volume hne)
    (ae_restrict_of_ae (branchFinitePair i z).regular)
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_regularRegion_iff.mp (hreg hx.1)
  have hvp : ∀ y∈O∩V,0<y 0 := fun y hy => z.d_pos.trans hy.2.1
  apply analyticPair_regular_of_patch (axial_halfspace_open 0) (axial_halfspace_connected 0)
    (fun j => torusAffineField_analytic hs _ _) contDiffOn_const (hO.1.inter hV) hvp ⟨x,hxO,hx⟩
  exact ((hO.2.2.2.mono inter_subset_left).congr (hO.1.inter hV)
    (fun y hy => (branchFinitePair_initial hs i z y hy.2).symm))

theorem branchSpliced_regular {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) :
    ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion
      (fun y j => branchSplicedField i z j y)
      (fun y => ⟨branchSplicedTensor i z y,branchSplicedTensor_symm i z y⟩) {x | 0<x 0} := by
  filter_upwards [branchInitialPair_regular hs i z,(branchFinitePair i z).regular,
    ae_coord3_ne 0 (z.d+5*z.e/8)] with x hi hf hn hx
  by_cases ht : x 0<z.d+5*z.e/8
  · apply mem_regularRegion_congr_nhds (hi hx) ?_ ?_ (axial_halfspace_open 0) hx
    · filter_upwards [Filter.eventually_all.mpr (fun j =>
        branchSplicedField_initial i z hs j (by linarith [z.e_pos] : x 0<z.d+3*z.e/4))] with y hy
      exact funext hy
    · filter_upwards [(isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht] with y hy
      exact Subtype.ext (ite_eq_left hy)
  · have ht' : z.d+5*z.e/8<x 0 := lt_of_le_of_ne (not_lt.mp ht) hn.symm
    apply mem_regularRegion_congr_nhds (hf (by linarith [z.e_pos])) ?_ ?_
      (axial_halfspace_open 0) hx
    · filter_upwards [Filter.eventually_all.mpr (fun j =>
        branchSplicedField_final i z j (by linarith [z.e_pos] : z.d+z.e/2<x 0))] with y hy
      exact funext hy
    · filter_upwards [(axial_halfspace_open (z.d+5*z.e/8)).mem_nhds ht'] with y hy
      exact Subtype.ext (ite_eq_right (not_lt.mpr hy.le))

end ScalarConductivity

end
end

end OAI
