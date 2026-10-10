import Mathlib
import OAI.Geometry.WeakHessian.Measure.LocalizedTestCutoff

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile168
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma exists_compact_lipschitz_plateau {E U : Set X} (hE : IsCompact E) (hU : IsOpen U)
    (hEU : E ⊆ U) :
    ∃ f : X → ℝ,GloballyLipschitz f ∧ HasCompactSupport f ∧
      (∀ x,0 ≤ f x ∧ f x ≤ 1) ∧ tsupport f ⊆ U ∧
      ∃ V : Set X,IsOpen V ∧ E ⊆ V ∧ ∀ x ∈ V,f x = 1 := by
  by_cases hEn : E.Nonempty
  swap
  · have he : E = ∅ := not_nonempty_iff_eq_empty.mp hEn
    refine ⟨fun _ => 0,⟨0,LipschitzWith.const 0⟩,?_,fun _ => ⟨le_rfl,zero_le_one⟩,?_,∅,isOpen_empty,?_,?_⟩
    · simp [HasCompactSupport]
    · simp
    · simp [he]
    · simp
  obtain ⟨δ,hδ,hδU⟩ := hE.exists_cthickening_subset_open hU hEU
  let c : ℝ := 2/δ
  have hc : 0 < c := by dsimp [c]; positivity
  have hce : c*δ = 2 := by dsimp [c]; field_simp
  let f (x : X) : ℝ := rootClip 1 (2-c*Metric.infDist x E)
  have hfl : LipschitzWith ‖c‖₊ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (f x) (f y) ≤ dist (2-c*Metric.infDist x E) (2-c*Metric.infDist y E) := by
        simpa only [NNReal.coe_one,one_mul,f] using
          (rootClip_lipschitz 1).dist_le_mul (2-c*Metric.infDist x E) (2-c*Metric.infDist y E)
      _ = |c| *dist (Metric.infDist x E) (Metric.infDist y E) := by
        rw [dist_sub_left,Real.dist_eq,← mul_sub,abs_mul,Real.dist_eq]
      _ ≤ |c| *dist x y := mul_le_mul_of_nonneg_left
        (by simpa using (Metric.lipschitz_infDist_pt E).dist_le_mul x y) (abs_nonneg c)
  have hs : tsupport f ⊆ Metric.cthickening δ E := by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    apply Metric.thickening_subset_cthickening δ E
    apply (Metric.mem_thickening_iff_infDist_lt hEn).mpr
    by_contra HH
    have hge : δ ≤ Metric.infDist x E := le_of_not_gt HH
    have hraw : 2-c*Metric.infDist x E ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left hge hc.le]
    exact hx (show f x = 0 from max_eq_left ((min_le_right 1 _).trans hraw))
  refine ⟨f,⟨_,hfl⟩,(hE.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport f) hs,
    fun x => ⟨rootClip_nonneg _ _,rootClip_le zero_le_one _⟩,hs.trans hδU,
    Metric.thickening (δ/2) E,Metric.isOpen_thickening,
    Metric.self_subset_thickening (by positivity) E,?_⟩
  intro x hx
  have hh := (Metric.mem_thickening_iff_infDist_lt hEn).mp hx
  have hraw : 1 ≤ 2-c*Metric.infDist x E := by nlinarith [mul_le_mul_of_nonneg_left hh.le hc.le]
  simp only [f,rootClip,min_eq_left hraw,max_eq_right zero_le_one]

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_test_cutoff_in_open {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {E U : Set X} (hE : IsCompact E) (hU : IsOpen U) (hEU : E ⊆ U) :
    ∃ χ : X → ℝ,IsTestFunction m χ ∧ HasCompactSupport χ ∧
      (∀ x,0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ U ∧
      (∃ V : Set X,IsOpen V ∧ E ⊆ V ∧ ∀ x ∈ V,χ x = 1) ∧
      ∃ B : ℝ,∀ᵐ x ∂m,|laplacian m χ x| ≤ B := by
  obtain ⟨f,hf,hfc,hfb,hfU,V,hV,hEV,hfV⟩ := exists_compact_lipschitz_plateau hE hU hEU
  obtain ⟨χ,hχ,hχc,hχb,hχf,hχ1,B,hB⟩ := hrcd.exists_test_cutoff_of_compact_lipschitz hN hfull hfin o hf.choose_spec hfc
  exact ⟨χ,hχ,hχc,hχb,hχf.trans hfU,⟨V,hV,hEV,fun x hx => hχ1 x (hfV x hx)⟩,B,hB⟩
end WeakHessian

end
end InlinedFile168

end OAI
