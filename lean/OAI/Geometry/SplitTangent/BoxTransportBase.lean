import Mathlib
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.RationalTrivialization

namespace OAI

/-! Box Transport Base. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.ReciprocalCharts

def torus : Set (ℂ × ℂ) := {w | w.1 ≠ 0 ∧ w.2 ≠ 0}
lemma torus_open : IsOpen torus :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    (isOpen_ne_fun continuous_snd continuous_const)
lemma torus_dense : Dense torus := by
  exact (dense_compl_singleton (0 : ℂ)).prod (dense_compl_singleton (0 : ℂ))

def coord (b : Bool) (z : ℂ) : ℂ := if b then z⁻¹ else z
def scale (b : Bool) (z : ℂ) : ℂ := if b then -(z^2)⁻¹ else 1
def changeChart (b c : Bool) (w : ℂ × ℂ) : ℂ × ℂ := (coord b w.1,coord c w.2)

lemma coord_involutive (b : Bool) (z : ℂ) : coord b (coord b z) = z := by
  cases b <;> simp [coord]
lemma coord_ne_zero (b : Bool) {z : ℂ} (hz : z ≠ 0) : coord b z ≠ 0 := by
  cases b <;> simpa [coord] using hz
lemma changeChart_involutive (b c : Bool) (w : ℂ × ℂ) :
    changeChart b c (changeChart b c w) = w := by
  simp only [changeChart,coord_involutive]
lemma changeChart_torus (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    changeChart b c w ∈ torus := ⟨coord_ne_zero b hw.1,coord_ne_zero c hw.2⟩
lemma coord_xor (b c : Bool) (z : ℂ) : coord b (coord c z) = coord (Bool.xor b c) z := by
  cases b <;> cases c <;> simp [coord]
lemma changeChart_xor (a b c d : Bool) (w : ℂ × ℂ) :
    changeChart a b (changeChart c d w) = changeChart (Bool.xor a c) (Bool.xor b d) w := by
  simp only [changeChart,coord_xor]
lemma coord_deriv (b : Bool) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (coord b) (scale b z) z := by
  cases b
  · exact hasDerivAt_id z
  · exact hasDerivAt_inv hz
lemma coord_analytic (b : Bool) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (coord b) z := by
  cases b
  · exact analyticAt_id
  · exact analyticAt_id.inv hz
lemma changeChart_analytic (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    AnalyticAt ℂ (changeChart b c) w :=
  ((coord_analytic b hw.1).comp analyticAt_fst).prod
    ((coord_analytic c hw.2).comp analyticAt_snd)
lemma changeChart_fderiv (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    fderiv ℂ (changeChart b c) w =
      (scale b w.1 • ContinuousLinearMap.fst ℂ ℂ ℂ).prod
        (scale c w.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) := by
  have hf := (coord_deriv b hw.1).comp_hasFDerivAt (𝕜 := ℂ) w hasFDerivAt_fst
  have hg := (coord_deriv c hw.2).comp_hasFDerivAt (𝕜 := ℂ) w hasFDerivAt_snd
  exact (hf.prodMk hg).fderiv
lemma changeChart_fderiv_first (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    fderiv ℂ (changeChart b c) w (1,0) = scale b w.1 • (1,0) := by
  rw [changeChart_fderiv b c hw]
  simp
lemma changeChart_fderiv_second (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    fderiv ℂ (changeChart b c) w (0,1) = scale c w.2 • (0,1) := by
  rw [changeChart_fderiv b c hw]
  simp

 
def overlap (a b c d : Bool) : Set (ℂ × ℂ) :=
  {w | (a ≠ c → w.1 ≠ 0) ∧ (b ≠ d → w.2 ≠ 0)}
lemma torus_subset_overlap (a b c d : Bool) : torus ⊆ overlap a b c d :=
  fun _ h => ⟨fun _ => h.1,fun _ => h.2⟩
lemma overlap_open (a b c d : Bool) : IsOpen (overlap a b c d) := by
  change IsOpen ({w : ℂ × ℂ | a ≠ c → w.1 ≠ 0} ∩ {w | b ≠ d → w.2 ≠ 0})
  apply IsOpen.inter
  · by_cases h : a = c
    · simp [h]
    · simpa only [ne_eq,h,not_false_eq_true,true_implies] using isOpen_ne_fun (continuous_fst : Continuous (Prod.fst : ℂ × ℂ → ℂ)) (continuous_const : Continuous (fun _ : ℂ × ℂ => (0 : ℂ)))
  · by_cases h : b = d
    · simp [h]
    · simpa only [ne_eq,h,not_false_eq_true,true_implies] using isOpen_ne_fun (continuous_snd : Continuous (Prod.snd : ℂ × ℂ → ℂ)) (continuous_const : Continuous (fun _ : ℂ × ℂ => (0 : ℂ)))
lemma changeChart_analytic_on_overlap (a b c d : Bool) {w : ℂ × ℂ}
    (hw : w ∈ overlap a b c d) :
    AnalyticAt ℂ (changeChart (Bool.xor a c) (Bool.xor b d)) w := by
  apply AnalyticAt.prod
  · have hf : AnalyticAt ℂ (coord (Bool.xor a c)) w.1 := by
      by_cases h : a = c
      · subst c; simp only [Bool.xor_self]; exact analyticAt_id
      · exact coord_analytic _ (hw.1 h)
    exact hf.comp analyticAt_fst
  · have hf : AnalyticAt ℂ (coord (Bool.xor b d)) w.2 := by
      by_cases h : b = d
      · subst d; simp only [Bool.xor_self]; exact analyticAt_id
      · exact coord_analytic _ (hw.2 h)
    exact hf.comp analyticAt_snd

lemma changeChart_transition (a b c d : Bool) (w : ℂ × ℂ) :
    changeChart c d (changeChart (Bool.xor a c) (Bool.xor b d) w) = changeChart a b w := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [changeChart,coord]

end SplitTangent.ReciprocalCharts

namespace SplitTangent
open Filter Topology Set

 

structure TangentBox {X : ComplexManifold.{u}} (S : TangentSplitting X) (g : RationalCurve X) where
  chart : Bool → Bool → ℂ × ℂ → X.Carrier
  holomorphic : ∀ a b, ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (chart a b)
  overlap : ∀ a b c d w, w ∈ ReciprocalCharts.overlap a b c d →
    chart a b w = chart c d (ReciprocalCharts.changeChart (Bool.xor a c) (Bool.xor b d) w)
  finite_diagonal : ∀ z, chart false false (z,z) = g.finite z
  infinity_diagonal : ∀ z, chart true true (z,z) = g.infinity z
  tangency : ∀ a b w,
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (chart a b) w (1,0) ∈ S.first (chart a b w) ∧
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (chart a b) w (0,1) ∈ S.second (chart a b w)

end SplitTangent

namespace SplitTangent.TangentBox
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (F : TangentBox S g)

 
def firstFactor (b : ℂ) : RationalCurve X where
  finite z := F.chart false false (z,b)
  infinity z := F.chart true false (z,b)
  finite_holomorphic := (F.holomorphic false false).comp
    ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun z : ℂ => (z,b))).contMDiff)
  infinity_holomorphic := (F.holomorphic true false).comp
    ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun z : ℂ => (z,b))).contMDiff)
  overlap z hz := by
    have h := F.overlap false false true false (z,b) ⟨fun _ => hz,by simp⟩
    simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

lemma firstFactor_diagonal (b : ℂ) : (F.firstFactor b).finite b=g.finite b :=
  F.finite_diagonal b

lemma firstFactor_tangent (b z : ℂ) (c : Bool) :
    S.swap.projector (F.chart c false (z,b))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun w : ℂ => F.chart c false (w,b)) z (1 : ℂ))=0 := by
  have hd : HasFDerivAt (fun w : ℂ => (w,b))
      ((ContinuousLinearMap.id ℂ ℂ).prod 0) z :=
    hasFDerivAt_id z |>.prodMk (hasFDerivAt_const b z)
  have hm : MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) (fun w : ℂ => (w,b)) z :=
    hd.differentiableAt.mdifferentiableAt
  have hchain := mfderiv_comp z ((F.holomorphic c false (z,b)).mdifferentiableAt (by simp)) hm
  change S.complementAt _ _=0
  apply (S.mem_first_iff_complement_eq_zero _ _).mp
  change (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) ((F.chart c false) ∘ (fun w : ℂ => (w,b))) z) (1 : ℂ) ∈ _
  rw [hchain,mfderiv_eq_fderiv,hd.fderiv]
  change mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (F.chart c false) (z,b) (1,0) ∈ S.first (F.chart c false (z,b))
  exact (F.tangency c false (z,b)).1

 

theorem exists_normalized_second_map (b : ℂ) :
    ∃ B : CurveBundleMap (F.firstFactor b) (RationalCurve.constant (g.finite b)),
      B.finite b=S.complementAt (g.finite b) := by
  rw [← F.firstFactor_diagonal b]
  exact S.swap.exists_rational_reverse_map (F.firstFactor b)
    (fun z => F.firstFactor_tangent b z false) (fun z => F.firstFactor_tangent b z true) b

end SplitTangent.TangentBox

end

end OAI
