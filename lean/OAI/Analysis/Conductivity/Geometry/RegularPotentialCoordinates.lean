import Mathlib
import OAI.Analysis.Conductivity.Sources.LocalPhysicalCorrection

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def potentialCompletion (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) : Mat3 :=
  ![(gradientColumns D).col 0,(gradientColumns D).col 1,
    crossProduct ((gradientColumns D).col 0) ((gradientColumns D).col 1)]

lemma potentialCompletion_det_ne_zero (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (hD : Function.Surjective D) : (potentialCompletion D).det≠0 := by
  have hc : crossProduct ((gradientColumns D).col 0) ((gradientColumns D).col 1)≠0 := by
    apply crossProduct_ne_zero_iff_linearIndependent.mpr
    have he : ![(gradientColumns D).col 0,(gradientColumns D).col 1] =
        (gradientColumns D).col := by
      ext j i
      fin_cases j <;> rfl
    rw [he]
    exact gradientColumns_rank D hD
  rw [potentialCompletion,←triple_product_eq_det,
    triple_product_permutation ((gradientColumns D).col 0),
    triple_product_permutation ((gradientColumns D).col 1)]
  exact mt dotProduct_self_eq_zero.mp hc

lemma potentialCompletion_pairing (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) (x : Coord3) :
    coordinatePair (potentialCompletion D*ᵥx)=D x := by
  rw [←gradientColumns_apply D x]
  ext j
  fin_cases j <;> rfl

def potentialCompletionEquiv (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (hD : Function.Surjective D) : Coord3 ≃L[ℝ] Coord3 :=
  (LinearMap.equivOfDetNeZero (Matrix.toLin' (potentialCompletion D))
    (by rw [LinearMap.det_toLin']; exact potentialCompletion_det_ne_zero D hD)).toContinuousLinearEquiv

lemma potentialCompletionEquiv_pairing (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (hD : Function.Surjective D) (x : Coord3) :
    coordinatePair (potentialCompletionEquiv D hD x)=D x :=
  potentialCompletion_pairing D x

theorem exists_regular_potential_coordinates
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (a : Coord3) (hD : Function.Surjective (fderiv ℝ u a))
    {U : Set Coord3} (hU : IsOpen U) (ha : a∈U) :
    ∃ X : OpenPartialHomeomorph Coord3 Coord3,
      a∈X.target ∧ X.target⊆U ∧
      ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) X.symm ∧
      u=coordinatePair∘X.symm := by
  obtain ⟨Y,haY,hYU,hY,hYi,he,hder⟩ := exists_potential_chart hu a hD hU ha
  let L : Coord3 ≃L[ℝ] Coord3 := potentialCompletionEquiv (fderiv ℝ u a) hD
  let Z := Y.transHomeomorph L.toHomeomorph
  refine ⟨Z.symm,haY,hYU,?_,?_,?_⟩
  · change ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun z => Y.symm (L.symm z)) {z | L.symm z∈Y.target}
    exact hYi.comp L.symm.contDiff.contDiffOn (fun _ hx => hx)
  · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => L (Y z))
    exact L.contDiff.comp hY
  · funext x
    exact (he x).symm.trans (potentialCompletionEquiv_pairing _ hD (Y x)).symm

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma mem_correctionBox {a b x : Coord3} : x∈correctionBox a b ↔ ∀ i,a i<x i ∧ x i<b i := by
  constructor
  · rintro ⟨⟨h0,h1⟩,h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0,h 1⟩,h 2⟩

lemma correctionBox_isOpen (a b : Coord3) : IsOpen (correctionBox a b) :=
  ((isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo).preimage boxCoordinates.continuous

lemma exists_correctionBox_inside {U : Set Coord3} (hU : IsOpen U) {x : Coord3} (hx : x∈U) :
    ∃ a b : Coord3,(∀ i,a i<b i) ∧ x∈correctionBox a b ∧ correctionBox a b⊆U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨fun i => x i-ε,fun i => x i+ε,fun i => by linarith,
    mem_correctionBox.mpr (fun i => by constructor <;> linarith),?_⟩
  intro y hy
  apply hball
  rw [Metric.mem_ball,dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq,abs_lt]
  have hi := mem_correctionBox.mp hy i
  constructor <;> linarith

structure RegularCorrectionBox (u : Coord3 → Fin 2 → ℝ) (U : Set Coord3) where
  chart : OpenPartialHomeomorph Coord3 Coord3
  lower : Coord3
  upper : Coord3
  widths : ∀ i,lower i<upper i
  subset_source : correctionBox lower upper⊆chart.source
  smooth : ContDiffOn ℝ (↑(⊤:ℕ∞)) chart chart.source
  inverse_smooth : ContDiffOn ℝ (↑(⊤:ℕ∞)) chart.symm chart.target
  potentials : EqOn u (coordinatePair∘chart.symm) chart.target
  target_subset : chart.target⊆U

namespace RegularCorrectionBox
variable {u : Coord3 → Fin 2 → ℝ} {U : Set Coord3}
def region (B : RegularCorrectionBox u U) : Set Coord3 :=
  B.chart '' correctionBox B.lower B.upper

lemma region_open (B : RegularCorrectionBox u U) : IsOpen B.region :=
  B.chart.isOpen_image_of_subset_source (correctionBox_isOpen _ _) B.subset_source

lemma region_target (B : RegularCorrectionBox u U) : B.region⊆B.chart.target := by
  rintro y ⟨x,hx,rfl⟩
  exact B.chart.map_source (B.subset_source hx)

lemma region_subset (B : RegularCorrectionBox u U) : B.region⊆U :=
  B.region_target.trans B.target_subset

lemma region_nonempty (B : RegularCorrectionBox u U) : B.region.Nonempty := by
  refine ⟨B.chart (fun i => (B.lower i+B.upper i)/2),
    (fun i => (B.lower i+B.upper i)/2),?_,rfl⟩
  exact mem_correctionBox.mpr (fun i => by have := B.widths i; constructor <;> linarith)

end RegularCorrectionBox

theorem exists_regular_correction_box
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U : Set Coord3} (hU : IsOpen U) {p : Coord3} (hp : p∈U)
    (hD : Function.Surjective (fderiv ℝ u p)) :
    ∃ B : RegularCorrectionBox u U,p∈B.region := by
  obtain ⟨X,hpX,hXU,hX,hXi,he⟩ := exists_regular_potential_coordinates hu p hD hU hp
  obtain ⟨a,b,hab,hx,hs⟩ := exists_correctionBox_inside X.open_source (X.map_target hpX)
  let B : RegularCorrectionBox u U := ⟨X,a,b,hab,hs,hX,hXi.contDiffOn,fun _ _ => congrFun he _,hXU⟩
  exact ⟨B,X.symm p,hx,X.right_inv hpX⟩

end ScalarConductivity

end

end OAI
