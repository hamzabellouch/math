import OAI.NumberTheory.JointDickman.Amplification.RationalArcSeparation
import OAI.NumberTheory.JointDickman.Amplification.MinorArcMeasurable

namespace OAI

/-! # The measurable major-arc partition of the exact Fourier integral -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

noncomputable def majorArcRegion (B j : ℕ) (X : ℝ) : Set ℝ :=
  {θ | θ ∈ Ioc 0 1 ∧ InRationalArc (-(j : ℝ)*θ) ((B : ℝ)^12) ((B : ℝ)^13/X)}

noncomputable def rationalArcPiece (B j : ℕ) (X : ℝ) (r : ℚ) : Set ℝ :=
  {θ | θ ∈ Ioc 0 1 ∧ (r.den : ℝ) ≤ (B : ℝ)^12 ∧
    |-(j : ℝ)*θ-(r : ℝ)| ≤ (B : ℝ)^13/X}

theorem majorArcRegion_eq_iUnion (B j : ℕ) (X : ℝ) :
    majorArcRegion B j X = ⋃ r : ℚ, rationalArcPiece B j X r := by
  ext θ
  simp only [majorArcRegion,rationalArcPiece,mem_ofPred_eq,mem_iUnion,InRationalArc]
  aesop

theorem rationalArcPiece_measurable (B j : ℕ) (X : ℝ) (r : ℚ) :
    MeasurableSet (rationalArcPiece B j X r) := by
  by_cases hr : (r.den : ℝ) ≤ (B : ℝ)^12
  · have hs : MeasurableSet {θ : ℝ | |-(j : ℝ)*θ-(r : ℝ)| ≤ (B : ℝ)^13/X} :=
      (isClosed_le ((continuous_const.mul continuous_id).sub continuous_const).abs
        continuous_const).measurableSet
    convert (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)).inter hs using 1
    ext θ
    simp [rationalArcPiece,hr]
  · simp [rationalArcPiece,hr]

theorem majorArcRegion_measurable (B j : ℕ) (X : ℝ) :
    MeasurableSet (majorArcRegion B j X) := by
  rw [majorArcRegion_eq_iUnion]
  exact MeasurableSet.iUnion (rationalArcPiece_measurable B j X)

theorem majorMinor_partition (B j : ℕ) (X : ℝ) :
    majorArcRegion B j X ∪ minorArcRegion B j X = Ioc 0 1 := by
  ext θ
  simp only [majorArcRegion,minorArcRegion,mem_union,mem_ofPred_eq]
  tauto

theorem majorMinor_disjoint (B j : ℕ) (X : ℝ) :
    Disjoint (majorArcRegion B j X) (minorArcRegion B j X) := by
  rw [disjoint_left]
  intro θ hmaj hmin
  exact hmin.2 hmaj.2

theorem majorMinor_integral (B j : ℕ) (X : ℝ) {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ θ in (0 : ℝ)..1, F θ) =
      (∫ θ in majorArcRegion B j X, F θ)+(∫ θ in minorArcRegion B j X, F θ) := by
  have hI : IntegrableOn F (Ioc 0 1) := (hF.intervalIntegrable 0 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← majorMinor_partition B j X]
  exact setIntegral_union (majorMinor_disjoint B j X) (minorArcRegion_measurable B j X)
    (hI.mono_set (fun _ h => h.1)) (hI.mono_set (minorArcRegion_subset B j X))

theorem rationalArcPiece_pairwise :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X → ∀ j : ℕ,
      Pairwise (Disjoint on (rationalArcPiece B j X)) := by
  filter_upwards [majorArc_rational_unique] with B hB
  intro X hX hlog j r s hrs
  change Disjoint (rationalArcPiece B j X r) (rationalArcPiece B j X s)
  rw [disjoint_left]
  intro θ hr hs
  exact hrs (hB X hX hlog (-(j : ℝ)*θ) r s hr.2.1 hs.2.1 hr.2.2 hs.2.2)

theorem majorArc_integral_sum :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X → ∀ j : ℕ,
      ∀ F : ℝ → ℂ, Continuous F →
      (∫ θ in majorArcRegion B j X, F θ) =
        ∑' r : ℚ, ∫ θ in rationalArcPiece B j X r, F θ := by
  filter_upwards [rationalArcPiece_pairwise] with B hB
  intro X hX hlog j F hF
  rw [majorArcRegion_eq_iUnion]
  apply integral_iUnion (rationalArcPiece_measurable B j X) (hB X hX hlog j)
  apply ((hF.intervalIntegrable (μ := volume) 0 1).1).mono_set
  intro θ hθ
  obtain ⟨r,hr⟩ := mem_iUnion.mp hθ
  exact hr.1

end JointDickman

end OAI
