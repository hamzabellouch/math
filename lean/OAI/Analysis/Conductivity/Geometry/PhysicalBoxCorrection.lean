import Mathlib
import OAI.Analysis.Conductivity.Geometry.CoordinateWeakCorrection
import OAI.Analysis.Conductivity.Sources.LocalPiola

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

def coordinatePairCLM : Coord3 →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (j.castLE (by decide : 2≤3)))

def coordinatePair : Coord3 → Fin 2 → ℝ := coordinatePairCLM

lemma coordinatePair_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) coordinatePair :=
  coordinatePairCLM.contDiff

@[simp] lemma coordinatePair_zero (x : Coord3) : coordinatePair x 0=x 0 := rfl
@[simp] lemma coordinatePair_one (x : Coord3) : coordinatePair x 1=x 1 := rfl

lemma coordinatePair_columns (B : Mat3) (x : Coord3) (j : Fin 2) :
    (B*gradientColumns (fderiv ℝ coordinatePair x)).col j=(B.col (j.castLE (by decide : 2≤3))) := by
  have hd : fderiv ℝ coordinatePair x=coordinatePairCLM := coordinatePairCLM.hasFDerivAt.fderiv
  rw [hd]
  ext i
  fin_cases j
  all_goals simp [Matrix.mul_apply,gradientColumns,LinearMap.toMatrix',
    coordinatePairCLM,Matrix.transpose_apply,Matrix.col,Pi.single_apply]

theorem physical_box_symmetric_correction
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (hbox : boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))⊆X.source)
    {r₁ r₂ : Box3 → ℝ}
    (hr₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (hr₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hs₁ : HasCompactSupport r₁) (hs₂ : HasCompactSupport r₂)
    (hv₁ : tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hv₂ : tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hz₁ : (∫ p,r₁ p)=0) (hz₂ : (∫ p,r₂ p)=0)
    (ht : (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0) :
    ∃ H : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤ : ℕ∞)) H ∧ HasCompactSupport H ∧ tsupport H⊆X.target ∧
      (∀ y,(H y).IsSymm) ∧
      ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ (coordinatePair∘X.symm) y)).col j))=
          -(∫ y,ψ y*localPiolaSource X (fun x => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j) y) := by
  obtain ⟨B,hB,hcB,htB,hsy,hw₁,hw₂⟩ :=
    compact_coordinate_box_correction hab hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht
  apply local_symmetric_source_transport X hX hXi B hB hcB (htB.trans hbox) hsy
    coordinatePair coordinatePair_smooth.contDiffOn
  · intro j
    fin_cases j
    · exact hs₁.comp_homeomorph boxCoordinates.toHomeomorph
    · exact hs₂.comp_homeomorph boxCoordinates.toHomeomorph
  · intro j
    fin_cases j
    · exact ((tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans (preimage_mono hv₁)).trans hbox
    · exact ((tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans (preimage_mono hv₂)).trans hbox
  · intro j ψ hψ
    simp_rw [coordinatePair_columns]
    fin_cases j
    · exact hw₁ ψ hψ
    · exact hw₂ ψ hψ

end ScalarConductivity

end

end OAI
