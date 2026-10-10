import Mathlib
import OAI.Analysis.Conductivity.Geometry.CompactRegularBoxCorrection
import OAI.Analysis.Conductivity.Geometry.BoxCoordinateBridge
import OAI.Analysis.Conductivity.Flux.CubeWeakDivergence
import OAI.Analysis.Conductivity.Variational.MatrixCompact

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma cube_weak_divergence_to_coordinates {F₁ F₂ F₃ r : Box3 → ℝ}
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂)
    (h₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₃)
    (hs₁ : HasCompactSupport F₁) (hs₂ : HasCompactSupport F₂) (hs₃ : HasCompactSupport F₃)
    (hd : ∀ p,cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
      cubePartial F₃ ((0,0),1) p=r p)
    (φ : Coord3 → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) :
    (∫ x,fderiv ℝ φ x ![F₁ (boxCoordinates x),F₂ (boxCoordinates x),F₃ (boxCoordinates x)])=
      -(∫ x,φ x*r (boxCoordinates x)) := by
  have he (p w : Box3) : fderiv ℝ (φ∘boxCoordinates.symm) p w=
      fderiv ℝ φ (boxCoordinates.symm p) (boxCoordinates.symm w) := by
    rw [fderiv_comp p (hφ.differentiable (by simp) _) boxCoordinates.symm.differentiableAt,
      boxCoordinates.symm.fderiv]
    rfl
  have h := cube_weak_divergence h₁ h₂ h₃ hs₁ hs₂ hs₃ hd (φ∘boxCoordinates.symm)
    (hφ.comp boxCoordinates.symm.contDiff)
  simp_rw [he,Function.comp_apply] at h
  rw [←boxCoordinates_integral (fun p => fderiv ℝ φ (boxCoordinates.symm p)
    (boxCoordinates.symm ((F₁ p,F₂ p),F₃ p))),
    ←boxCoordinates_integral (fun p => φ (boxCoordinates.symm p)*r p)] at h
  simpa only [boxCoordinates.symm_apply_apply,boxCoordinates_symm_apply] using h

theorem compact_coordinate_box_correction {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    {r₁ r₂ : Box3 → ℝ}
    (hr₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (hr₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hs₁ : HasCompactSupport r₁) (hs₂ : HasCompactSupport r₂)
    (hv₁ : tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hv₂ : tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hz₁ : (∫ p,r₁ p)=0) (hz₂ : (∫ p,r₂ p)=0)
    (ht : (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0) :
    ∃ B : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤ : ℕ∞)) B ∧ HasCompactSupport B ∧
      tsupport B⊆boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)) ∧
      (∀ x,(B x).IsSymm) ∧
      (∀ φ : Coord3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        (∫ x,fderiv ℝ φ x ((B x).col 0))=-(∫ x,φ x*r₁ (boxCoordinates x))) ∧
      (∀ φ : Coord3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        (∫ x,fderiv ℝ φ x ((B x).col 1))=-(∫ x,φ x*r₂ (boxCoordinates x))) := by
  obtain ⟨H,hH,hcH,hsH,hsy,hd₁,hd₂⟩ :=
    compact_regular_box_correction hab hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht
  let B : Coord3 → Mat3 := fun x i j => H i j (boxCoordinates x)
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => (hH i j).comp boxCoordinates.contDiff))
  have hbc : HasCompactSupport B := matrix_hasCompactSupport B (fun i j =>
    (hcH i j).comp_homeomorph boxCoordinates.toHomeomorph)
  have hbs : tsupport B⊆boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)) := by
    apply matrix_tsupport_subset B
    intro i j
    exact (tsupport_comp_subset_preimage (H i j) boxCoordinates.continuous).trans (preimage_mono (hsH i j))
  have hcol (x : Coord3) (j : Fin 3) : (B x).col j=
      ![H 0 j (boxCoordinates x),H 1 j (boxCoordinates x),H 2 j (boxCoordinates x)] := by
    ext i; fin_cases i <;> rfl
  refine ⟨B,hB,hbc,hbs,?_,?_,?_⟩
  · intro x
    ext i j
    exact hsy j i (boxCoordinates x)
  · intro φ hφ
    simp_rw [hcol]
    exact cube_weak_divergence_to_coordinates (hH 0 0) (hH 1 0) (hH 2 0)
      (hcH 0 0) (hcH 1 0) (hcH 2 0) hd₁ φ hφ
  · intro φ hφ
    simp_rw [hcol]
    exact cube_weak_divergence_to_coordinates (hH 0 1) (hH 1 1) (hH 2 1)
      (hcH 0 1) (hcH 1 1) (hcH 2 1) hd₂ φ hφ

end ScalarConductivity

end

end OAI
