import Mathlib
import OAI.Analysis.Conductivity.Geometry.CoordinateWeakCorrection
import OAI.Analysis.Conductivity.Variational.CompactRegularC0

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem compact_coordinate_box_correction_C0 {a b c d : Fin 3 → ℝ}
    (hab : ∀ i,a i<b i) (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i) :
    ∃ L : ℝ,0<L ∧ ∀ (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ → ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ →
      HasCompactSupport r₁ → HasCompactSupport r₂ →
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r₁ p)=0 → (∫ p,r₂ p)=0 →
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0 → ∀ M : ℝ,0≤M →
      UniformC1Bound r₁ M → UniformC1Bound r₂ M →
    ∃ B : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤ : ℕ∞)) B ∧ HasCompactSupport B ∧
      tsupport B⊆boxCoordinates ⁻¹' ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) ∧
      (∀ x,(B x).IsSymm) ∧
      (∀ φ : Coord3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        (∫ x,fderiv ℝ φ x ((B x).col 0))=-(∫ x,φ x*r₁ (boxCoordinates x))) ∧
      (∀ φ : Coord3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        (∫ x,fderiv ℝ φ x ((B x).col 1))=-(∫ x,φ x*r₂ (boxCoordinates x))) ∧
      (∀ x,‖B x‖≤L*M) := by
  obtain ⟨L,hL,solve⟩ := compact_regular_box_correction_C0 hab hca hbd
  refine ⟨L,hL,?_⟩
  intro r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  obtain ⟨H,hH,hcH,hsH,hsy,hd₁,hd₂,hbH⟩ :=
    solve r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  let B : Coord3 → Mat3 := fun x i j => H i j (boxCoordinates x)
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => (hH i j).comp boxCoordinates.contDiff))
  have hbc : HasCompactSupport B := matrix_hasCompactSupport B (fun i j =>
    (hcH i j).comp_homeomorph boxCoordinates.toHomeomorph)
  have hbs : tsupport B⊆boxCoordinates ⁻¹' ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) := by
    apply matrix_tsupport_subset B
    intro i j
    exact (tsupport_comp_subset_preimage (H i j) boxCoordinates.continuous).trans (preimage_mono (hsH i j))
  have hcol (x : Coord3) (j : Fin 3) : (B x).col j=
      ![H 0 j (boxCoordinates x),H 1 j (boxCoordinates x),H 2 j (boxCoordinates x)] := by
    ext i; fin_cases i <;> rfl
  refine ⟨B,hB,hbc,hbs,?_,?_,?_,?_⟩
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

  · intro x
    apply Matrix.norm_le_iff (mul_nonneg hL.le hM) |>.mpr
    intro i j
    exact hbH i j (boxCoordinates x)

end ScalarConductivity

end
end

end OAI
