import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalBoxCorrection
import OAI.Analysis.Conductivity.Geometry.CoordinateCorrectionC0
import OAI.Analysis.Conductivity.Flux.LocalTensorBounds

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem physical_box_symmetric_correction_C0
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a b c d : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i)
    (hbox : boxCoordinates ⁻¹' ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2))⊆X.source) :
    ∃ L : ℝ,0<L ∧ ∀ (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ → ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ →
      HasCompactSupport r₁ → HasCompactSupport r₂ →
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r₁ p)=0 → (∫ p,r₂ p)=0 →
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0 → ∀ M : ℝ,0≤M →
      UniformC1Bound r₁ M → UniformC1Bound r₂ M →
    ∃ H : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤ : ℕ∞)) H ∧ HasCompactSupport H ∧ tsupport H⊆X.target ∧
      (∀ y,(H y).IsSymm) ∧
      (∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ (coordinatePair∘X.symm) y)).col j))=
          -(∫ y,ψ y*localPiolaSource X (fun x => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j) y)) ∧
      (∀ y,‖H y‖≤L*M) := by
  let K := boxCoordinates ⁻¹' ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2))
  have hK : IsCompact K := by
    have hc : IsCompact ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) :=
      (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
    convert hc.image boxCoordinates.symm.continuous using 1
    ext x
    constructor
    · intro hx
      exact ⟨boxCoordinates x,hx,boxCoordinates.symm_apply_apply x⟩
    · rintro ⟨p,hp,rfl⟩
      simpa only [K,mem_preimage,boxCoordinates.apply_symm_apply] using hp
  obtain ⟨P,hP,hPi⟩ := localPiolaTensor_linear_bound X hX hXi hK hbox
  obtain ⟨L,hL,solve⟩ := compact_coordinate_box_correction_C0 hab hca hbd
  refine ⟨P*L,mul_pos hP hL,?_⟩
  intro r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  obtain ⟨B,hB,hcB,htB,hsy,hw₁,hw₂,hbB⟩ :=
    solve r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  have hBs : tsupport B⊆X.source := htB.trans hbox
  have hinner : (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)⊆
      (Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2) := by
    intro p hp
    exact ⟨⟨⟨((hca 0).trans hp.1.1.1).le,(hp.1.1.2.trans (hbd 0)).le⟩,
      ⟨((hca 1).trans hp.1.2.1).le,(hp.1.2.2.trans (hbd 1)).le⟩⟩,
      ⟨((hca 2).trans hp.2.1).le,(hp.2.2.trans (hbd 2)).le⟩⟩
  let r : Fin 2 → Coord3 → ℝ := fun j x => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j
  have hcr : ∀ j,HasCompactSupport (r j) := by
    intro j
    fin_cases j
    · exact hs₁.comp_homeomorph boxCoordinates.toHomeomorph
    · exact hs₂.comp_homeomorph boxCoordinates.toHomeomorph
  have hsr : ∀ j,tsupport (r j)⊆X.source := by
    intro j
    fin_cases j
    · exact ((tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans
        (preimage_mono (hv₁.trans hinner))).trans hbox
    · exact ((tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans
        (preimage_mono (hv₂.trans hinner))).trans hbox
  have hweak : ∀ j (φ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ coordinatePair x)).col j))=
        -(∫ x,φ x*r j x) := by
    intro j φ hφ
    simp_rw [coordinatePair_columns]
    fin_cases j
    · exact hw₁ φ hφ
    · exact hw₂ φ hφ
  refine ⟨localPiolaTensor X B,localPiolaTensor_smooth X hX hXi B hB hcB hBs,
    (localPiolaTensor_compact X B hcB hBs).1,(localPiolaTensor_compact X B hcB hBs).2,
    localPiolaTensor_isSymm X B hsy,?_,?_⟩
  · intro j ψ hψ
    simp_rw [localPiolaTensor_columns X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) B coordinatePair
      (coordinatePair_smooth.differentiable (by simp)).differentiableOn]
    have htj := tensorColumn_tsupport B (fun x => gradientColumns (fderiv ℝ coordinatePair x)) j
    exact localPiolaFlux_weak_source volume X hX hXi _ _
      (hcB.of_isClosed_subset isClosed_closure htj) (hcr j) (htj.trans hBs) (hsr j) (hweak j) ψ hψ
  · intro y
    exact (hPi B ((subset_tsupport B).trans htB) y).trans
      ((mul_le_mul_of_nonneg_left (hbB _) hP.le).trans_eq (by ring))

end ScalarConductivity

end
end

end OAI
