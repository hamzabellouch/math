import OAI.Analysis.TriangularHilbert.ErrorEnvelope

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma errorOutput_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (i j : D) :
    ‖kernelOutput (A 1) (A 2) h (fun m => h*(m:ℤ)) (fun a b => endpointError (r a b)) i j‖ ≤
      envelopeConstant*meshMassConstant*jumpMax D A i j := by
  have hri := hh.trans_le (hr i j)
  have hs : h^2 ≤ 6*(r i j)^2 := by have hr' := hr i j; nlinarith [sq_nonneg (r i j),sq_nonneg h]
  have hed (k : D) : h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ) = h*((((k:ℤ)-(-(i:ℤ)-(j:ℤ))):ℤ):ℝ) := by
    push_cast
    ring
  have h1 := gaussian_sum_le_lineMax D (fun k => ‖A 1 j k‖^2) (fun _ => sq_nonneg _) hh hs (-(i:ℤ)-(j:ℤ))
  have h2 := gaussian_sum_le_lineMax D (fun k => ‖A 2 k i‖^2) (fun _ => sq_nonneg _) hh hs (-(i:ℤ)-(j:ℤ))
  simp_rw [← hed] at h1 h2
  unfold kernelOutput
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k, envelopeConstant*(‖A 1 j k‖^2+‖A 2 k i‖^2)*
        (h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hh.le,Real.norm_eq_abs]
      have hp : ‖A 1 j k‖*‖A 2 k i‖ ≤ ‖A 1 j k‖^2+‖A 2 k i‖^2 := by nlinarith [sq_nonneg (‖A 1 j k‖-‖A 2 k i‖)]
      have hg := endpointError_bound hri (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))
      calc
        _ ≤ h*‖A 1 j k‖*‖A 2 k i‖*(envelopeConstant*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by gcongr
        _ = envelopeConstant*(‖A 1 j k‖*‖A 2 k i‖)*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp envelopeConstant_pos.le)
          (mul_nonneg hh.le (density_nonneg (by positivity) _))
    _ = envelopeConstant*((∑ k, ‖A 1 j k‖^2*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))))+
        (∑ k, ‖A 2 k i‖^2*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))))) := by
      simp only [mul_assoc,mul_add,add_mul,Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ envelopeConstant*(meshMassConstant*lineMax D (fun k => ‖A 1 j k‖^2) (-(i:ℤ)-(j:ℤ))+
        meshMassConstant*lineMax D (fun k => ‖A 2 k i‖^2) (-(i:ℤ)-(j:ℤ))) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) envelopeConstant_pos.le
    _ ≤ _ := by
      unfold jumpMax
      have h0 := lineMax_nonneg D (fun k => ‖A 0 i k‖^2) (fun _ => sq_nonneg _) (j:ℤ)
      have h3 := lineMax_nonneg D (fun k => ‖A 0 k j‖^2) (fun _ => sq_nonneg _) (i:ℤ)
      have hC := envelopeConstant_pos
      have hM := meshMassConstant_pos
      nlinarith [mul_nonneg (mul_nonneg hC.le hM.le) h0,mul_nonneg (mul_nonneg hC.le hM.le) h3]

def errorPairingConstant : ℝ := envelopeConstant*meshMassConstant*jumpScalarConstant
lemma errorPairingConstant_pos : 0 < errorPairingConstant :=
  mul_pos (mul_pos envelopeConstant_pos meshMassConstant_pos) jumpScalarConstant_pos

lemma errorPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => endpointError (r i j))‖ ≤
      errorPairingConstant*arrayCubic A h := by
  unfold kernelPairing
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, ∑ j, h^2*‖A 0 i j‖*(envelopeConstant*meshMassConstant*jumpMax D A i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg h)]
      exact mul_le_mul_of_nonneg_left (errorOutput_le D A hh r hr i j) (by positivity)
    _ = envelopeConstant*meshMassConstant*h^2*(∑ i, ∑ j, ‖A 0 i j‖*jumpMax D A i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ envelopeConstant*meshMassConstant*h^2*(jumpScalarConstant*(∑ v,∑ i,∑ j,‖A v i j‖^3)) :=
      mul_le_mul_of_nonneg_left (sum_jumpMax_le D A) (mul_nonneg (mul_nonneg envelopeConstant_pos.le meshMassConstant_pos.le) (sq_nonneg h))
    _ = _ := by
      unfold errorPairingConstant arrayCubic
      simp only [← Finset.mul_sum]
      ring
end
end TriangularHilbert.Heat
end

end OAI
