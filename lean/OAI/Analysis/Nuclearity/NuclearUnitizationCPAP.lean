import OAI.Analysis.Nuclearity.UnitizedCPMap
import OAI.Analysis.Nuclearity.CPBlockSum
import OAI.Analysis.PureInfiniteness.ScalarComplement
import OAI.Analysis.Nuclearity.UnitalCPContraction
import OAI.Analysis.Nuclearity.UnitizedTensorElementary

namespace OAI

/-! Matrix approximations of the unitization. An extra matrix block records
the scalar coordinate, so the return map fixes the adjoined unit exactly. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

private abbrev Mat (n : ℕ) := CStarMatrix (Fin n) (Fin n) ℂ
private abbrev Block (n : ℕ) := CStarMatrix (Fin 2) (Fin 2) (Mat n)

local instance nuMatOrder {n : ℕ} : PartialOrder (Mat n) := CStarAlgebra.spectralOrder _
local instance nuMatOrdered {n : ℕ} : StarOrderedRing (Mat n) := CStarAlgebra.spectralOrderedRing _
local instance nuBlockOrder {n : ℕ} : PartialOrder (Block n) := CStarAlgebra.spectralOrder _
local instance nuBlockOrdered {n : ℕ} : StarOrderedRing (Block n) := CStarAlgebra.spectralOrderedRing _
local instance nuUnitMatOrder {n : ℕ} : PartialOrder (Unitization ℂ (Mat n)) :=
  CStarAlgebra.spectralOrder _
local instance nuUnitMatOrdered {n : ℕ} : StarOrderedRing (Unitization ℂ (Mat n)) :=
  CStarAlgebra.spectralOrderedRing _

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local instance nuUnitOrder : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
local instance nuUnitOrdered : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _

private def scalarMatrixHom (n : ℕ) : Unitization ℂ A →⋆ₙₐ[ℂ] Mat n :=
  (matrixDiagonalHom (n := Fin n)).comp unitizationScalarHom

private def unitizedMatrixCompression {n : ℕ} (φ : A →L[ℂ] Mat n) :
    Unitization ℂ A →L[ℂ] Block n :=
  (starHomContinuousLinear (twoCornerInclusion 0)).comp (unitizedCPLinear φ) +
    (starHomContinuousLinear (twoCornerInclusion 1)).comp
      (starHomContinuousLinear (scalarMatrixHom n))

private def unitizedMatrixReturn (n : ℕ) (i : Fin n) :
    Block n →L[ℂ] Unitization ℂ (Mat n) :=
  (starHomContinuousLinear (Unitization.inrNonUnitalStarAlgHom ℂ (Mat n))).comp
      (matrixCornerLinear 0) +
    (starHomContinuousLinear (scalarComplementHom (D := Mat n))).comp
      ((matrixCornerLinear i).comp (matrixCornerLinear 1))

omit [PartialOrder A] [StarOrderedRing A] in
private lemma scalarMatrixHom_entry (n : ℕ) (x : Unitization ℂ A) (i j : Fin n) :
    scalarMatrixHom n x i j = if i = j then x.fst else 0 := rfl

omit [PartialOrder A] [StarOrderedRing A] in
private lemma unitizedMatrixCompression_apply {n : ℕ} (φ : A →L[ℂ] Mat n)
    (x : Unitization ℂ A) :
    unitizedMatrixCompression φ x = twoCornerInclusion 0 (unitizedCPLinear φ x) +
      twoCornerInclusion 1 (scalarMatrixHom n x) := rfl

private lemma unitizedMatrixReturn_apply (n : ℕ) (i : Fin n) (M : Block n) :
    unitizedMatrixReturn n i M = (Unitization.inr (M 0 0) : Unitization ℂ (Mat n)) +
      (M 1 1 i i) • (1 - Unitization.inr (1 : Mat n)) := rfl

private lemma unitizedMatrixCompression_cp {n : ℕ} (φ : A →L[ℂ] Mat n)
    (hφ : CompletelyPositive φ) (hn : ‖φ‖ ≤ 1) :
    CompletelyPositive (unitizedMatrixCompression φ) := by
  apply completelyPositive_add
  · exact completelyPositive_comp _ _ (unitizedCPLinear_cp φ hφ hn)
      (starHomContinuous_completelyPositive _)
  · exact completelyPositive_comp _ _ (starHomContinuous_completelyPositive _)
      (starHomContinuous_completelyPositive _)

omit [PartialOrder A] [StarOrderedRing A] in
private lemma unitizedMatrixCompression_one {n : ℕ} (φ : A →L[ℂ] Mat n) :
    unitizedMatrixCompression φ 1 = 1 := by
  rw [unitizedMatrixCompression_apply, unitizedCPLinear_one]
  have hs : scalarMatrixHom (A := A) n 1 = 1 := by
    ext i j
    rw [scalarMatrixHom_entry, CStarMatrix.one_apply]
    rfl
  rw [hs]
  apply CStarMatrix.ext
  intro i j
  change (if i = 0 ∧ j = 0 then (1 : Mat n) else 0) +
    (if i = 1 ∧ j = 1 then (1 : Mat n) else 0) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;> simp

private lemma unitizedMatrixReturn_cp (n : ℕ) (i : Fin n) :
    CompletelyPositive (unitizedMatrixReturn n i) := by
  apply completelyPositive_add
  · exact completelyPositive_comp _ _ (matrixCornerLinear_cp 0)
      (starHomContinuous_completelyPositive _)
  · exact completelyPositive_comp _ _
      (completelyPositive_comp _ _ (matrixCornerLinear_cp 1) (matrixCornerLinear_cp i))
      (starHomContinuous_completelyPositive _)

private lemma unitizedMatrixReturn_one (n : ℕ) (i : Fin n) :
    unitizedMatrixReturn n i 1 = 1 := by
  rw [unitizedMatrixReturn_apply]
  simp

omit [PartialOrder A] [StarOrderedRing A] in
private lemma unitizedMatrixReturn_compression {n : ℕ} (i : Fin n)
    (φ : A →L[ℂ] Mat n) (x : Unitization ℂ A) :
    unitizedMatrixReturn n i (unitizedMatrixCompression φ x) =
      (Unitization.inr (φ x.snd) : Unitization ℂ (Mat n)) + x.fst • 1 := by
  rw [unitizedMatrixReturn_apply]
  have h0 : unitizedMatrixCompression φ x 0 0 = unitizedCPLinear φ x := by
    rw [unitizedMatrixCompression_apply, CStarMatrix.add_apply]
    simp only [twoCornerInclusion_apply]
    simp
  have h1 : unitizedMatrixCompression φ x 1 1 = scalarMatrixHom n x := by
    rw [unitizedMatrixCompression_apply, CStarMatrix.add_apply]
    simp only [twoCornerInclusion_apply]
    simp
  rw [h0, h1, scalarMatrixHom_entry, ite_eq_left rfl]
  change (Unitization.inr (φ x.snd + x.fst • (1 : Mat n)) : Unitization ℂ (Mat n)) +
    x.fst • (1 - Unitization.inr (1 : Mat n)) = _
  rw [Unitization.inr_add, Unitization.inr_smul, smul_sub]
  abel

private lemma clm_comp_norm_le_one {X Y Z : Type*}
    [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y] [SeminormedAddCommGroup Z]
    [NormedSpace ℂ X] [NormedSpace ℂ Y] [NormedSpace ℂ Z]
    (f : X →L[ℂ] Y) (g : Y →L[ℂ] Z) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    ‖g.comp f‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hg hf (norm_nonneg f) zero_le_one).trans_eq (mul_one 1))

/-- Nuclear matrix approximations extend to the forced unitization. -/
theorem nuclear_unitization_cpap (hA : Nuclear A) : Nuclear (Unitization ℂ A) := by
  classical
  intro F ε hε
  obtain ⟨n, hn, φ, ψ, hφ, hψ, hφn, hψn, happ⟩ := hA (F.image (fun x : Unitization ℂ A => x.snd)) ε hε
  let i : Fin n := ⟨0, by omega⟩
  let ψ' := (starHomContinuousLinear (Unitization.inrNonUnitalStarAlgHom ℂ A)).comp ψ
  have hψ' : CompletelyPositive ψ' := completelyPositive_comp _ _ hψ
    (starHomContinuous_completelyPositive _)
  have hψ'n : ‖ψ'‖ ≤ 1 := clm_comp_norm_le_one _ _ hψn
    (starHomContinuousLinear_norm_le_one _)
  let P := starHomContinuousLinear (twoMatrixPack n)
  let Q := starHomContinuousLinear (twoMatrixUnpack n)
  let Φ := P.comp (unitizedMatrixCompression φ)
  let R := (unitizedCPLinear ψ').comp (unitizedMatrixReturn n i)
  let Ψ := R.comp Q
  have hcomp := unitizedMatrixCompression_cp φ hφ hφn
  have hret := unitizedMatrixReturn_cp n i
  have hΦ : CompletelyPositive Φ := completelyPositive_comp _ _ hcomp
    (starHomContinuous_completelyPositive _)
  have hR : CompletelyPositive R := completelyPositive_comp _ _ hret
    (unitizedCPLinear_cp ψ' hψ' hψ'n)
  have hΨ : CompletelyPositive Ψ := completelyPositive_comp _ _
    (starHomContinuous_completelyPositive _) hR
  have hRn : ‖R‖ ≤ 1 := completelyPositive_norm_le_of_unital hR (by
    change unitizedCPLinear ψ' (unitizedMatrixReturn n i 1) = 1
    rw [unitizedMatrixReturn_one, unitizedCPLinear_one])
  have hΦn : ‖Φ‖ ≤ 1 := clm_comp_norm_le_one _ _
    (completelyPositive_norm_le_of_unital hcomp (unitizedMatrixCompression_one φ))
    (starHomContinuousLinear_norm_le_one _)
  have hΨn : ‖Ψ‖ ≤ 1 := clm_comp_norm_le_one _ _
    (starHomContinuousLinear_norm_le_one _) hRn
  refine ⟨2 * n, by omega, Φ, Ψ, hΦ, hΨ, hΦn, hΨn, ?_⟩
  intro x hx
  have hv : Ψ (Φ x) = (Unitization.inr (ψ (φ x.snd)) : Unitization ℂ A) + x.fst • 1 := by
    change unitizedCPLinear ψ'
      (unitizedMatrixReturn n i (twoMatrixUnpack n (twoMatrixPack n (unitizedMatrixCompression φ x)))) = _
    rw [twoMatrixUnpack_pack, unitizedMatrixReturn_compression, map_add, map_smul,
      unitizedCPLinear_inr, unitizedCPLinear_one]
    rfl
  have he : Ψ (Φ x) - x = (Unitization.inr (ψ (φ x.snd) - x.snd) : Unitization ℂ A) := by
    rw [hv]
    apply Unitization.ext
    · change (0 + x.fst * 1) - x.fst = 0
      ring
    · change (ψ (φ x.snd) + x.fst • (0 : A)) - x.snd = ψ (φ x.snd) - x.snd
      simp
  rw [he, Unitization.norm_inr]
  exact happ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

end WeakPureInfiniteness

end

end OAI
