import OAI.Analysis.PeriodicLattice.Main

namespace OAI

/-! A rational transverse transformation of the periodic lattice field.
The first direction is ignorable for this field, so its velocity can be
scaled without defining a nonintegral dilation of the circle. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace PeriodicLattice.RapidTorus
open TorusCalculus Quantitative

theorem realRingHomCompTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

theorem spaceContinuousSMul : ContinuousSMul ℝ Space := inferInstance

def transverseLinear : Space →L[ℝ] Space :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  letI := threeAtLeastTwo
  letI := realRingHomCompTriple
  letI := spaceContinuousSMul
  ContinuousLinearMap.id ℝ Space - (3 / 2 : ℝ) •
    ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 1)).comp
      (EuclideanSpace.proj 0))

theorem transverseLinear_apply (x : Space) (i : Fin 3) :
    transverseLinear x i = if i = 0 then -(1 / 2 : ℝ) * x i else x i := by
  change ((x - (3 / 2 : ℝ) • (x 0 • EuclideanSpace.single 0 1)) : Space) i = _
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs with hi
  · subst i
    ring
  · simp

theorem transverseLinear_bound (x : Space) : ‖transverseLinear x‖ ≤ 3 * ‖x‖ := by
  have hs : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space)‖ = 1 := by
    exact (PiLp.norm_single 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) (1 : ℝ)).trans norm_one
  change ‖x - (3 / 2 : ℝ) • (x 0 • EuclideanSpace.single 0 1)‖ ≤ _
  calc
    _ ≤ ‖x‖ + ‖(3 / 2 : ℝ) • (x 0 • EuclideanSpace.single 0 1)‖ := norm_sub_le _ _
    _ = ‖x‖ + (3 / 2 : ℝ) * ‖x 0‖ := by
      simp only [norm_smul, hs, Real.norm_eq_abs]
      norm_num
    _ ≤ ‖x‖ + (3 / 2 : ℝ) * ‖x‖ := by gcongr; exact PiLp.norm_apply_le x 0
    _ ≤ _ := by nlinarith [norm_nonneg x]

def shiftVector : Space :=
  letI := twoAtLeastTwo
  letI := fourAtLeastTwo
  WithLp.toLp 2 ![0, 1 / 4, 0]
def shift (q : Torus) : Torus := q + torusMk shiftVector

def shiftedField {A : Type*} (F : Field A) : Field A := fun t q => F t (shift q)
def transformedField (F : VectorField) : VectorField :=
  fun t q => transverseLinear (shiftedField F t q)

theorem shiftedField_smooth {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) :
    ContDiff ℝ ∞ (lifted (shiftedField F)) := by
  have hg : ContDiff ℝ ∞ (fun tx : ℝ × Space => (tx.1, tx.2 + shiftVector)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  change ContDiff ℝ ∞ (fun tx : ℝ × Space => F tx.1 (torusMk tx.2 + torusMk shiftVector))
  simpa only [lifted, shiftedField, shift, mk_add, Function.comp_def] using hF.comp hg

theorem transformedField_smooth {F : VectorField} (hF : ContDiff ℝ ∞ (lifted F)) :
    ContDiff ℝ ∞ (lifted (transformedField F)) :=
  transverseLinear.contDiff.comp (shiftedField_smooth hF)

theorem shiftedField_spaceD {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (i : Fin 3) :
    spaceD i (shiftedField F) = shiftedField (spaceD i F) := by
  funext t q
  have he : (fun s : ℝ => shiftedField F t (q + torusMk (EuclideanSpace.single i s))) =
      (fun s : ℝ => F t (shift q + torusMk (EuclideanSpace.single i s))) := by
    funext s
    unfold shiftedField shift
    congr 1
    abel
  change deriv (fun s : ℝ => shiftedField F t (q + torusMk (EuclideanSpace.single i s))) 0 = _
  rw [he]
  exact ((hasDerivAt_translation hF t (shift q) i 0).deriv).trans (by
    simp only [single_zero, mk_zero, add_zero, shiftedField])

theorem transformedField_spaceD {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) (i : Fin 3) :
    spaceD i (transformedField F) = transformedField (spaceD i F) := by
  funext t q
  have hd := hasDerivAt_translation (shiftedField_smooth hF) t q i 0
  have hc := transverseLinear.hasFDerivAt.comp_hasDerivAt 0 hd
  change deriv (fun s : ℝ => transverseLinear
    (shiftedField F t (q + torusMk (EuclideanSpace.single i s)))) 0 = _
  simpa only [Function.comp_def, single_zero, mk_zero, add_zero,
    shiftedField_spaceD hF, transformedField] using hc.deriv

theorem transformedField_fullTimeD {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) :
    fullTimeD (transformedField F) = transformedField (fullTimeD F) := by
  funext t q
  have hc := transverseLinear.hasFDerivAt.comp_hasDerivAt t
    (fullTime_hasDerivAt hF t (shift q))
  exact hc.deriv

theorem transformedField_coordD {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) (i : Option (Fin 3)) :
    coordD i (transformedField F) = transformedField (coordD i F) := by
  cases i with
  | none => exact transformedField_fullTimeD hF
  | some j => exact transformedField_spaceD hF j

theorem transformedField_word {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) (w : List (Option (Fin 3))) :
    fieldWord w (transformedField F) = transformedField (fieldWord w F) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [fieldWord_cons, ih, transformedField_coordD (fieldWord_contDiff hF w)]
      rfl

theorem transformedField_meanZero {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) (hm : MeanZero F) : MeanZero (transformedField F) := by
  intro t ht
  have hi : Integrable (fun q => F t (shift q)) torusVolume :=
    ((continuous_iff_lifted (shiftedField F)).mpr (shiftedField_smooth hF).continuous).comp
      (continuous_const.prodMk continuous_id) |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ q, transverseLinear (F t (shift q)) ∂torusVolume) = 0
  rw [transverseLinear.integral_comp_comm hi]
  change transverseLinear (∫ q, F t (q + torusMk shiftVector) ∂torusVolume) = 0
  rw [integral_add_right_eq_self, hm t ht, map_zero]

end PeriodicLattice.RapidTorus

end

end OAI
