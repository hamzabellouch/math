import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.RegularTorus

namespace OAI

/-! Two plane sections, transition matrices and associated charts. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k] [Infinite k]

noncomputable def planeXSection (x : planeTorusPoints k) : SL2 k :=
  ⟨!![x.val 0, 0; x.val 1, (x.val 0)⁻¹], by
    simp [Matrix.det_fin_two, x.property 0]⟩

noncomputable def planeYSection (x : planeTorusPoints k) : SL2 k :=
  ⟨!![x.val 0, -(x.val 1)⁻¹; x.val 1, 0], by
    simp [Matrix.det_fin_two, x.property 1]⟩

noncomputable def planeChartCoordinate (i j : Fin 2) : planeCoordinateChart k i :=
  algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i) (MvPolynomial.X j)

noncomputable def planeChartInverse (i : Fin 2) : planeCoordinateChart k i :=
  IsLocalization.Away.invSelf (S := planeCoordinateChart k i) (MvPolynomial.X i : MvPolynomial (Fin 2) k)

omit [Infinite k] in
lemma planeChartEvaluation_coordinate (i j : Fin 2) (x : planeTorusPoints k) :
    planeChartEvaluation k i (planeChartCoordinate k i j) x = x.val j := by
  rw [planeChartCoordinate, planeChartEvaluation_algebraMap,
    planeTorusEvaluation_apply, MvPolynomial.eval_X]

omit [Infinite k] in
lemma planeChartEvaluation_inverse (i : Fin 2) (x : planeTorusPoints k) :
    planeChartEvaluation k i (planeChartInverse k i) x = (x.val i)⁻¹ := by
  have hmul : planeChartCoordinate k i i * planeChartInverse k i = 1 :=
    IsLocalization.Away.mul_invSelf (S := planeCoordinateChart k i) (MvPolynomial.X i : MvPolynomial (Fin 2) k)
  have h := congrFun (congrArg (planeChartEvaluation k i) hmul) x
  simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply,
    planeChartEvaluation_coordinate] at h
  exact mul_left_cancel₀ (x.property i) (h.trans (mul_inv_cancel₀ (x.property i)).symm)

noncomputable def planeXPolynomialChart :
    MvPolynomial (Fin 2 × Fin 2) k →ₐ[k] planeCoordinateChart k 0 :=
  MvPolynomial.aeval (fun ij =>
    (!![planeChartCoordinate k 0 0, 0;
      planeChartCoordinate k 0 1, planeChartInverse k 0]) ij.1 ij.2)

noncomputable def planeYPolynomialChart :
    MvPolynomial (Fin 2 × Fin 2) k →ₐ[k] planeCoordinateChart k 1 :=
  MvPolynomial.aeval (fun ij =>
    (!![planeChartCoordinate k 1 0, -planeChartInverse k 1;
      planeChartCoordinate k 1 1, 0]) ij.1 ij.2)

omit [Infinite k] in
lemma planeXPolynomialChart_evaluation (P : MvPolynomial (Fin 2 × Fin 2) k)
    (x : planeTorusPoints k) :
    planeChartEvaluation k 0 (planeXPolynomialChart k P) x =
      coordinateEvaluation k P (planeXSection k x) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [planeXPolynomialChart, coordinateEvaluation]
  | add P Q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X P i hp =>
    simp only [map_mul, Pi.mul_apply, hp]
    congr 1
    rw [coordinateEvaluation_apply, MvPolynomial.eval_X]
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [planeXPolynomialChart, planeXSection,
        planeChartEvaluation_coordinate, planeChartEvaluation_inverse]

omit [Infinite k] in
lemma planeYPolynomialChart_evaluation (P : MvPolynomial (Fin 2 × Fin 2) k)
    (x : planeTorusPoints k) :
    planeChartEvaluation k 1 (planeYPolynomialChart k P) x =
      coordinateEvaluation k P (planeYSection k x) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [planeYPolynomialChart, coordinateEvaluation]
  | add P Q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X P i hp =>
    simp only [map_mul, Pi.mul_apply, hp]
    congr 1
    rw [coordinateEvaluation_apply, MvPolynomial.eval_X]
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [planeYPolynomialChart, planeYSection,
        planeChartEvaluation_coordinate, planeChartEvaluation_inverse]

noncomputable def regularXChartValue (f : regularSL2Functions k) : planeCoordinateChart k 0 :=
  planeXPolynomialChart k f.property.choose

omit [Infinite k] in
lemma regularXChartValue_evaluation (f : regularSL2Functions k) (x : planeTorusPoints k) :
    planeChartEvaluation k 0 (regularXChartValue k f) x = f.val (planeXSection k x) := by
  rw [regularXChartValue, planeXPolynomialChart_evaluation]
  exact congrFun f.property.choose_spec _

noncomputable def regularXChart : regularSL2Functions k →ₐ[k] planeCoordinateChart k 0 where
  toFun := regularXChartValue k
  map_zero' := by
    apply planeChartEvaluation_injective k 0
    ext x
    rw [regularXChartValue_evaluation, map_zero]
    rfl
  map_one' := by
    apply planeChartEvaluation_injective k 0
    ext x
    rw [regularXChartValue_evaluation, map_one]
    rfl
  map_add' f h := by
    apply planeChartEvaluation_injective k 0
    ext x
    rw [map_add, Pi.add_apply, regularXChartValue_evaluation,
      regularXChartValue_evaluation, regularXChartValue_evaluation]
    rfl
  map_mul' f h := by
    apply planeChartEvaluation_injective k 0
    ext x
    rw [map_mul, Pi.mul_apply, regularXChartValue_evaluation,
      regularXChartValue_evaluation, regularXChartValue_evaluation]
    rfl
  commutes' a := by
    apply planeChartEvaluation_injective k 0
    ext x
    rw [regularXChartValue_evaluation, AlgHom.commutes]
    rfl

noncomputable def regularYChartValue (f : regularSL2Functions k) : planeCoordinateChart k 1 :=
  planeYPolynomialChart k f.property.choose

omit [Infinite k] in
lemma regularYChartValue_evaluation (f : regularSL2Functions k) (x : planeTorusPoints k) :
    planeChartEvaluation k 1 (regularYChartValue k f) x = f.val (planeYSection k x) := by
  rw [regularYChartValue, planeYPolynomialChart_evaluation]
  exact congrFun f.property.choose_spec _

noncomputable def regularYChart : regularSL2Functions k →ₐ[k] planeCoordinateChart k 1 where
  toFun := regularYChartValue k
  map_zero' := by
    apply planeChartEvaluation_injective k 1
    ext x
    rw [regularYChartValue_evaluation, map_zero]
    rfl
  map_one' := by
    apply planeChartEvaluation_injective k 1
    ext x
    rw [regularYChartValue_evaluation, map_one]
    rfl
  map_add' f h := by
    apply planeChartEvaluation_injective k 1
    ext x
    rw [map_add, Pi.add_apply, regularYChartValue_evaluation,
      regularYChartValue_evaluation, regularYChartValue_evaluation]
    rfl
  map_mul' f h := by
    apply planeChartEvaluation_injective k 1
    ext x
    rw [map_mul, Pi.mul_apply, regularYChartValue_evaluation,
      regularYChartValue_evaluation, regularYChartValue_evaluation]
    rfl
  commutes' a := by
    apply planeChartEvaluation_injective k 1
    ext x
    rw [regularYChartValue_evaluation, AlgHom.commutes]
    rfl

end

universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma planeSections_transition (x : planeTorusPoints k) :
    planeYSection k x = planeXSection k x * unipotent k (-(x.val 0 * x.val 1)⁻¹) := by
  apply Subtype.ext
  ext i j
  change _ = ((planeXSection k x : Matrix (Fin 2) (Fin 2) k) *
    (unipotent k (-(x.val 0 * x.val 1)⁻¹) : Matrix (Fin 2) (Fin 2) k)) i j
  fin_cases i <;> fin_cases j <;>
    simp [planeXSection, planeYSection, unipotent, Matrix.mul_apply,
      Fin.sum_univ_two, x.property]
  field_simp [x.property 0, x.property 1]

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma sl2_xSection_decomposition (g : SL2 k) (ha : g 0 0 ≠ 0) (hc : g 1 0 ≠ 0) :
    g = planeXSection k ⟨fun i => g i 0, by intro i; fin_cases i; exact ha; exact hc⟩ *
      unipotent k (g 0 1 / g 0 0) := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  ext i j
  change (g : Matrix (Fin 2) (Fin 2) k) i j =
    ((planeXSection k _ : Matrix (Fin 2) (Fin 2) k) *
    (unipotent k (g 0 1 / g 0 0) : Matrix (Fin 2) (Fin 2) k)) i j
  fin_cases i <;> fin_cases j <;>
    simp [planeXSection, unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · apply (mul_left_cancel₀ ha)
    field_simp
    linear_combination hd

noncomputable def associatedXChart :
    (associatedSectionsSubmodule k ι ρ) →ₗ[k] (ι → planeCoordinateChart k 0) where
  toFun f i := regularXChart k (f.val i)
  map_add' := by intro f h; funext i; exact map_add _ _ _
  map_smul' := by intro a f; funext i; exact (regularXChart k).toLinearMap.map_smul a (f.val i)

noncomputable def associatedYChart :
    (associatedSectionsSubmodule k ι ρ) →ₗ[k] (ι → planeCoordinateChart k 1) where
  toFun f i := regularYChart k (f.val i)
  map_add' := by intro f h; funext i; exact map_add _ _ _
  map_smul' := by intro a f; funext i; exact (regularYChart k).toLinearMap.map_smul a (f.val i)

omit [Fintype ι] [DecidableEq ι] in
lemma associatedXChart_evaluation (f : associatedSectionsSubmodule k ι ρ)
    (x : planeTorusPoints k) :
    (fun i => planeChartEvaluation k 0 (associatedXChart k ι ρ f i) x) =
      regularVectorEvaluation k ι (planeXSection k x) f.val := by
  funext i
  exact regularXChartValue_evaluation k (f.val i) x

omit [Fintype ι] [DecidableEq ι] in
lemma associatedYChart_evaluation (f : associatedSectionsSubmodule k ι ρ)
    (x : planeTorusPoints k) :
    (fun i => planeChartEvaluation k 1 (associatedYChart k ι ρ f i) x) =
      regularVectorEvaluation k ι (planeYSection k x) f.val := by
  funext i
  exact regularYChartValue_evaluation k (f.val i) x

omit [Fintype ι] [DecidableEq ι] in
lemma associatedCharts_transition (f : associatedSectionsSubmodule k ι ρ)
    (x : planeTorusPoints k) :
    (fun i => planeChartEvaluation k 1 (associatedYChart k ι ρ f i) x) =
      ρ (Multiplicative.ofAdd ((x.val 0 * x.val 1)⁻¹))
        (fun i => planeChartEvaluation k 0 (associatedXChart k ι ρ f i) x) := by
  rw [associatedYChart_evaluation, associatedXChart_evaluation, planeSections_transition]
  simpa only [neg_neg] using f.property (planeXSection k x) (-(x.val 0 * x.val 1)⁻¹)

omit [Fintype ι] [DecidableEq ι] in
lemma associatedXChart_injective : Function.Injective (associatedXChart k ι ρ) := by
  intro f h he
  apply Subtype.ext
  funext i
  apply sub_eq_zero.mp
  apply regularSL2_torus_dense k
  intro g ha hc
  let x : planeTorusPoints k := ⟨fun j => g j 0, by intro j; fin_cases j; exact ha; exact hc⟩
  have hf' : regularVectorEvaluation k ι (planeXSection k x) f.val =
      regularVectorEvaluation k ι (planeXSection k x) h.val := by
    rw [← associatedXChart_evaluation, ← associatedXChart_evaluation, he]
  have heq := f.property (planeXSection k x) (g 0 1 / g 0 0)
  have heq' := h.property (planeXSection k x) (g 0 1 / g 0 0)
  rw [← sl2_xSection_decomposition k g ha hc, hf'] at heq
  rw [← sl2_xSection_decomposition k g ha hc] at heq'
  exact sub_eq_zero.mpr (congrFun (heq.trans heq'.symm) i)

end FiberFunctorProof

 

open scoped BigOperators
end

end OAI
