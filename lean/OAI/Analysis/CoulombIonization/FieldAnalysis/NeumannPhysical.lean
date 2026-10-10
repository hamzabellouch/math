import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannWeak
import OAI.Analysis.CoulombIonization.Variational.ConfigurationCoordinates

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

def cartesianValue (ψ : FormVector N) (s : Spins N) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  ψ.value s ((configurationCoordinates N).symm x)

def cartesianGradient (ψ : FormVector N) (s : Spins N) (q : Fin N × Fin 3)
    (x : (Fin N × Fin 3) → ℝ) : ℂ := ψ.gradient s q.1 q.2 ((configurationCoordinates N).symm x)

lemma SobolevFermion.cartesian_anti {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    FlatAEAntisymmetric (cartesianValue ψ) := by
  intro π s
  filter_upwards [(configurationCoordinates_symm_preserving N).quasiMeasurePreserving.ae
    (hψ.2.2.2 π s)] with x hx
  simpa only [cartesianValue,configurationCoordinates_permute] using hx

lemma SobolevFermion.cartesian_weak {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (q : Fin N × Fin 3) (φ : ((Fin N × Fin 3) → ℝ) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, cartesianValue ψ s x * Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
      -(∫ x, cartesianGradient ψ s q x*(φ x:ℂ)) := by
  have hh := hψ.2.2.1 s q.1 q.2 (fun y => φ (configurationCoordinates N y))
    (hφ.comp (configurationCoordinates N).contDiff)
    (hc.comp_homeomorph (configurationCoordinates N).toHomeomorph)
  have hd (x : Configuration N) :
      lineDeriv ℝ (fun y => φ (configurationCoordinates N y)) x (direction q.1 q.2) =
        lineDeriv ℝ φ (configurationCoordinates N x) (Pi.single q 1) := by
    exact lineDeriv_flattenConfiguration φ x q.1 q.2
  simp only [hd] at hh
  calc
    _ = ∫ x : Configuration N, cartesianValue ψ s (configurationCoordinates N x) *
        Complex.ofReal (lineDeriv ℝ φ (configurationCoordinates N x) (Pi.single q 1)) :=
      (integral_configurationCoordinates (fun x => cartesianValue ψ s x *
        Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1)))).symm
    _ = -(∫ x : Configuration N, cartesianGradient ψ s q (configurationCoordinates N x) *
        (φ (configurationCoordinates N x):ℂ)) := by
      simpa only [cartesianValue,cartesianGradient,ContinuousLinearEquiv.symm_apply_apply] using hh
    _ = _ := congrArg Neg.neg (integral_configurationCoordinates (fun x => cartesianGradient ψ s q x*(φ x:ℂ)))

theorem SobolevFermion.neumann_unit_grid {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    tfKinetic*(∑ s : Spins N, ∫ x : Configuration N,
      cellPressure (pointCell (flattenConfiguration N x))*‖ψ.value s x‖^2) ≤
      formKinetic ψ +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  have hm (s : Spins N) : MemLp (cartesianValue ψ s) 2 :=
    (hψ.1 s).comp_measurePreserving (configurationCoordinates_symm_preserving N)
  have hg (s : Spins N) (q : Fin N × Fin 3) : MemLp (cartesianGradient ψ s q) 2 :=
    (hψ.2.1 s q.1 q.2).comp_measurePreserving (configurationCoordinates_symm_preserving N)
  have hh := neumann_global_weak hm hg hψ.cartesian_anti hψ.cartesian_weak
  have he (s : Spins N) :
      (∫ x, cellPressure (pointCell x)*‖cartesianValue ψ s x‖^2) =
        ∫ x : Configuration N, cellPressure (pointCell (flattenConfiguration N x))*‖ψ.value s x‖^2 := by
    rw [←integral_configurationCoordinates (fun x => cellPressure (pointCell x)*‖cartesianValue ψ s x‖^2)]
    change (∫ x : Configuration N, cellPressure (pointCell (configurationCoordinates N x))*
      ‖ψ.value s ((configurationCoordinates N).symm (configurationCoordinates N x))‖^2) = _
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have heg (s : Spins N) (q : Fin N × Fin 3) :
      (∫ x, ‖cartesianGradient ψ s q x‖^2) = ∫ x, ‖ψ.gradient s q.1 q.2 x‖^2 :=
    integral_configurationCoordinates_symm (fun x => ‖ψ.gradient s q.1 q.2 x‖^2)
  have hem (s : Spins N) : (∫ x, ‖cartesianValue ψ s x‖^2) = ∫ x, ‖ψ.value s x‖^2 :=
    integral_configurationCoordinates_symm (fun x => ‖ψ.value s x‖^2)
  simp_rw [he,heg,hem] at hh
  simpa only [Fintype.sum_prod_type,formKinetic,formMass] using hh

theorem FormAdmissible.neumann_unit_grid {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    tfKinetic*(∑ s : Spins N, ∫ x : Configuration N,
      cellPressure (pointCell (flattenConfiguration N x))*‖ψ.value s x‖^2) ≤
      formKinetic ψ+neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) := by
  have hh := hψ.sobolevFermion.neumann_unit_grid
  unfold formMass at hh
  simpa only [hψ.2.2.2.2.1,mul_one] using hh

end CoulombAtom

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace CoulombNeumann
open CoulombAtom

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma memLp_comp_real_smul {f : E → ℂ} {p : ENNReal} (hf : MemLp f p)
    {b : ℝ} (hb : b ≠ 0) : MemLp (fun x => f (b • x)) p := by
  apply MemLp.comp_of_map (f := fun x : E => b • x) _ ((continuous_id.const_smul b).measurable.aemeasurable)
  rw [Measure.map_addHaar_smul volume hb]
  exact hf.smul_measure (by simp)

lemma memLp_comp_affine {f : E → ℂ} {p : ENNReal} (hf : MemLp f p)
    {b : ℝ} (hb : b ≠ 0) (t : E) : MemLp (fun x => f (b • x+t)) p := by
  exact memLp_comp_real_smul (hf.comp_measurePreserving (measurePreserving_add_right volume t)) hb

lemma integral_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) {b : ℝ} (hb : 0 < b) (t : E) :
    (∫ x, f (b • x+t)) = (b ^ Module.finrank ℝ E)⁻¹ • ∫ x, f x := by
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => f (x+t)) b (hR := hb.le),
    integral_add_right_eq_self]

end Affine
variable {N : ℕ}

def gridTranslation (t : Fin 3 → ℝ) : (Fin N × Fin 3) → ℝ := fun q => t q.2

def affineGrid (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :=
  b • x + gridTranslation t

def affineGridInv (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :=
  b⁻¹ • (x-gridTranslation t)

@[simp] lemma affineGridInv_affineGrid {b : ℝ} (hb : b ≠ 0) (t : Fin 3 → ℝ)
    (x : (Fin N × Fin 3) → ℝ) : affineGridInv b t (affineGrid b t x) = x := by
  simp [affineGridInv,affineGrid,smul_smul,hb]

@[simp] lemma affineGrid_affineGridInv {b : ℝ} (hb : b ≠ 0) (t : Fin 3 → ℝ)
    (x : (Fin N × Fin 3) → ℝ) : affineGrid b t (affineGridInv b t x) = x := by
  simp [affineGridInv,affineGrid,smul_smul,hb]

lemma affineGrid_anti {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (ha : FlatAntisymmetric f) (b : ℝ) (t : Fin 3 → ℝ) :
    FlatAntisymmetric (fun s x => f s (affineGrid b t x)) := by
  intro i j hij s x
  convert ha i j hij s (affineGrid b t x) using 1
  congr 1

lemma affineGrid_contDiff (b : ℝ) (t : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (affineGrid (N := N) b t) := by
  change ContDiff ℝ ∞ (fun x : (Fin N × Fin 3) → ℝ => b • x + gridTranslation t)
  exact (contDiff_id.const_smul b).add contDiff_const

lemma affineGrid_fderiv {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    fderiv ℝ (fun y => f (affineGrid b t y)) x (Pi.single q 1) =
      b • fderiv ℝ f (affineGrid b t x) (Pi.single q 1) := by
  have h := (hf.differentiable (by simp) (affineGrid b t x)).hasFDerivAt.comp x
    (((hasFDerivAt_id x).const_smul b).add_const (gridTranslation t))
  have hh := congrArg (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv
  simpa only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,Function.comp_def] using hh

def gridPressure (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) : ℝ :=
  b⁻¹^2 * cellPressure (pointCell (affineGridInv b t x))

lemma gridPressure_nonneg (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :
    0 ≤ gridPressure b t x := mul_nonneg (sq_nonneg _) (cellPressure_nonneg _)

lemma gridPressure_bound (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :
    gridPressure b t x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) :=
  mul_le_mul_of_nonneg_left (cellPressure_le _) (sq_nonneg _)

lemma gridPressure_measurable (b : ℝ) (t : Fin 3 → ℝ) :
    Measurable (gridPressure (N := N) b t) := by
  apply measurable_const.mul
  apply flatPressure_measurable.comp
  change Measurable (fun x : (Fin N × Fin 3) → ℝ => b⁻¹ • (x-gridTranslation t))
  exact ((continuous_id.sub continuous_const).const_smul b⁻¹).measurable

lemma gridPressure_integrable {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : MemLp f 2)
    (b : ℝ) (t : Fin 3 → ℝ) : Integrable (fun x => gridPressure b t x*‖f x‖^2) := by
  apply hf.norm.integrable_sq.bdd_mul (gridPressure_measurable b t).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (gridPressure_nonneg b t x)]
    exact gridPressure_bound b t x)

theorem neumann_affine_smooth_component
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (ha : FlatAntisymmetric f)
    (hm : ∀ s, MemLp (f s) 2)
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) (s : Fin N → Fin 2) :
    tfKinetic*(∫ x, gridPressure b t x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x, ‖f s x‖^2) := by
  have hf' (s) : ContDiff ℝ 1 (fun x => f s (affineGrid b t x)) :=
    (hf s).comp ((affineGrid_contDiff b t).of_le (by simp))
  have hm' (s) : MemLp (fun x => f s (affineGrid b t x)) 2 :=
    memLp_comp_affine (hm s) hb.ne' _
  have hg' (s) (q : Fin N × Fin 3) : MemLp
      (fun x => fderiv ℝ (fun y => f s (affineGrid b t y)) x (Pi.single q 1)) 2 := by
    simp_rw [affineGrid_fderiv (hf s)]
    exact (memLp_comp_affine (hg s q) hb.ne' _).const_smul b
  have hh := neumann_global_smooth_component hf' (affineGrid_anti ha b t) hm' hg' s
  let J : ℝ := (b ^ Module.finrank ℝ ((Fin N × Fin 3) → ℝ))⁻¹
  have hJ : 0 < J := inv_pos.mpr (pow_pos hb _)
  have he : (∫ x, cellPressure (pointCell x)*‖f s (affineGrid b t x)‖^2) =
      J*b^2*(∫ x, gridPressure b t x*‖f s x‖^2) := by
    have hh := integral_comp_affine (fun x => gridPressure b t x*‖f s x‖^2) hb (gridTranslation t)
    change (∫ x, gridPressure b t (affineGrid b t x)*‖f s (affineGrid b t x)‖^2) = J * _ at hh
    have he (x : (Fin N × Fin 3) → ℝ) : gridPressure b t (affineGrid b t x) =
        b⁻¹^2*cellPressure (pointCell x) := by
      simp only [gridPressure,affineGridInv_affineGrid hb.ne']
    simp only [he,mul_assoc,integral_const_mul] at hh
    have hh' := congrArg (fun v : ℝ => b^2*v) hh
    convert hh' using 1 <;> field_simp [hb.ne']
  have heK (q : Fin N × Fin 3) :
      (∫ x, ‖fderiv ℝ (fun y => f s (affineGrid b t y)) x (Pi.single q 1)‖^2) =
      b^2*J*(∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) := by
    simp_rw [affineGrid_fderiv (hf s),norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
    have hh := integral_comp_affine (fun x => ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) hb (gridTranslation t)
    change (∫ x, ‖fderiv ℝ (f s) (affineGrid b t x) (Pi.single q 1)‖^2) = J * _ at hh
    rw [hh,mul_assoc]
  have heM : (∫ x, ‖f s (affineGrid b t x)‖^2) = J*(∫ x, ‖f s x‖^2) :=
    by
      simpa only [affineGrid,smul_eq_mul] using integral_comp_affine (fun x => ‖f s x‖^2) hb (gridTranslation t)
  simp_rw [he,heK,heM,←Finset.mul_sum] at hh
  apply (mul_le_mul_iff_right₀ (mul_pos hJ (sq_pos_of_pos hb))).mp
  calc
    _ = tfKinetic*(J*b^2*(∫ x, gridPressure b t x*‖f s x‖^2)) := by ring
    _ ≤ (1/2:ℝ)*(b^2*J*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2)) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(J*(∫ x, ‖f s x‖^2)) := hh
    _ = _ := by field_simp [hb.ne']

end CoulombNeumann

end

end OAI
