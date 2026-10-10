import Mathlib
import OAI.MathematicalPhysics.BFSS.WeightedGradients
import OAI.MathematicalPhysics.BFSS.ProfileMoments

namespace OAI

/-! Gauge-invariant kinetic density and measured normal kinetic estimates. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Finset
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] coreToL2 charge bracketPart normalSlice

def kineticDensity (f : SmoothCore N) (x : Boson N) : ℝ :=
  ∑ p : SpaceIndex × ColorIndex N, ‖coordinateDerivative p.1 p.2 f x‖^2

lemma kineticDensity_integral (f : SmoothCore N) :
    (∫ x, kineticDensity f x) =
      ∑ p : SpaceIndex × ColorIndex N, ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 := by
  simp only [kineticDensity,coreToL2_norm_sq]
  exact integral_finsetSum _ (fun p _ => coreNormSq_integrable _)

lemma normalCoreField_kinetic_le (q : Boson N) {h : ℝ} (hh : 0 < h)
    (f : SmoothCore N) (z : M.normalSlice q) :
    (∑ j, ‖fderiv ℝ (M.normalCoreField q h f) z
      (stdOrthonormalBasis ℝ (M.normalSlice q) j)‖^2) ≤
      (h^M.orbitDimension q)⁻¹ * kineticDensity f (h⁻¹ • q+(z : Boson N)) := by
  have hl := BFSSSliceAnalytic.affine_kinetic_le (M.normalSlice q)
    (EuclideanSpace.basisFun (SpaceIndex × ColorIndex N) ℝ)
    (stdOrthonormalBasis ℝ (M.normalSlice q)) (h⁻¹ • q)
    (Real.sqrt ((h^M.orbitDimension q)⁻¹)) f (f.contDiff.differentiable (by simp)) z
  rw [Real.sq_sqrt (inv_nonneg.mpr (pow_nonneg hh.le _))] at hl
  unfold normalCoreField kineticDensity
  simp only [coordinateDerivative_apply]
  simpa only [EuclideanSpace.basisFun_apply,Prod.mk.eta] using hl
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Finset
variable {N : ℕ} {M : AlgebraData N}
attribute [local irreducible] coreToL2 charge bracketPart normalSlice gaugeAction

lemma kineticDensity_continuous (f : SmoothCore N) : Continuous (kineticDensity f) := by
  exact continuous_finsetSum _ (fun p _ => (coordinateDerivative p.1 p.2 f).continuous.norm.pow 2)

lemma kineticDensity_nonneg (f : SmoothCore N) (x : Boson N) : 0 ≤ kineticDensity f x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma kineticDensity_compactSupport (f : SmoothCore N) : HasCompactSupport (kineticDensity f) := by
  have hk := (f.hasCompactSupport.fderiv ℝ).comp_left
    (g := fun L : Boson N →L[ℝ] Fermion N => ∑ p : SpaceIndex × ColorIndex N,
      ‖L (EuclideanSpace.single p 1)‖^2) (by simp)
  have he : kineticDensity f = (fun L : Boson N →L[ℝ] Fermion N =>
      ∑ p : SpaceIndex × ColorIndex N, ‖L (EuclideanSpace.single p 1)‖^2) ∘ fderiv ℝ (f : Boson N → Fermion N) := by
    funext x
    simp only [kineticDensity,coordinateDerivative_apply,Function.comp_apply,Prod.mk.eta]
  rw [he]
  exact hk

namespace GaugeData
variable (G : M.GaugeData)

lemma invariantCore_kineticDensity (f : G.invariantCore) (g : GaugeGroup N) (x : Boson N) :
    kineticDensity f.val (G.boson g x) = kineticDensity f.val x := by
  let e := EuclideanSpace.basisFun (SpaceIndex × ColorIndex N) ℝ
  have hb := BFSSSliceAnalytic.kinetic_basis_independent e (e.map (G.boson g))
    (fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x))
  have he (i : SpaceIndex × ColorIndex N) :
      ‖fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x) ((e.map (G.boson g)) i)‖ =
      ‖fderiv ℝ (f.val : Boson N → Fermion N) x (e i)‖ := by
    rw [OrthonormalBasis.map_apply,G.invariantCore_fderiv,(G.fermion g).norm_map]
  simp_rw [he] at hb
  simpa only [kineticDensity,coordinateDerivative_apply,e,EuclideanSpace.basisFun_apply,Prod.mk.eta] using hb.symm

lemma invariantCore_kineticDensity_unitary (hN : 2 ≤ N) (f : G.invariantCore)
    (U : unitary (ColorMatrix N)) (x : Boson N) :
    kineticDensity f.val (M.gaugeAction U x) = kineticDensity f.val x := by
  obtain ⟨g,hg⟩ := G.unitary_boson_exists hN U
  rw [←hg x]
  exact G.invariantCore_kineticDensity f g x
end GaugeData
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set Finset
variable {N : ℕ} {M : AlgebraData N}
attribute [local irreducible] coreToL2 charge bracketPart normalSlice gaugeAction normalCoreField

def normalKineticDensity (q : Boson N) (h : ℝ) (f : SmoothCore N) (z : M.normalSlice q) : ℝ :=
  ∑ j, ‖fderiv ℝ (M.normalCoreField q h f) z
    (stdOrthonormalBasis ℝ (M.normalSlice q) j)‖^2

lemma normalKineticDensity_continuous (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    Continuous (normalKineticDensity (M := M) q h f) := by
  apply continuous_finsetSum
  intro j _
  exact ((((M.normalCoreField_contDiff q h f).continuous_fderiv (by simp)).clm_apply
    continuous_const).norm.pow 2)

lemma normalKineticDensity_compactSupport (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    HasCompactSupport (normalKineticDensity (M := M) q h f) := by
  have hk := (M.normalCoreField_compactSupport q h f).fderiv ℝ
  have ht := hk.comp_left (g := fun L : M.normalSlice q →L[ℝ] Fermion N =>
    ∑ j, ‖L (stdOrthonormalBasis ℝ (M.normalSlice q) j)‖^2) (by simp)
  exact ht

namespace GaugeData
variable (G : M.GaugeData)

lemma slice_kinetic_integral_le (hN : 2 ≤ N) (q : Boson N)
    (J : M.normalSlice q → ℝ) (V : Set (Boson N))
    (hJ : Continuous J) (hJn : ∀ z, 0 ≤ J z)
    (hm : ∀ h : ℝ, 0 < h → ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
      (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
      (∀ x ∈ Function.support F, h • x ∈ V) →
      (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
        ∫ z : M.normalSlice q, J (h • z)*F (h⁻¹ • q+(z : Boson N)))
    {h : ℝ} (hh : 0 < h) (φ : Boson N → ℝ) (hφ : Continuous φ)
    (hφn : ∀ x, 0 ≤ φ x)
    (hφi : ∀ U : unitary (ColorMatrix N), ∀ x, φ (M.gaugeAction U x) = φ x)
    (hφs : Function.support φ ⊆ V) (f : G.invariantCore) :
    (∫ z : M.normalSlice q, J (h • z)*φ (q+h • (z : Boson N))*
        normalKineticDensity q h f.val z) ≤
      ∫ x, φ (h • x)*kineticDensity f.val x := by
  let F : Boson N → ℝ := fun x => φ (h • x)*kineticDensity f.val x
  have hsm : Continuous (fun x : Boson N => h • x) :=
    Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_id
  have hFc : Continuous F := (hφ.comp hsm).mul (kineticDensity_continuous f.val)
  have hFK : HasCompactSupport F := (kineticDensity_compactSupport f.val).mul_left
  have hFi (U : unitary (ColorMatrix N)) (x : Boson N) : F (M.gaugeAction U x) = F x := by
    dsimp [F]
    rw [←M.gaugeAction_smul,hφi,G.invariantCore_kineticDensity_unitary hN]
  have hFs (x : Boson N) (hx : x ∈ Function.support F) : h • x ∈ V := by
    apply hφs
    intro hz
    exact hx (by simp only [F,hz,zero_mul])
  have hmeasure := hm h hh F hFc hFK hFi hFs
  change (∫ z, _) ≤ ∫ x, F x
  rw [hmeasure,←integral_const_mul]
  have hzs : Continuous (fun z : M.normalSlice q => h • z) :=
    Continuous.smul (M := ℝ) (X := M.normalSlice q) continuous_const continuous_id
  have hza : Continuous (fun z : M.normalSlice q => q+h • (z : Boson N)) :=
    continuous_const.add (Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_subtype_val)
  have hzb : Continuous (fun z : M.normalSlice q => h⁻¹ • q+(z : Boson N)) :=
    continuous_const.add continuous_subtype_val
  have hw : Continuous (fun z : M.normalSlice q => J (h • z)*φ (q+h • (z : Boson N))) :=
    (hJ.comp hzs).mul (hφ.comp hza)
  have hl : Integrable (fun z : M.normalSlice q => J (h • z)*φ (q+h • (z : Boson N))*
      normalKineticDensity q h f.val z) :=
    (hw.mul (normalKineticDensity_continuous q h f.val)).integrable_of_hasCompactSupport
      ((normalKineticDensity_compactSupport q h f.val).mul_left)
  have hbase : HasCompactSupport (fun z : M.normalSlice q => F (h⁻¹ • q+(z : Boson N))) := by
    have hi : Isometry (fun z : M.normalSlice q => h⁻¹ • q+(z : Boson N)) := by
      intro z w
      simp only [edist_dist,dist_add_left]
      rfl
    exact hFK.comp_isClosedEmbedding hi.isClosedEmbedding
  have hrcs : HasCompactSupport (fun z : M.normalSlice q => J (h • z)*F (h⁻¹ • q+(z : Boson N))) :=
    HasCompactSupport.mul_left (f := fun z : M.normalSlice q => J (h • z)) hbase
  have hrc : Continuous (fun z : M.normalSlice q => J (h • z)*F (h⁻¹ • q+(z : Boson N))) :=
    (hJ.comp hzs).mul (hFc.comp hzb)
  have hr : Integrable (fun z : M.normalSlice q => J (h • z)*F (h⁻¹ • q+(z : Boson N))) :=
    hrc.integrable_of_hasCompactSupport hrcs
  apply integral_mono hl (hr.const_mul _)
  intro z
  have hb := mul_le_mul_of_nonneg_left (M.normalCoreField_kinetic_le q hh f.val z)
    (mul_nonneg (hJn (h • z)) (hφn (q+h • (z : Boson N))))
  have he : h • (h⁻¹ • q+(z : Boson N)) = q+h • (z : Boson N) := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  change J (h • z)*φ (q+h • (z : Boson N))*normalKineticDensity q h f.val z ≤ _ at hb
  dsimp [F]
  rw [he]
  nlinarith only [hb]

theorem normalOrbit_kinetic (hN : 2 ≤ N) (q : Boson N) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧
      (∀ U : M.gaugeStabilizer q, ∀ z, J (M.stabilizerNormalIsometry q U z) = J z) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ (h : ℝ), 0 < h → ∀ (φ : Boson N → ℝ), Continuous φ →
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
        (∀ U : unitary (ColorMatrix N), ∀ x, φ (M.gaugeAction U x) = φ x) →
        Function.support φ ⊆ V → ∀ f : G.invariantCore,
          (∫ z : M.normalSlice q, J (h • z)*φ (q+h • (z : Boson N))*
            normalKineticDensity q h f.val z) ≤
            ∫ x, φ (h • x)*kineticDensity f.val x := by
  obtain ⟨J,V,δ,hJ,hJn,hJ0,hδ,hδJ,hJi,hV,hqV,hVi,hm⟩ := M.normalOrbit_measure hN q
  refine ⟨J,V,hJ,hJn,hJ0,hJi,hV,hqV,hVi,?_⟩
  intro h hh φ hφ hφb hφi hφs f
  exact G.slice_kinetic_integral_le hN q J V hJ hJn hm hh φ hφ (fun x => (hφb x).1) hφi hφs f
end GaugeData
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

lemma MeasuredNormalPatch.kinetic_le (hN : 2 ≤ N) {q : Boson N}
    (P : G.MeasuredNormalPatch q) {h : ℝ} (hh : 0 < h) (f : G.invariantCore) :
    (∫ z : M.normalSlice q, P.density (h • z)*P.cutoff (q+h • (z : Boson N))*
      normalKineticDensity q h f.val z) ≤
      ∫ x, P.cutoff (h • x)*kineticDensity f.val x :=
  G.slice_kinetic_integral_le hN q P.density P.integrationDomain
    P.density_continuous P.density_nonneg P.integration hh P.cutoff
    P.cutoff_continuous (fun x => (P.cutoff_bounds x).1) P.cutoff_invariant P.integration_support f

lemma MeasuredNormalPatch.kinetic_le_total (hN : 2 ≤ N) {q : Boson N}
    (P : G.MeasuredNormalPatch q) {h : ℝ} (hh : 0 < h) (f : G.invariantCore) :
    (∫ z : M.normalSlice q, P.density (h • z)*P.cutoff (q+h • (z : Boson N))*
      normalKineticDensity q h f.val z) ≤
      ∫ x, kineticDensity f.val x := by
  apply (P.kinetic_le G hN hh f).trans
  have hi : Integrable (kineticDensity f.val) :=
    (kineticDensity_continuous f.val).integrable_of_hasCompactSupport (kineticDensity_compactSupport f.val)
  have hw : Continuous (fun x : Boson N => P.cutoff (h • x)) :=
    P.cutoff_continuous.comp (Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_id)
  apply integral_mono ((hw.mul (kineticDensity_continuous f.val)).integrable_of_hasCompactSupport
    (kineticDensity_compactSupport f.val).mul_left) hi
  intro x
  exact mul_le_of_le_one_left (kineticDensity_nonneg f.val x) (P.cutoff_bounds (h • x)).2
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 normalCoreField
local instance kineticMeasuresSliceNormedAddCommGroup (q : Boson N) :
    NormedAddCommGroup (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance kineticMeasuresSliceNormedSpace (q : Boson N) :
    NormedSpace ℝ (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance kineticMeasuresCoordinatesNormedAddCommGroup (q : Boson N) :
    NormedAddCommGroup (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance
local instance kineticMeasuresCoordinatesNormedSpace (q : Boson N) :
    NormedSpace ℝ (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance

lemma normalCoordinateCore_kinetic (q : Boson N) (h : ℝ) (f : SmoothCore N)
    (x : M.NormalCoordinates q) :
    (∑ j, ‖fderiv ℝ (M.normalCoordinateCore q h f : M.NormalCoordinates q → Fermion N) x
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ j)‖^2) =
      normalKineticDensity q h f (M.normalCoordinateIsometry q x) := by
  have hd := (((M.normalCoreField_contDiff q h f).differentiable (by simp))
    (M.normalCoordinateIsometry q x)).hasFDerivAt.comp x
      (M.normalCoordinateIsometry q).hasFDerivAt
  have heq : (M.normalCoordinateCore q h f : M.NormalCoordinates q → Fermion N) =
      M.normalCoreField q h f ∘ M.normalCoordinateIsometry q := by
    funext y
    rw [M.normalCoordinateCore_apply]
    rfl
  rw [heq]
  unfold normalKineticDensity
  rw [hd.fderiv]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousLinearMap.comp_apply,EuclideanSpace.basisFun_apply]
  change ‖fderiv ℝ (M.normalCoreField q h f) (M.normalCoordinateIsometry q x)
    ((stdOrthonormalBasis ℝ (M.normalSlice q)).repr.symm (EuclideanSpace.single j 1))‖^2 = _
  rw [OrthonormalBasis.repr_symm_single]

lemma normalCoordinateCore_weighted_kinetic (q : Boson N) (h : ℝ) (f : SmoothCore N)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ)
    (hJ : ∀ z, 0 ≤ J z) (hφ : ∀ x, 0 ≤ φ x) :
    (∫ x : M.NormalCoordinates q, (M.normalCoordinateWeight q J φ (h • x))^2 *
      ∑ j, ‖fderiv ℝ (M.normalCoordinateCore q h f : M.NormalCoordinates q → Fermion N) x
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ j)‖^2) =
    ∫ z : M.normalSlice q, J (h • z)*φ (q+h • (z : Boson N))*normalKineticDensity q h f z := by
  simp_rw [M.normalCoordinateCore_kinetic]
  have he (x : M.NormalCoordinates q) :
      (M.normalCoordinateWeight q J φ (h • x))^2 =
      J (h • M.normalCoordinateIsometry q x)*φ (q+h • (M.normalCoordinateIsometry q x : Boson N)) := by
    simp only [normalCoordinateWeight,map_smul,Submodule.coe_smul]
    exact Real.sq_sqrt (mul_nonneg (hJ _) (hφ _))
  simp_rw [he]
  exact (M.normalCoordinateIsometry q).measurePreserving.integral_comp
    (M.normalCoordinateIsometry q).toHomeomorph.measurableEmbedding
    (fun z : M.normalSlice q => J (h • z)*φ (q+h • (z : Boson N))*normalKineticDensity q h f z)
end
end BFSSQuantum.AlgebraData

end OAI
