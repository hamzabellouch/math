import Mathlib
import OAI.MathematicalPhysics.BFSS.GaugeCore
import OAI.MathematicalPhysics.BFSS.LocalBounds
import OAI.MathematicalPhysics.BFSS.RellichCompactness

namespace OAI

/-! Normal-coordinate smooth fields and local compactness of core families. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
open scoped NNReal
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] coreToL2 charge bracketPart BFSSKinetic.kineticDerivative

lemma derivative_integral_le_coordinate_sum (f : SmoothCore N) :
    (∫ x, ‖fderiv ℝ (f : Boson N → Fermion N) x‖ ^ 2) ≤
      (Fintype.card (SpaceIndex × ColorIndex N) : ℝ) *
        ∑ p : SpaceIndex × ColorIndex N, ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖ ^ 2 := by
  simp_rw [coreToL2_norm_sq]
  rw [← integral_finsetSum _ (fun p _ => coreNormSq_integrable _), ← integral_const_mul]
  apply integral_mono
    (BFSSRellich.derivative_norm_sq_integrable (f.contDiff.of_le (by simp)) f.hasCompactSupport)
    ((integrable_finsetSum _ (fun p _ => coreNormSq_integrable _)).const_mul _)
  intro x
  simp_rw [coordinateDerivative_apply]
  exact BFSSRellich.opNorm_sq_le_coordinate_sum _

end
end BFSSQuantum.AlgebraData
namespace BFSSSliceAnalytic
noncomputable section
open MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (S : Submodule ℝ E) (a : E) (c : ℝ) (f : E → F)
local instance coreCompactnessAffineNormedAddCommGroup : NormedAddCommGroup (S →L[ℝ] F) := inferInstance
local instance coreCompactnessAffineNormedSpace : NormedSpace ℝ (S →L[ℝ] F) := inferInstance

omit [FiniteDimensional ℝ E] in
lemma affine_contDiff {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun z : S => c • f (a+(z : E))) := by
  exact (hf.comp (contDiff_const.add S.subtypeL.contDiff)).const_smul c

lemma affine_compactSupport (hf : HasCompactSupport f) :
    HasCompactSupport (fun z : S => c • f (a+(z : E))) := by
  have hi : Isometry (fun z : S => a+(z : E)) := by
    intro z w
    simp only [edist_add_left]
    rfl
  exact (hf.comp_isClosedEmbedding hi.isClosedEmbedding).smul_left

omit [FiniteDimensional ℝ E] in
lemma affine_fderiv (hf : Differentiable ℝ f) (z : S) :
    fderiv ℝ (fun z : S => c • f (a+(z : E))) z =
      c • (fderiv ℝ f (a+(z : E))).comp S.subtypeL := by
  have ha : HasFDerivAt (fun z : S => a+(z : E)) S.subtypeL z :=
    S.subtypeL.hasFDerivAt.const_add a
  exact (((hf (a+(z : E))).hasFDerivAt.comp z ha).const_smul c).fderiv

omit [FiniteDimensional ℝ E] in
lemma affine_fderiv_norm_sq (hf : Differentiable ℝ f) (z : S) :
    ‖fderiv ℝ (fun z : S => c • f (a+(z : E))) z‖^2 ≤
      c^2 * ‖fderiv ℝ f (a+(z : E))‖^2 := by
  rw [affine_fderiv S a c f hf,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (fderiv ℝ f _).le_opNorm (v : E)
end
end BFSSSliceAnalytic
namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
local instance coreCompactnessNormalSliceNormedAddCommGroup (q : Boson N) : NormedAddCommGroup (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
local instance coreCompactnessNormalSliceNormedSpace (q : Boson N) : NormedSpace ℝ (M.normalSlice q →L[ℝ] Fermion N) := inferInstance
attribute [local irreducible] coreToL2 charge bracketPart BFSSKinetic.kineticDerivative gaugeAction normalSlice

def normalCoreField (q : Boson N) (h : ℝ) (f : SmoothCore N) : M.normalSlice q → Fermion N :=
  fun z => Real.sqrt ((h ^ M.orbitDimension q)⁻¹) • f (h⁻¹ • q+(z : Boson N))

lemma normalCoreField_contDiff (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (M.normalCoreField q h f) := by
  exact BFSSSliceAnalytic.affine_contDiff (M.normalSlice q) (h⁻¹ • q) _ f f.contDiff

lemma normalCoreField_compactSupport (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.normalCoreField q h f) := by
  exact BFSSSliceAnalytic.affine_compactSupport (M.normalSlice q) (h⁻¹ • q) _ f f.hasCompactSupport

lemma normalCoreField_norm_sq (q : Boson N) {h : ℝ} (hh : 0 < h)
    (f : SmoothCore N) (z : M.normalSlice q) :
    ‖M.normalCoreField q h f z‖^2 =
      (h ^ M.orbitDimension q)⁻¹ * ‖f (h⁻¹ • q+(z : Boson N))‖^2 := by
  rw [normalCoreField,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (inv_nonneg.mpr (pow_nonneg hh.le _))]

lemma normalCoreField_fderiv (q : Boson N) (h : ℝ) (f : SmoothCore N)
    (z : M.normalSlice q) :
    fderiv ℝ (M.normalCoreField q h f) z =
      Real.sqrt ((h ^ M.orbitDimension q)⁻¹) •
      (fderiv ℝ (f : Boson N → Fermion N) (h⁻¹ • q+(z : Boson N))).comp
        (M.normalSlice q).subtypeL := by
  exact BFSSSliceAnalytic.affine_fderiv (M.normalSlice q) (h⁻¹ • q) _ f
    (f.contDiff.differentiable (by simp)) z

lemma normalCoreField_fderiv_norm_sq (q : Boson N) {h : ℝ} (hh : 0 < h)
    (f : SmoothCore N) (z : M.normalSlice q) :
    ‖fderiv ℝ (M.normalCoreField q h f) z‖^2 ≤
      (h ^ M.orbitDimension q)⁻¹ *
        ‖fderiv ℝ (f : Boson N → Fermion N) (h⁻¹ • q+(z : Boson N))‖^2 := by
  have hb := BFSSSliceAnalytic.affine_fderiv_norm_sq (M.normalSlice q) (h⁻¹ • q)
    (Real.sqrt ((h ^ M.orbitDimension q)⁻¹)) f (f.contDiff.differentiable (by simp)) z
  rw [Real.sq_sqrt (inv_nonneg.mpr (pow_nonneg hh.le _))] at hb
  exact hb

lemma normalCoreField_derivative_integrable (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    Integrable (fun z : M.normalSlice q => ‖fderiv ℝ (M.normalCoreField q h f) z‖^2) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((M.normalCoreField_contDiff q h f).continuous_fderiv (by simp)).norm.pow 2
  · exact ((M.normalCoreField_compactSupport q h f).fderiv ℝ).comp_left
      (g := fun L : M.normalSlice q →L[ℝ] Fermion N => ‖L‖^2) (by simp)

namespace GaugeData
variable {M} (G : M.GaugeData)

theorem normalCoreField_local_bounds (hN : 2 ≤ N) (q : Boson N) :
    ∃ η B K : ℝ, 0 < η ∧ 0 < B ∧ 0 ≤ K ∧
    ∀ h R : ℝ, 0 < h → h ≤ 1 → 0 ≤ R → h*R < η →
    ∀ f : G.invariantCore,
      (∫ z : M.normalSlice q in Metric.closedBall 0 R, ‖M.normalCoreField q h f.val z‖^2) ≤
        B * ‖coreToL2 f.val‖^2 ∧
      (∫ z : M.normalSlice q in Metric.closedBall 0 R,
        ‖fderiv ℝ (M.normalCoreField q h f.val) z‖^2) ≤
        B * (M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2) := by
  obtain ⟨η,B,hη,hB,hbound⟩ := M.normalOrbit_local_integral_bound hN q
  obtain ⟨c,K,hc,hK,hgraph⟩ := M.massive_core_uniform_distance hN
  let d : ℝ := Fintype.card (SpaceIndex × ColorIndex N)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨η,max B (2*d*B),K,hη,lt_of_lt_of_le hB (le_max_left _ _),hK,?_⟩
  intro h R hh hh1 hR hhR f
  have hnorm := hbound h R hh hR hhR (fun x => ‖f.val x‖^2)
    (f.val.continuous.norm.pow 2)
    (f.val.hasCompactSupport.comp_left (g := fun v : Fermion N => ‖v‖^2) (by simp))
    (fun _ => sq_nonneg _) (by intro U x; rw [G.invariantCore_norm_unitary hN])
  have hdf : Continuous (fderiv ℝ (f.val : Boson N → Fermion N)) :=
    f.val.contDiff.continuous_fderiv (by simp)
  have hdfK : HasCompactSupport (fderiv ℝ (f.val : Boson N → Fermion N)) :=
    f.val.hasCompactSupport.fderiv ℝ
  have hgrad := hbound h R hh hR hhR (fun x => ‖fderiv ℝ (f.val : Boson N → Fermion N) x‖^2)
    (hdf.norm.pow 2) (hdfK.comp_left (g := fun L : Boson N →L[ℝ] Fermion N => ‖L‖^2) (by simp))
    (fun _ => sq_nonneg _) (by intro U x; rw [G.invariantCore_fderiv_norm_unitary hN])
  constructor
  · simp_rw [M.normalCoreField_norm_sq q hh]
    rw [integral_const_mul]
    rw [←coreToL2_norm_sq] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · have hfdi := M.normalCoreField_derivative_integrable q h f.val
    have hai : Isometry (fun z : M.normalSlice q => h⁻¹ • q+(z : Boson N)) := by
      intro z w
      simp only [edist_add_left]
      rfl
    have hgi : Integrable (fun z : M.normalSlice q =>
        (h ^ M.orbitDimension q)⁻¹ *
          ‖fderiv ℝ (f.val : Boson N → Fermion N) (h⁻¹ • q+(z : Boson N))‖^2) := by
      apply Integrable.const_mul
      apply Continuous.integrable_of_hasCompactSupport
      · exact (hdf.comp (continuous_const.add continuous_subtype_val)).norm.pow 2
      · exact ((hdfK.comp_isClosedEmbedding hai.isClosedEmbedding).comp_left
          (g := fun L : Boson N →L[ℝ] Fermion N => ‖L‖^2) (by simp))
    have hl : (∫ z : M.normalSlice q in Metric.closedBall 0 R,
        ‖fderiv ℝ (M.normalCoreField q h f.val) z‖^2) ≤
        ∫ z : M.normalSlice q in Metric.closedBall 0 R,
          (h ^ M.orbitDimension q)⁻¹ *
            ‖fderiv ℝ (f.val : Boson N → Fermion N) (h⁻¹ • q+(z : Boson N))‖^2 :=
      setIntegral_mono_on hfdi.integrableOn hgi.integrableOn
      Metric.isClosed_closedBall.measurableSet (fun z _ => M.normalCoreField_fderiv_norm_sq q hh f.val z)
    rw [integral_const_mul] at hl
    have hgl := derivative_integral_le_coordinate_sum f.val
    have hen := hgraph h hh hh1 f.val
    have hmom : 0 ≤ ∫ x : Boson N, (M.massiveDistance h x)^2*‖f.val x‖^2 :=
      integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsum : (∑ p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f.val)‖^2) ≤
        2*(M.deformedCoreEnergy h 1 f.val+K*‖coreToL2 f.val‖^2) := by
      nlinarith [mul_nonneg (half_pos hc).le hmom]
    have hepos : 0 ≤ M.deformedCoreEnergy h 1 f.val+K*‖coreToL2 f.val‖^2 :=
      by
      have hp : 0 ≤ ∑ p : SpaceIndex × ColorIndex N,
          ‖coreToL2 (coordinateDerivative p.1 p.2 f.val)‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
    calc
      _ ≤ B * (∫ x, ‖fderiv ℝ (f.val : Boson N → Fermion N) x‖^2) := hl.trans hgrad
      _ ≤ B * (d * ∑ p : SpaceIndex × ColorIndex N,
          ‖coreToL2 (coordinateDerivative p.1 p.2 f.val)‖^2) :=
        mul_le_mul_of_nonneg_left hgl hB.le
      _ ≤ B * (d * (2*(M.deformedCoreEnergy h 1 f.val+K*‖coreToL2 f.val‖^2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hd) hB.le
      _ = (2*d*B)*(M.deformedCoreEnergy h 1 f.val+K*‖coreToL2 f.val‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hepos
end GaugeData
end
end BFSSQuantum.AlgebraData
namespace BFSSSliceAnalytic
noncomputable section
open MeasureTheory Set
variable {E E' F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance coreCompactnessIsometryDomainNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance coreCompactnessIsometryDomainNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance coreCompactnessIsometryCodomainNormedAddCommGroup : NormedAddCommGroup (E' →L[ℝ] F) := inferInstance
local instance coreCompactnessIsometryCodomainNormedSpace : NormedSpace ℝ (E' →L[ℝ] F) := inferInstance

lemma isometry_fderiv_norm_le (e : E ≃ₗᵢ[ℝ] E') {f : E' → F}
    (hf : Differentiable ℝ f) (x : E) :
    ‖fderiv ℝ (f ∘ e) x‖ ≤ ‖fderiv ℝ f (e x)‖ := by
  have hd := ((hf (e x)).hasFDerivAt.comp x e.hasFDerivAt).fderiv
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖(fderiv ℝ f (e x)) (e v)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using (fderiv ℝ f (e x)).le_opNorm (e v)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E'] [BorelSpace E'] [FiniteDimensional ℝ E']

lemma isometry_closedBall_integral (e : E ≃ₗᵢ[ℝ] E') (R : ℝ) (g : E' → F) :
    (∫ x in Metric.closedBall 0 R, g (e x)) =
      ∫ x in Metric.closedBall 0 R, g x := by
  have he : e ⁻¹' Metric.closedBall (0 : E') R = Metric.closedBall 0 R := by
    ext x
    simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right,e.norm_map]
  have hm := e.measurePreserving.restrict_preimage (s := Metric.closedBall (0 : E') R) Metric.isClosed_closedBall.measurableSet
  have hi := hm.integral_comp e.toHomeomorph.measurableEmbedding g
  rw [he] at hi
  exact hi
lemma isometry_derivative_integral_le (e : E ≃ₗᵢ[ℝ] E') (R : ℝ) {f : E' → F}
    (hf : ContDiff ℝ 1 f) :
    (∫ x in Metric.closedBall 0 R, ‖fderiv ℝ (f ∘ e) x‖^2) ≤
      ∫ x in Metric.closedBall 0 R, ‖fderiv ℝ f x‖^2 := by
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hg : Continuous (fderiv ℝ (f ∘ e)) :=
    (hf.comp e.contDiff).continuous_fderiv (by simp)
  calc
    _ ≤ ∫ x in Metric.closedBall 0 R, ‖fderiv ℝ f (e x)‖^2 := by
      apply setIntegral_mono_on (μ := volume)
        (f := fun x => ‖fderiv ℝ (f ∘ e) x‖^2)
        (g := fun x => ‖fderiv ℝ f (e x)‖^2)
        ((hg.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R))
        (((hdf.comp e.continuous).norm.pow 2).continuousOn.integrableOn_compact
          (isCompact_closedBall 0 R)) Metric.isClosed_closedBall.measurableSet
      intro x _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (isometry_fderiv_norm_le e (hf.differentiable (by simp)) x) 2
    _ = _ := isometry_closedBall_integral e R (fun x => ‖fderiv ℝ f x‖^2)

end
end BFSSSliceAnalytic

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2

abbrev NormalCoordinates (q : Boson N) :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ (M.normalSlice q)))

def normalCoordinateIsometry (q : Boson N) : M.NormalCoordinates q ≃ₗᵢ[ℝ] M.normalSlice q :=
  (stdOrthonormalBasis ℝ (M.normalSlice q)).repr.symm

def normalCoordinateField (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    M.NormalCoordinates q → Fermion N :=
  M.normalCoreField q h f ∘ M.normalCoordinateIsometry q

lemma normalCoordinateField_contDiff (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (M.normalCoordinateField q h f) :=
  (M.normalCoreField_contDiff q h f).comp (M.normalCoordinateIsometry q).contDiff

lemma normalCoordinateField_integral (q : Boson N) (h R : ℝ) (f : SmoothCore N) :
    (∫ x : M.NormalCoordinates q in Metric.closedBall 0 R,
      ‖M.normalCoordinateField q h f x‖^2) =
      ∫ z : M.normalSlice q in Metric.closedBall 0 R, ‖M.normalCoreField q h f z‖^2 :=
  BFSSSliceAnalytic.isometry_closedBall_integral (M.normalCoordinateIsometry q) R
    (fun z => ‖M.normalCoreField q h f z‖^2)

lemma normalCoordinateField_derivative_integral (q : Boson N) (h R : ℝ) (f : SmoothCore N) :
    (∫ x : M.NormalCoordinates q in Metric.closedBall 0 R,
      ‖fderiv ℝ (M.normalCoordinateField q h f) x‖^2) ≤
      ∫ z : M.normalSlice q in Metric.closedBall 0 R,
        ‖fderiv ℝ (M.normalCoreField q h f) z‖^2 := by
  exact BFSSSliceAnalytic.isometry_derivative_integral_le (M.normalCoordinateIsometry q) R
    ((M.normalCoreField_contDiff q h f).of_le (by simp))

end
end BFSSQuantum.AlgebraData
namespace BFSSRellich
noncomputable section
open MeasureTheory Set
open scoped NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]
local instance coreCompactnessRellichNormedAddCommGroup : NormedAddCommGroup (Euclidean (ι := ι) →L[ℝ] H) := inferInstance
local instance coreCompactnessRellichNormedSpace : NormedSpace ℝ (Euclidean (ι := ι) →L[ℝ] H) := inferInstance

omit [DecidableEq ι] [CompleteSpace H] in
theorem localRellich_on {J : Type*}
    {K : Set (Euclidean (ι := ι))} [CompactSpace K]
    (φ : ContDiffBump (0 : Euclidean (ι := ι)))
    (hK : K ⊆ Metric.closedBall 0 φ.rIn)
    (f : J → Euclidean (ι := ι) → H) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (A B : ℝ≥0)
    (hA : ∀ j, (∫ x in Metric.closedBall 0 φ.rOut, ‖fderiv ℝ (f j) x‖^2) ≤ (A : ℝ)^2)
    (hB : ∀ j, (∫ x in Metric.closedBall 0 φ.rOut, ‖f j x‖^2) ≤ (B : ℝ)^2) :
    TotallyBounded (range (fun j => localLp (K := K) (f j) (hf j).continuous)) := by
  let S : Set (Euclidean (ι := ι)) := Metric.closedBall 0 φ.rOut
  have hSc : IsCompact S := isCompact_closedBall _ _
  let g : J → Euclidean (ι := ι) → H := fun j x => φ x • f j x
  have hg (j : J) : ContDiff ℝ 1 (g j) := φ.contDiff.smul (hf j)
  have hgK (j : J) : HasCompactSupport (g j) := φ.hasCompactSupport.smul_right
  have hgs (j : J) : tsupport (g j) ⊆ S := by
    calc
      _ ⊆ tsupport (φ : Euclidean (ι := ι) → ℝ) := tsupport_smul_subset_left _ _
      _ = S := φ.tsupport_eq
  obtain ⟨C₀,hC₀⟩ := ((φ.hasCompactSupport.fderiv ℝ).isCompact_range
    ((φ.contDiff : ContDiff ℝ 1 (φ : Euclidean (ι := ι) → ℝ)).continuous_fderiv (by norm_num))).isBounded.exists_norm_le
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hder : ∀ x, ‖fderiv ℝ (φ : Euclidean (ι := ι) → ℝ) x‖ ≤ C :=
    fun x => (hC₀ _ (mem_range_self x)).trans (le_max_left _ _)
  have hgnorm (j : J) (x : Euclidean (ι := ι)) : ‖g j x‖ ≤ ‖f j x‖ := by
    change ‖φ x • f j x‖ ≤ ‖f j x‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg (x := x))]
    exact mul_le_of_le_one_left (norm_nonneg _) (φ.le_one (x := x))
  have hgder (j : J) (x : Euclidean (ι := ι)) :
      ‖fderiv ℝ (g j) x‖^2 ≤ 2*‖fderiv ℝ (f j) x‖^2+2*C^2*‖f j x‖^2 := by
    have hdiff : ∀ y, DifferentiableAt ℝ (φ : Euclidean (ι := ι) → ℝ) y :=
      (φ.contDiff : ContDiff ℝ 1 (φ : Euclidean (ι := ι) → ℝ)).differentiable (by norm_num)
    have hf' : DifferentiableAt ℝ (f j) x := (hf j).differentiable (by simp) x
    have hb : ‖fderiv ℝ (g j) x‖ ≤ ‖fderiv ℝ (f j) x‖+C*‖f j x‖ := by
      change ‖fderiv ℝ (fun y => φ y • f j y) x‖ ≤ _
      rw [fderiv_fun_smul (hdiff x) hf']
      calc
        _ ≤ ‖(φ x) • fderiv ℝ (f j) x‖+
            ‖(fderiv ℝ (φ : Euclidean (ι := ι) → ℝ) x).smulRight (f j x)‖ := norm_add_le _ _
        _ = φ x * ‖fderiv ℝ (f j) x‖+
            ‖fderiv ℝ (φ : Euclidean (ι := ι) → ℝ) x‖*‖f j x‖ := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg (x := x)),
            ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ _ := add_le_add
          (mul_le_of_le_one_left (norm_nonneg _) (φ.le_one (x := x)))
          (mul_le_mul_of_nonneg_right (hder x) (norm_nonneg _))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [sq_nonneg (‖fderiv ℝ (f j) x‖-C*‖f j x‖)]
  have hgi (j : J) : Integrable (fun x => ‖g j x‖^2) :=
    continuous_norm_sq_integrable (hg j).continuous (hgK j)
  have hgdi (j : J) : Integrable (fun x => ‖fderiv ℝ (g j) x‖^2) :=
    derivative_norm_sq_integrable (hg j) (hgK j)
  have hfn (j : J) : IntegrableOn (fun x => ‖f j x‖^2) S :=
    ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact hSc
  have hfd (j : J) : IntegrableOn (fun x => ‖fderiv ℝ (f j) x‖^2) S :=
    (((hf j).continuous_fderiv (by simp)).norm.pow 2).continuousOn.integrableOn_compact hSc
  have hgn (j : J) : (∫ x, ‖g j x‖^2) ≤ (B : ℝ)^2 := by
    calc
      _ = ∫ x in S, ‖g j x‖^2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hz : g j x = 0 := by
          by_contra hn
          exact hx (hgs j (subset_tsupport _ hn))
        simp [hz]
      _ ≤ ∫ x in S, ‖f j x‖^2 :=
        setIntegral_mono_on (hgi j).integrableOn (hfn j) hSc.measurableSet
          (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hgnorm j x) 2)
      _ ≤ _ := hB j
  have hgd (j : J) : (∫ x, ‖fderiv ℝ (g j) x‖^2) ≤
      2*(A : ℝ)^2+2*C^2*(B : ℝ)^2 := by
    calc
      _ = ∫ x in S, ‖fderiv ℝ (g j) x‖^2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hz : fderiv ℝ (g j) x = 0 := by
          by_contra hn
          exact hx (hgs j (support_fderiv_subset ℝ hn))
        simp [hz]
      _ ≤ ∫ x in S, 2*‖fderiv ℝ (f j) x‖^2+2*C^2*‖f j x‖^2 :=
        setIntegral_mono_on (hgdi j).integrableOn
          (by
            exact ContinuousOn.integrableOn_compact hSc
              (((((hf j).continuous_fderiv (by simp)).norm.pow 2).const_mul 2).add
                (((hf j).continuous.norm.pow 2).const_mul (2*C^2))).continuousOn) hSc.measurableSet
          (fun x _ => hgder j x)
      _ = 2*(∫ x in S, ‖fderiv ℝ (f j) x‖^2)+2*C^2*(∫ x in S, ‖f j x‖^2) := by
        rw [integral_add ((hfd j).const_mul 2) ((hfn j).const_mul (2*C^2))]
        simp only [integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hA j) (by norm_num))
        (mul_le_mul_of_nonneg_left (hB j) (by positivity))
  let A' : ℝ≥0 := ⟨Real.sqrt (2*(A : ℝ)^2+2*C^2*(B : ℝ)^2), Real.sqrt_nonneg _⟩
  let B' : ℝ≥0 := ⟨volume.real S+(B : ℝ)^2, by positivity⟩
  have ht := localRellich (K := K) g hg hgK A' B' (by
    intro j
    change _ ≤ (Real.sqrt _)^2
    rw [Real.sq_sqrt (by positivity)]
    exact hgd j) (by
    intro j
    exact (integral_norm_le_volume_add_square (hg j).continuous (hgK j) hSc
      ((subset_tsupport _).trans (hgs j))).trans
      (add_le_add_right (hgn j) _))
  have he (j : J) : localLp (K := K) (f j) (hf j).continuous = localLp (g j) (hg j).continuous := by
    unfold localLp
    congr 1
    apply ContinuousMap.ext
    intro x
    change f j x = φ x • f j x
    rw [φ.one_of_mem_closedBall (hK x.property),one_smul]
  simpa only [←he] using ht
end
end BFSSRellich
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
local instance coreCompactnessNormalCoordinateNormedAddCommGroup (q : Boson N) : NormedAddCommGroup (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance
local instance coreCompactnessNormalCoordinateNormedSpace (q : Boson N) : NormedSpace ℝ (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance

theorem normalCore_locallyCompact (hN : 2 ≤ N) (q : Boson N) :
    ∃ η : ℝ, 0 < η ∧ ∀ {J : Type*}
      (φ : ContDiffBump (0 : M.NormalCoordinates q)) (E : ℝ≥0)
      (h : J → ℝ) (f : J → G.invariantCore),
      (∀ j, 0 < h j ∧ h j ≤ 1 ∧ h j * φ.rOut < η) →
      (∀ j, ‖coreToL2 (f j).val‖^2 ≤ E) →
      (∀ j, M.deformedCoreEnergy (h j) 1 (f j).val ≤ E) →
      TotallyBounded (range (fun j => BFSSRellich.localLp
        (K := Metric.closedBall (0 : M.NormalCoordinates q) φ.rIn)
        (M.normalCoordinateField q (h j) (f j).val)
        (M.normalCoordinateField_contDiff q (h j) (f j).val).continuous)) := by
  obtain ⟨η,B,K,hη,hB,hK,hbound⟩ := G.normalCoreField_local_bounds hN q
  refine ⟨η,hη,?_⟩
  intro J φ E h f hh hnorm henergy
  let A : ℝ≥0 := ⟨Real.sqrt (B*((E : ℝ)+K*E)), Real.sqrt_nonneg _⟩
  let B' : ℝ≥0 := ⟨Real.sqrt (B*E), Real.sqrt_nonneg _⟩
  have hE : 0 ≤ (E : ℝ) := E.property
  have hR : 0 ≤ φ.rOut := φ.rOut_pos.le
  have hb (j : J) := hbound (h j) φ.rOut (hh j).1 (hh j).2.1 hR (hh j).2.2 (f j)
  apply BFSSRellich.localRellich_on φ (Subset.refl _) 
    (fun j => M.normalCoordinateField q (h j) (f j).val)
    (fun j => (M.normalCoordinateField_contDiff q (h j) (f j).val).of_le (by simp)) A B'
  · intro j
    change _ ≤ (Real.sqrt _)^2
    rw [Real.sq_sqrt (mul_nonneg hB.le (add_nonneg hE (mul_nonneg hK hE)))]
    exact ((M.normalCoordinateField_derivative_integral q (h j) φ.rOut (f j).val).trans
      (hb j).2).trans (mul_le_mul_of_nonneg_left
        (add_le_add (henergy j) (mul_le_mul_of_nonneg_left (hnorm j) hK)) hB.le)
  · intro j
    rw [M.normalCoordinateField_integral]
    change _ ≤ (Real.sqrt _)^2
    rw [Real.sq_sqrt (mul_nonneg hB.le hE)]
    exact (hb j).1.trans (mul_le_mul_of_nonneg_left (hnorm j) hB.le)
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
